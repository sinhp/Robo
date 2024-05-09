import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- World "Matrix"
-- Level 1

/- # Introduction

An `n`-dimensional vector is nothing but a function out of `Fin n`. For instance
a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
`x i : ℝ`.
We represent such a vector as `![x_1, ..., x_n]`.

Since vectors are functions, we define their addition and scalar multiplication pointwise.

Under the hood, `![a, b, c]` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.
where `Matrix.vecCons : α → (Fin n → α) → Fin (Nat.succ n) → α`

Counter-intuitively, the empty vector is quite important in Lean since ultimately every
vector is built up from it.

-/


#check Matrix.vecCons

open Real Function Set Finset BigOperators

example (a b c : ℝ) : ![a,b,c] 0 = a := by
  rfl

example (a b c : ℝ) : ![a,b,c] 1 = b := by
  rfl

example : ![(sqrt 3)/2, 1/2] + ![-(sqrt 3)/2, 1/2] = ![0, 1] := by
  --simp
  --ring
  funext i
  fin_cases i <;>
  simp <;>
  ring

#check Matrix.empty_eq

#check Matrix.zero_empty

theorem one_empty {α : Type*} [One α] : (1 : Fin 0 → ℝ) = ![] :=
  Matrix.empty_eq _

#check smul_eq_mul

example (x : ℝ) : ![x] = fun _ ↦ x := by
  simp only [Matrix.cons_fin_one]

example (x y : ℝ) : ![x] + ![y] = ![x + y] := by
  --simp
  simp only [Matrix.cons_fin_one]
  rfl

example : α ≃ (Fin 1 → α) := by
  refine' {..}
  · intro a
    exact fun _ => a
  · intro f
    exact f 0
  · intro a
    dsimp
  · intro f
    simp
    ext i
    fin_cases i
    simp


#check Matrix.smul_cons

example : sqrt 2 • ![(sqrt 2)/2, 0] + sqrt 2 • ![0, (sqrt 2)/2] = ![1, 1] := by
  -- simp only [Matrix.smul_cons]
  -- simp only [smul_eq_mul]
  -- simp only [mul_zero]
  -- simp only [Matrix.smul_empty]
  -- ring
  -- norm_num
  simp
  ring
  --norm_num
  simp

example {a : ℝ} (h : a + a = 0) : a = 0 := by
  --simp only [add_self_eq_zero] at h
  simpa using h


example {a b : ℝ} (h : 2 • ![a, -b] + - ![a + b, a - b] = ![0, 0]) :
    a = 0 ∧ b = 0 := by
  simp at h
  conv at h =>
    lhs
    ring
  --constructor
  -- ...
  apply congr_fun at h
  have h₁ : a - b = 0 := h 0
  have h₂ : -a - b = 0 := h 1
  rw [eq_of_sub_eq_zero h₁] at *
  have : - b = 0 := by
    apply add_self_eq_zero.mp at h₂
    exact h₂
  simp only [and_self]
  apply neg_eq_zero.mp this

example : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v : Fin 2 → ℝ | 3 * v 0 - v 1 = 0  }  -- { (![x, y] : Fin 2 → ℝ) | 3 * x - y = 0 } -- -- --
  add_mem' := by
    intro a b ha hb
    rw [mem_setOf] at *
    simp
    rw [mul_add]
    linear_combination ha + hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    dsimp at *
    rw [← sub_eq_zero.mp hx]
    linarith


#check Submodule.smul_mem
#check inv_smul_smul
#check Submodule.smul_mem_iff



example (M : Type*) [AddCommMonoid M] [Module ℝ M] (S : Submodule ℝ M) (x : M) (r : ℝ) (hr : r ≠ 0) :
    r • x ∈ S ↔ x ∈ S := by
  --apply Submodule.smul_mem_iff
  --assumption
  constructor
  · intro hrxS
    rw [← inv_smul_smul (Units.mk0 r hr) x]
    apply Submodule.smul_mem
    simpa using hrxS
  · intro hxS
    --simpa using (Submodule.smul_mem S r hxS)
    apply Submodule.smul_mem
    assumption


example (R M : Type*) [DivisionSemiring R] [AddCommMonoid M] [Module R M] (S : Submodule R M) (x : M) (r : R) (hr : r ≠ 0) :
    r • x ∈ S ↔ x ∈ S := by
  constructor
  · intro hrxS
    rw [← inv_smul_smul (Units.mk0 r hr) x]
    apply Submodule.smul_mem
    simpa using hrxS
  · intro hxS
    apply Submodule.smul_mem
    assumption

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff s0



/-
Given a (finite or infinite) family of vector subspaces of a vector space V,
we can define the greatest common subspace of this family as the intersection
of all the subspaces in the family. In this level you will prove that the set
intersection of a family of subspaces is a subspace.
-/

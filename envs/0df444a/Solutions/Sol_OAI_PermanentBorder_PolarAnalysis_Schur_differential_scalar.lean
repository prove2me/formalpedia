-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:46:45.499058+00:00
-- url     : https://prove2.me/submissions/ba9931c6-cb1a-4fe6-a0fc-3686ad46b753

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SchurDifferentials.lean:L65-L117
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_Schur_solved_left

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem solved_right (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    block a β γ E *ᵥ normalized (right γ E) =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, fromBlocks_mulVec, right, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : E *ᵥ -(E⁻¹ *ᵥ γ) = -γ := by
    rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv E hu, one_mulVec]
  rw [hh]
  ext j
  cases j <;> simp [scalar, mulVec, dotProduct, Finset.mul_sum, sub_eq_add_neg]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_det {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (fun y => (E y).det) x := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem differentiableAt_adjugate {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply differentiableAt_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem differentiableAt_inverse {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((differentiableAt_det hE).inv hx).mul (differentiableAt_adjugate hE i j)
end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- from OAI.Algebra.Determinantal.SchurDifferentials ----
namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_right {γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => right (γ y) (E y) i) x := by
  simp only [right, Pi.neg_apply, mulVec, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (differentiableAt_inverse hE hx i j).mul (hγ j))).neg

omit [Fintype ι] [DecidableEq ι] in
 theorem differential_mulVec {κ : Type*} [Fintype κ]
    {A : V → Matrix ι κ ℂ} {p : V → κ → ℂ} {x : V}
    (hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x)
    (hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x) (h : V) (i : ι) :
    fderiv ℂ (fun y => (A y *ᵥ p y) i) x h =
      ((Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h) *ᵥ p x) i +
      (A x *ᵥ (fun j => fderiv ℂ (fun y => p y j) x h)) i := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hA i j).hasFDerivAt.mul (hp j).hasFDerivAt)
  have heq : fderiv ℂ (fun y => (A y *ᵥ p y) i) x =
      ∑ j, ((A x i j) • fderiv ℂ (fun y => p y j) x +
        (p x j) • fderiv ℂ (fun y => A y i j) x) := by
    convert! hd.fderiv using 1
  rw [heq]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Finset.sum_add_distrib, Matrix.of_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

 theorem differential_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (h : V) :
    fderiv ℂ (fun y => scalar (a y) (β y) (γ y) (E y)) x h =
      normalized (left (β x) (E x)) ⬝ᵥ
        ((Matrix.of fun i j => fderiv ℂ (fun y => block (a y) (β y) (γ y) (E y) i j) x h)
          *ᵥ normalized (right (γ x) (E x))) := by
  let A := fun y => block (a y) (β y) (γ y) (E y)
  let p := fun y => normalized (right (γ y) (E y))
  let b := normalized (left (β x) (E x))
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  have hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x := by
    intro i j
    cases i <;> cases j <;> simp only [A, block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
    · exact ha
    · exact hβ _
    · exact hγ _
    · exact hE _ _
  have hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x := by
    intro i
    cases i with
    | inl u => exact differentiableAt_const _
    | inr i => exact differentiableAt_right hγ hE hx i
  have hevent : ∀ᶠ y in 𝓝 x, (E y).det ≠ 0 :=
    (differentiableAt_det hE).continuousAt.eventually_ne hx
  have heq (i : Unit ⊕ ι) :
      (fun y => (A y *ᵥ p y) i) =ᶠ[𝓝 x] (fun y => Sum.elim (fun _ => S y) (fun _ => 0) i) := by
    filter_upwards [hevent] with y hy
    exact congr_fun (solved_right (a y) (β y) (γ y) (E y) hy) i
  let dA : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
    Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h
  let dp : Unit ⊕ ι → ℂ := fun j => fderiv ℂ (fun y => p y j) x h
  have hd : dA *ᵥ p x + A x *ᵥ dp =
      Sum.elim (fun _ => fderiv ℂ S x h) (fun _ => 0) := by
    ext i
    change (dA *ᵥ p x) i + (A x *ᵥ dp) i = _
    rw [← differential_mulVec hA hp h i]
    rw [(heq i).fderiv_eq]
    cases i <;> simp
  have hb : b ᵥ* A x = Sum.elim (fun _ => S x) (fun _ => 0) :=
    solved_left (a x) (β x) (γ x) (E x) hx
  have hz : b ⬝ᵥ (A x *ᵥ dp) = 0 := by
    rw [dotProduct_mulVec, hb]
    simp [dotProduct, dp, p, normalized, Fintype.sum_sum_type]
  have hd' := congrArg (fun z => b ⬝ᵥ z) hd
  rw [dotProduct_add, hz, add_zero] at hd'
  change fderiv ℂ S x h = b ⬝ᵥ (dA *ᵥ p x)
  simpa [dotProduct, b, normalized, Fintype.sum_sum_type] using hd'.symm
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

end PermanentBorder.PolarAnalysis

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar := @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.differential_scalar

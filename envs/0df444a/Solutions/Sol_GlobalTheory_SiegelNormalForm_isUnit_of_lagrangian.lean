-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:09.49435+00:00
-- url     : https://prove2.me/submissions/37570982-ce12-4910-a40b-bf93527d6808

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.SiegelNormalForm
namespace _root_.GlobalTheory.SiegelNormalForm
theorem _root_.solution (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (f : Fin g → Fin g → ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ (star z)).re)
    (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Pᵀ * Hm * P.map star = Y.map (↑))
    (hf : ∀ i j, ((P *ᵥ Pi.single i 1) ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0) :
    IsUnit P := by
  by_contra hP
  have hdet : P.det = 0 := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hP
    exact not_not.mp hP
  have hYdet : Y.det = 0 := by
    have h1 : (Y.map ((↑) : ℝ → ℂ)).det = 0 := by
      rw [← hY, det_mul, det_mul, det_transpose, hdet]
      simp
    have h2 : ((Y.det : ℝ) : ℂ) = (Y.map ((↑) : ℝ → ℂ)).det :=
      RingHom.map_det Complex.ofRealHom Y
    exact_mod_cast h2.trans h1
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hYdet
  set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc
  have hYx : (Y.map ((↑) : ℝ → ℂ)) *ᵥ xc = 0 := by
    ext i
    have := congrFun hx i
    simp only [mulVec, dotProduct, Pi.zero_apply, map_apply, hxc] at this ⊢
    exact_mod_cast this
  have hstar : star xc = xc := by
    ext i
    simp [hxc]
  have hPx : P *ᵥ xc = 0 := by
    by_contra hne
    have := hpos _ hne
    rw [_root_.GlobalTheory.SiegelNormalForm.form_pull, hY, hstar, hYx] at this
    simp at this
  have hsum : ∀ u : Fin g → ℂ,
      (P *ᵥ xc) ⬝ᵥ u = ∑ i, xc i * ((P *ᵥ Pi.single i 1) ⬝ᵥ u) := by
    intro u
    simp only [mulVec_single_one]
    simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.col_apply]
    ring
  apply hx0
  ext j
  have h := congrArg Complex.im (hsum (Hm *ᵥ star (f j)))
  rw [hPx, zero_dotProduct, Complex.zero_im, Complex.im_sum] at h
  simp only [hxc, Complex.im_ofReal_mul, hf, mul_ite, mul_neg, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa using h.symm
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm

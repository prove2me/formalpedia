-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_linear_of_mul_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:20.224064+00:00
-- url     : https://prove2.me/submissions/51d62d57-1d43-49a4-bc65-19135ba94a37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Theorems.Thm_GlobalTheory_ArtinKernel_differentiable_fderiv
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
namespace GlobalTheory.ArtinKernel
theorem _root_.solution {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (h0 : ∀ z, F z ≠ 0) {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = b l * F z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = cexp (lam l) := by
  have hb0 : ∀ l : S, b l ≠ 0 := by
    intro l hl
    have := hb l 0
    rw [hl, zero_mul, zero_add] at this
    exact h0 _ this
  have hdF : ∀ (l : S) z, fderiv ℂ F (z + l) = b l • fderiv ℂ F z := by
    intro l z
    have h1 : (fun w => F (w + l)) = fun w => b l * F w := funext fun w => hb l w
    rw [← fderiv_comp_add_right (f := F) (l : Fin g → ℂ), h1, fderiv_const_mul (hF z)]
  set H : (Fin g → ℂ) → ((Fin g → ℂ) →L[ℂ] ℂ) := fun z => (F z)⁻¹ • fderiv ℂ F z with hH
  have hHd : Differentiable ℂ H := (hF.inv h0).smul (differentiable_fderiv hF)
  have hper : ∀ z, ∀ l ∈ S, H (z + l) = H z := by
    intro z l hl
    simp only [hH]
    rw [hb ⟨l, hl⟩ z, hdF ⟨l, hl⟩ z, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (hb0 _), mul_one]
  have hconst : ∀ z, H z = H 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hHd hS hper z 0
  set L := H 0 with hL
  have hDF : ∀ w, fderiv ℂ F w = F w • L := by
    intro w
    rw [← hconst w, hH, smul_smul, mul_inv_cancel₀ (h0 w), one_smul]
  have hK : ∀ w, fderiv ℂ (fun z => F z * cexp (-L z)) w = 0 := by
    intro w
    have h2 : HasFDerivAt (fun z => F z * cexp (-L z))
        (F w • (cexp (-L w) • -L) + cexp (-L w) • fderiv ℂ F w) w :=
      (hF w).hasFDerivAt.mul L.hasFDerivAt.neg.cexp
    rw [h2.fderiv, hDF w]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hKd : Differentiable ℂ (fun z => F z * cexp (-L z)) :=
    hF.mul (L.differentiable.neg.cexp)
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have e1 := is_const_of_fderiv_eq_zero hKd hK (l : Fin g → ℂ) 0
  have e2 := hb l 0
  rw [zero_add] at e2
  rw [e2, map_zero, neg_zero, Complex.exp_zero, mul_one, mul_right_comm] at e1
  have e3 : b l * cexp (-L l) = 1 := by
    have := mul_right_cancel₀ (h0 0) (e1.trans (one_mul _).symm)
    exact this
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at e3
  simpa only [ContinuousLinearMap.coe_coe] using e3
end GlobalTheory.ArtinKernel

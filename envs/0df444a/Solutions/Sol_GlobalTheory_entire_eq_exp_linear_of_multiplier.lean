-- Prove2me | solution 1 for GlobalTheory.entire_eq_exp_linear_of_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:19.714531+00:00
-- url     : https://prove2.me/submissions/ef06236b-1226-4b45-80c6-79106be78a59

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace GlobalTheory
theorem _root_.solution [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {h : E → ℂ} (hd : Differentiable ℂ h) (h0 : ∀ z, h z ≠ 0) {S : Set E}
    (hS : Submodule.span ℝ S = ⊤) (hper : ∀ s ∈ S, ∃ c : ℂ, ∀ z, h (z + s) = c * h z) :
    ∃ L : E →L[ℂ] ℂ, ∀ z, h z = h 0 * Complex.exp (L z) := by
  set F : E → E →L[ℂ] ℂ := fun z => (h z)⁻¹ • fderiv ℂ h z with hFdef
  have hfd : Differentiable ℂ (fderiv ℂ h) := by
    intro z
    exact (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hd.differentiableOn).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hF : Differentiable ℂ F := (hd.inv h0).smul hfd
  have hFper : ∀ x, ∀ s ∈ S, F (x + s) = F x := by
    intro x s hs
    obtain ⟨c, hc⟩ := hper s hs
    have hc0 : c ≠ 0 := by
      intro hc0
      apply h0 s
      have := hc 0
      rwa [zero_add, hc0, zero_mul] at this
    have hfun : (fun z => h (z + s)) = fun z => c * h z := funext hc
    have hder : fderiv ℂ h (x + s) = c • fderiv ℂ h x := by
      rw [← fderiv_comp_add_right, hfun, fderiv_const_mul (hd x) c]
    simp only [hFdef]
    rw [hder, hc, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have hconst : ∀ z, F z = F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hF hS hFper z 0
  have hdh : ∀ z, fderiv ℂ h z = h z • F 0 := by
    intro z
    rw [← hconst z, hFdef]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (h0 z), one_smul]
  refine ⟨F 0, fun z => ?_⟩
  have hG : ∀ y, HasFDerivAt (fun z => h z * Complex.exp (-(F 0) z)) (0 : E →L[ℂ] ℂ) y := by
    intro y
    have h1 : HasFDerivAt h (h y • F 0) y := by
      rw [← hdh]
      exact (hd y).hasFDerivAt
    have h2 : HasFDerivAt (fun z => Complex.exp (-(F 0) z)) (Complex.exp (-(F 0) y) • (-(F 0))) y :=
      ((F 0).hasFDerivAt.neg).cexp
    refine (h1.mul h2).congr_fderiv ?_
    simp only [smul_neg, smul_smul, mul_comm (h y), neg_add_cancel]
  have hGc := is_const_of_fderiv_eq_zero (f := fun z => h z * Complex.exp (-(F 0) z))
    (fun y => (hG y).differentiableAt) (fun y => (hG y).fderiv) z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one] at hGc
  rw [← hGc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
end GlobalTheory

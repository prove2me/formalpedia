-- Prove2me | solution 1 for GlobalTheory.SharpGradient.SharpAt.of_minorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:44.232829+00:00
-- url     : https://prove2.me/submissions/ca0b0399-e2e3-4822-862f-55eb45455934

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_nonpos_of_isLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.SharpGradient
namespace SharpAt
theorem _root_.solution {φ ψ : V n → ℝ} {x : V n} {ξ : Fin n → ℂ} (h : SharpAt ψ x ξ)
    (hφ : ContDiffAt ℝ 2 φ x) (hle : ∀ᶠ v in 𝓝 x, ψ v ≤ φ v) (heq : φ x = ψ x) :
    SharpAt φ x ξ := by
  obtain ⟨hψ, h0, hL, hb⟩ := h
  have hrd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => φ y - ψ y) x := by
    filter_upwards [hle] with v hv
    linarith
  have hfd : fderiv ℝ φ x = fderiv ℝ ψ x := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (φ y : ℂ)) x = wd n j (fun y => (ψ y : ℂ)) x := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hmax : IsLocalMax (fun y => ψ y + (-1) * φ y) x := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * φ y) x := hψ.add (contDiffAt_const.mul hφ)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hφ) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hφ ξ] at h2
  have h3 : (leviV n (fun y => (ψ y : ℂ)) x ξ).re ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h2
    linarith
  refine ⟨hφ, heq ▸ h0, hL.trans h3, ?_⟩
  simp only [hwd]
  rw [heq]
  exact hb.trans (mul_le_mul_of_nonneg_left h3 h0)
end SharpAt
end GlobalTheory.SharpGradient

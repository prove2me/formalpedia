-- Prove2me | solution 1 for GlobalTheory.LeviZero.leviV_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:56.148313+00:00
-- url     : https://prove2.me/submissions/8df4768e-266a-4e29-a292-a5201ce12ce8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_log_norm_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_ofReal_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}
namespace GlobalTheory.LeviZero
theorem _root_.solution {d : V n → ℂ} {e c : ℂ} (he : e * e = 1) (hreal : ∀ y, conj (d y) = d y)
    (hd : HasJet ξ x d (cJ e * (1 + cJ c * (sJ * tJ)))) :
    leviV n (fun y => ((Real.log ‖d y‖ : ℝ) : ℂ)) x ξ = c := by
  have h2 := hd.mul hd
  have hu : (fun y => d y * d y) = fun y => ((Complex.normSq (d y) : ℝ) : ℂ) := by
    funext y; rw [← Complex.mul_conj, hreal]
  rw [hu] at h2
  have hcd : ContDiffAt ℝ 2 (fun y => Complex.normSq (d y)) x := by
    have := Complex.reCLM.contDiff.contDiffAt.comp x h2.cd
    simpa [Function.comp_def] using this
  have hv : Complex.normSq (d x) = 1 := by
    have := h2.val
    simp [cJ, sJ, tJ, he] at this
    exact this
  have hh : dDir ξ (fun y => ((Complex.normSq (d y) : ℝ) : ℂ)) x = 0 := by
    rw [h2.hol]; simp [cJ, sJ, tJ, DualNumber.snd_mul]
  have hl : leviV n (fun y => ((Complex.normSq (d y) : ℝ) : ℂ)) x ξ = 2 * c := by
    rw [h2.lev]; simp [cJ, sJ, tJ, DualNumber.snd_mul]
    linear_combination (2 * c) * he
  have hlog : ContDiffAt ℝ 2 Real.log (Complex.normSq (d x)) := by
    rw [hv]; exact Real.contDiffAt_log.2 one_ne_zero
  have hc := ReciprocityTheory.L2DbarEstimates.leviChain n Real.log (fun v => Complex.normSq (d v)) x ξ hcd hlog
  have hd1 : deriv Real.log (Complex.normSq (d x)) = 1 := by
    rw [Real.deriv_log', hv]; simp
  unfold dDir at hh
  rw [hh, hl, hd1] at hc
  have hf : (fun y => ((Real.log ‖d y‖ : ℝ) : ℂ)) =
      fun y => (((1 / 2 : ℝ) * Real.log (Complex.normSq (d y)) : ℝ) : ℂ) := by
    funext y; rw [IW.log_norm_eq]; congr 1; ring
  rw [hf, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (f := fun y => Real.log (Complex.normSq (d y))) _
    (hcd.log (by rw [hv]; exact one_ne_zero)), hc]
  simp
end GlobalTheory.LeviZero

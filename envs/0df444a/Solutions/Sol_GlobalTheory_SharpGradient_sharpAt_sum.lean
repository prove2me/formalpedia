-- Prove2me | solution 1 for GlobalTheory.SharpGradient.sharpAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:17.138924+00:00
-- url     : https://prove2.me/submissions/a3caa45b-d3b5-43bb-a320-49f06e0c8847

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_normSq_sum_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_sum


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
theorem _root_.solution {m : ℕ} {u : Fin m → V n → ℝ} {x : V n} {ξ : Fin n → ℂ}
    (h : ∀ i, SharpAt (u i) x ξ) : SharpAt (fun y => ∑ i, u i y) x ξ := by
  have hc : ∀ i, ContDiffAt ℝ 2 (u i) x := fun i => (h i).1
  have hL := H.leviV_ofReal_sum hc ξ
  have hw : ∑ j, wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x * ξ j =
      ∑ i, ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.wd_ofReal_sum (fun i => (hc i).differentiableAt (by simp)), Finset.sum_mul]
  refine ⟨ContDiffAt.sum fun i _ => hc i, Finset.sum_nonneg fun i _ => (h i).2.1, ?_, ?_⟩
  · rw [hL, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (h i).2.2.1
  · rw [hL, hw, Complex.re_sum]
    exact normSq_sum_le _ _ _ (fun i => (h i).2.1) (fun i => (h i).2.2.1) fun i => (h i).2.2.2
end GlobalTheory.SharpGradient

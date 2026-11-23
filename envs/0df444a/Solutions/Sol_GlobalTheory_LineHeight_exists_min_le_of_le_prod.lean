-- Prove2me | solution 1 for GlobalTheory.LineHeight.exists_min_le_of_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:47.845566+00:00
-- url     : https://prove2.me/submissions/2a070dde-24be-4ca8-8142-156dc0b423f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LineHeight
namespace GlobalTheory.LineHeight
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  by_cases hm0 : m ≤ 0
  · exact absurd ((min_le_right _ _).trans (hm0.trans (hf i0))) (not_le.mpr (hcon i0))
  · have h1 : ∀ i, f i ≤ 1 := fun i => ((hcon i).trans_le (min_le_left _ _)).le
    have hp : ∏ i, f i ≤ f i0 := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right (hf i0) (Finset.prod_le_one (fun i _ => hf i) fun i _ => h1 i)
    have h2 : f i0 < m := (hcon i0).trans_le (min_le_right _ _)
    linarith
end GlobalTheory.LineHeight

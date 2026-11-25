-- Prove2me | solution 1 for GlobalTheory.ofReal_tsum_sq_le_tsum_div_mul_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:58:31.977533+00:00
-- url     : https://prove2.me/submissions/63f8779b-92f7-4b17-9152-24d1a4253bda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealTsumSqLeTsumDivMulTsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by
  have ht : Filter.Tendsto (fun s : Finset ι => ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((∑' i, a i) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.pow hs.hasSum 2)
  refine le_of_tendsto' ht fun s => ?_
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / Real.sqrt (k i))
      (fun i => Real.sqrt (k i))
    have e1 : ∀ i, a i / Real.sqrt (k i) * Real.sqrt (k i) = a i := fun i =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hk i)).ne'
    have e2 : ∀ i, Real.sqrt (k i) ^ 2 = k i := fun i => Real.sq_sqrt (hk i).le
    simp only [e1, div_pow, e2] at h0
    exact h0
  have hd : ∀ i, 0 ≤ a i ^ 2 / k i := fun i => div_nonneg (sq_nonneg _) (hk i).le
  calc ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)
      ≤ ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i) := ENNReal.ofReal_le_ofReal h1
    _ = (∑ i ∈ s, ENNReal.ofReal (a i ^ 2 / k i)) * ∑ i ∈ s, ENNReal.ofReal (k i) := by
      rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hd i),
        ENNReal.ofReal_sum_of_nonneg fun i _ => hd i,
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hk i).le]
    _ ≤ _ := mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s)
end GlobalTheory

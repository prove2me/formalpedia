-- Prove2me | solution 1 for GlobalTheory.lowerSemicontinuousOn_sum_pos_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:09.427807+00:00
-- url     : https://prove2.me/submissions/9227ee02-e63b-4384-9b44-76da998365ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedHeightSupDriftOrthonormalFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAutStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeightsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSubspaceHeightGramDeterminantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (I : Finset ℕ) (e : ℕ → ℝ) (he : ∀ i, 0 < e i) (α : ℕ → Y → ℝ)
    (hα : ∀ i ∈ I, LowerSemicontinuousOn (α i) s) :
    LowerSemicontinuousOn (fun x => ∑ i ∈ I, e i * α i x) s := by
  have key : ∀ i ∈ I, LowerSemicontinuousOn (fun x => e i * α i x) s := by
    intro i hi x hx y hy
    have h1 : y / e i < α i x := by
      rw [div_lt_iff₀ (he i)]
      linarith
    filter_upwards [hα i hi x hx (y / e i) h1] with z hz
    rw [gt_iff_lt, div_lt_iff₀ (he i)] at hz
    show y < e i * α i z
    linarith
  exact lowerSemicontinuousOn_sum key
end GlobalTheory

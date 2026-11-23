-- Prove2me | solution 1 for GlobalTheory.summable_lattice_exp_neg_mul_norm_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:45.830833+00:00
-- url     : https://prove2.me/submissions/1225f357-9cde-4c12-a8ee-a7a67cb575f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq
import Theorems.Thm_GlobalTheory_exp_neg_mul_norm_add_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]
namespace GlobalTheory
theorem _root_.solution {a : ℝ} (ha : 0 < a) (u : E) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E) + u‖ ^ 2) :=
  .of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun x ↦ exp_neg_mul_norm_add_sq_le ha.le (x : E) le_rfl)
    ((summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _)
end GlobalTheory

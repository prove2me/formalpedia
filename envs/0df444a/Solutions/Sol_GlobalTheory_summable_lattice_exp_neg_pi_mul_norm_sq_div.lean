-- Prove2me | solution 1 for GlobalTheory.summable_lattice_exp_neg_pi_mul_norm_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:59.989736+00:00
-- url     : https://prove2.me/submissions/ceeb9e86-f5db-4a43-b382-2f370d22ebb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_sq

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Summable fun y : L ↦ Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
  refine (summable_lattice_exp_neg_mul_norm_sq L (div_pos Real.pi_pos ht)).congr fun y ↦ ?_
  congr 1
  ring
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.norm_cexp_neg_pi_mul_norm_sq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:07.88181+00:00
-- url     : https://prove2.me/submissions/860821ac-22d0-4bb7-b4d4-5ef073c1931a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv

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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (b : ℂ) (w v : E) :
    ‖Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)‖ =
      Real.exp (-(π * b.re) * ‖v‖ ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.min_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:09.457461+00:00
-- url     : https://prove2.me/submissions/8f56b40f-4a69-414e-b907-c6968e92b584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {u : ℝ} (hu : 0 < u) : min u (1 / u) ≤ Real.sqrt u := by
  rcases le_total u 1 with h | h
  · refine (min_le_left _ _).trans (Real.le_sqrt_of_sq_le ?_)
    nlinarith
  · exact (min_le_right _ _).trans (((div_le_one hu).2 h).trans (Real.one_le_sqrt.2 h))
end GlobalTheory.Hk.RealChar

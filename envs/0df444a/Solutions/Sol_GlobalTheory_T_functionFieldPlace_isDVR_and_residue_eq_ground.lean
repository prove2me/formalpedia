-- Prove2me | solution 1 for GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:03.518094+00:00
-- url     : https://prove2.me/submissions/3afb11c7-ec9a-40c0-96dc-dd118ff1fa25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGround
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
import Theorems.Thm_GlobalTheory_Nef_place_isDVR_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  first | exact @GlobalTheory.Nef.place_isDVR_residue | exact GlobalTheory.Nef.place_isDVR_residue | (intros; apply GlobalTheory.Nef.place_isDVR_residue <;> assumption)
end _root_.GlobalTheory.T

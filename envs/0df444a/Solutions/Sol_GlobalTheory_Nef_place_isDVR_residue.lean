-- Prove2me | solution 1 for GlobalTheory.Nef.place_isDVR_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:58:20.142504+00:00
-- url     : https://prove2.me/submissions/9a47e62e-4db0-4c84-9b32-20590852d674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGround
import Theorems.Thm_GlobalTheory_Nef_isDiscreteValuationRing_functionFieldPlace_ring
import Theorems.Thm_GlobalTheory_Nef_functionFieldPlace_exists_const_sub_lt_one

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
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  intro k F _ _ _ _ _ hF v
  exact ⟨isDiscreteValuationRing_functionFieldPlace_ring v, fun x hx => functionFieldPlace_exists_const_sub_lt_one hF v x hx⟩
end GlobalTheory.Nef

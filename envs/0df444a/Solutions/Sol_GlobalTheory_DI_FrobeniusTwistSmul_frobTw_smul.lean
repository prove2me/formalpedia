-- Prove2me | solution 1 for GlobalTheory.DI.FrobeniusTwistSmul.frobTw_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:29.299788+00:00
-- url     : https://prove2.me/submissions/6a2ed693-2332-4ce7-8404-ac9c40d2c7cc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExteriorAlgebraExtensionOfFrobeniusSemilin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FrobeniusTwistSmul
variable (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (W : Type) [AddCommGroup W] [Module K W]
namespace GlobalTheory.DI.FrobeniusTwistSmul
theorem _root_.solution (c : K) (x : FrobTw K p W) :
    c • x = ((c ^ p • (show W from x) : W) : FrobTw K p W) := by
  show (frobenius K p c) • (show W from x) = _
  rw [frobenius_def]
end GlobalTheory.DI.FrobeniusTwistSmul

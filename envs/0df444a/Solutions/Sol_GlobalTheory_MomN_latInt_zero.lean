-- Prove2me | solution 1 for GlobalTheory.MomN.latInt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:20.871024+00:00
-- url     : https://prove2.me/submissions/64e13a0f-4ba5-43ec-a371-cd83483db7fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LatIntZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.MomN
open GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.MomN
theorem _root_.solution (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) : LatInt ι ω Λ (fun _ => 0) := by
  intro κ _ v _
  refine ⟨0, by simp, ?_⟩
  intro k j f _
  simp
end GlobalTheory.MomN

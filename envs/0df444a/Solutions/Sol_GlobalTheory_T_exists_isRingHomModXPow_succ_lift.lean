-- Prove2me | solution 1 for GlobalTheory.T.exists_isRingHomModXPow_succ_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:30.962485+00:00
-- url     : https://prove2.me/submissions/8baf905e-ad33-4b54-a83d-8bea5e27d242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLiftStatement
import Theorems.Thm_GlobalTheory_Nef_PathJet_exists_lift_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R), π.FormallySmooth → ∀ n : ℕ, 1 ≤ n → ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β n φ → ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_lift_succ | exact GlobalTheory.Nef.PathJet.exists_lift_succ | (intros; apply GlobalTheory.Nef.PathJet.exists_lift_succ <;> assumption)
end _root_.GlobalTheory.T

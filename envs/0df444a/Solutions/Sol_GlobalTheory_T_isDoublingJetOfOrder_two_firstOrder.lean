-- Prove2me | solution 1 for GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:11.919307+00:00
-- url     : https://prove2.me/submissions/22b29114-a945-4d3e-aa2a-127452111f75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrderStatement
import Theorems.Thm_GlobalTheory_Nef_PathJet_firstOrder_isJet


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
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  first | exact @GlobalTheory.Nef.PathJet.firstOrder_isJet | exact GlobalTheory.Nef.PathJet.firstOrder_isJet | (intros; apply GlobalTheory.Nef.PathJet.firstOrder_isJet <;> assumption)
end _root_.GlobalTheory.T

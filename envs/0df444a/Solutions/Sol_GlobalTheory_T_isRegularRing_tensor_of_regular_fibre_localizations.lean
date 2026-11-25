-- Prove2me | solution 1 for GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:11.373821+00:00
-- url     : https://prove2.me/submissions/f24c1c54-743c-4260-a22f-995b44f2ddac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularRingTensorOfFibreLocalRingsStatement
import Theorems.Thm_GlobalTheory_isRegularRing_tensor_of_fibre_localRings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q → IsRegularLocalRing (Localization.AtPrime n ⧸ (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) → IsRegularRing (T ⊗[S] K) := by
  first | exact @GlobalTheory.isRegularRing_tensor_of_fibre_localRings | exact GlobalTheory.isRegularRing_tensor_of_fibre_localRings | (intros; apply GlobalTheory.isRegularRing_tensor_of_fibre_localRings <;> assumption)
end _root_.GlobalTheory.T

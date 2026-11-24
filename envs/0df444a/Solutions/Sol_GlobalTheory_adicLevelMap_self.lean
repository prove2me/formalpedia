-- Prove2me | solution 1 for GlobalTheory.adicLevelMap_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:24.526039+00:00
-- url     : https://prove2.me/submissions/fe1c69d2-ba5e-4c79-b473-7484b3cbc7c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
namespace GlobalTheory
theorem _root_.solution (n : ℕ) : adicLevelMap I (le_refl n) = 𝟙 _ := by
  have : Ideal.Quotient.factorPow I (le_refl n) = RingHom.id _ := Ideal.Quotient.ringHom_ext rfl
  rw [adicLevelMap, this, CommRingCat.ofHom_id, Spec.map_id]
end GlobalTheory

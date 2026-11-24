-- Prove2me | solution 1 for GlobalTheory.adicLevelMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:23.107167+00:00
-- url     : https://prove2.me/submissions/71277716-80f5-4757-b25a-4c1547d748ae

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
theorem _root_.solution {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    adicLevelMap I h ≫ adicLevelMap I h' = adicLevelMap I (h.trans h') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact Ideal.Quotient.ringHom_ext rfl
end GlobalTheory

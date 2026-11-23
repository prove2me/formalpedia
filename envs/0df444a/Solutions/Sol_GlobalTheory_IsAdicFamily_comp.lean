-- Prove2me | solution 1 for GlobalTheory.IsAdicFamily.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:34.060792+00:00
-- url     : https://prove2.me/submissions/68b169da-6180-4526-b3ea-64aed1bef4e7

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
variable {I}
namespace GlobalTheory
namespace IsAdicFamily
theorem _root_.solution {X Y : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) (p : X ⟶ Y) : IsAdicFamily I fun n => f n ≫ p :=
  fun n => by rw [← Category.assoc, hf n]
end IsAdicFamily
end GlobalTheory

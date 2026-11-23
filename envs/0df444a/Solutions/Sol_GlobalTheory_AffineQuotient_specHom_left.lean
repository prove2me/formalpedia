-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.specHom_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:45.587923+00:00
-- url     : https://prove2.me/submissions/7815384f-18e8-4fe0-b805-b10e5bbe6042

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
variable {S T T' : Type} [CommRing S] [CommRing T] [CommRing T'] [Algebra R S] [Algebra R T]
  [Algebra R T']
namespace GlobalTheory.AffineQuotient
theorem _root_.solution (φ : S →ₐ[R] T) :
    (specHom φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl
end GlobalTheory.AffineQuotient

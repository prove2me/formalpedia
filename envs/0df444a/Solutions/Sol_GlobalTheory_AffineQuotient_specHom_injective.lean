-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.specHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:37.376411+00:00
-- url     : https://prove2.me/submissions/ff5fefe2-a7c1-42d6-81a2-2122f4f21eb8

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
theorem _root_.solution : Function.Injective (specHom : (S →ₐ[R] T) → _) := by
  intro φ ψ h
  have := Spec.map_injective congr(($h).left)
  ext x
  exact congr($this x)
end GlobalTheory.AffineQuotient

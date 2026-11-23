-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.specHom_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:44.963729+00:00
-- url     : https://prove2.me/submissions/6632d3e8-ea20-49d9-a4e9-de38c656d65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_left

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
theorem _root_.solution (φ : S →ₐ[R] T) (ψ : T →ₐ[R] T') :
    specHom (ψ.comp φ) = specHom ψ ≫ specHom φ := by
  ext1
  rw [Over.comp_left, specHom_left, specHom_left, specHom_left, ← Spec.map_comp]
  rfl
end GlobalTheory.AffineQuotient

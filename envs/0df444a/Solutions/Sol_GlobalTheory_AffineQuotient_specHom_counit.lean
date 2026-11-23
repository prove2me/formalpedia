-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.specHom_counit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:45.8338+00:00
-- url     : https://prove2.me/submissions/08453ff3-407f-449e-b6d1-ac4b936041c1

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
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution {T : Type} [CommRing T] [Algebra R T] :
    specHom ((Algebra.ofId R T).comp (Bialgebra.counitAlgHom R Λ)) =
      toUnit _ ≫ η[specOver R Λ] := by
  ext1
  rw [Over.comp_left, one_spec_asOver_spec_left, specHom_left]
  exact Spec.map_comp (CommRingCat.ofHom (Bialgebra.counitAlgHom R Λ).toRingHom)
    (CommRingCat.ofHom (algebraMap R T))
end GlobalTheory.AffineQuotient

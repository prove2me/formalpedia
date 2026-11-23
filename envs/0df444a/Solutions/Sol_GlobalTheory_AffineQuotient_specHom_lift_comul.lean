-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.specHom_lift_comul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:45.730737+00:00
-- url     : https://prove2.me/submissions/442abac0-584e-4126-98be-96d7bd2644d9

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
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution {T : Type} [CommRing T] [Algebra R T] (φ ψ : Λ →ₐ[R] T) :
    specHom ((Algebra.TensorProduct.lift φ ψ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) = specHom φ * specHom ψ := by
  have := (Spec.mapMulEquiv (R := R) (S := Λ) (T := T)).map_mul (WithConv.toConv φ)
    (WithConv.toConv ψ)
  refine Eq.trans ?_ this
  change specHom _ = specHom _
  congr 1
  rw [AlgHom.convMul_def, ← AlgHom.comp_assoc]
  congr 1
  ext <;> simp
end GlobalTheory.AffineQuotient

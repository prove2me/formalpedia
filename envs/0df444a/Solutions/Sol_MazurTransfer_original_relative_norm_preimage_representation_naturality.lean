-- Prove2me | solution 1 for MazurTransfer.original_relative_norm_preimage_representation_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:08:30.981762+00:00
-- url     : https://prove2.me/submissions/14e66801-2545-4dd2-abf9-f97ba6345cc9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original pullback fibre represents preimages of the same given section, with its exact point equivalence over every test scheme.
Named downstream consumer: the same integral nineteen norm-preimage torsor and its selected mu19 quotient.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimageRepresentationData20261020
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeNormPreimagePointTorsor MazurTransfer.RelativeNormPreimageRepresentation
universe u
namespace MazurTransfer.OriginalRelativeNormPreimageRepresentationBoundary20261020
end MazurTransfer.OriginalRelativeNormPreimageRepresentationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL pullback fibre of a relative endomorphism
represents its preimages of the GIVEN integral section over EVERY test
scheme, with every precomposition map retained.
Named downstream consumer: principal-action isomorphism of the actual
finite-flat integral nineteen norm torsor.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativeNormPreimageRepresentationProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeNormPreimagePointTorsor
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (F : SchemeHomOver f f)
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)









variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))









variable {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
variable (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')

theorem pulledPoint_natural :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (pulledPoint a t) = pulledPoint a t' := by
  apply Subtype.ext
  change ψ ≫ (t ≫ a.val) = t' ≫ a.val
  rw [← Category.assoc, hψ]

theorem pointsEquiv_natural (b : SchemeHomOver t (fibreStr F a)) :
    (pointsEquiv F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv F a t b).val := by
  apply Subtype.ext
  exact Category.assoc _ _ _

end MazurTransfer.OriginalRelativeNormPreimageRepresentationProof20261020

theorem solution : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}, ∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') ,
GoodReductionJacobian.schemeHomOverComp ψ hψ (pulledPoint a t) = pulledPoint a t') ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}, ∀ (F : SchemeHomOver f f) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b : SchemeHomOver t (fibreStr F a)),
(pointsEquiv F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (pointsEquiv F a t b).val) := by
  exact ⟨MazurTransfer.OriginalRelativeNormPreimageRepresentationProof20261020.pulledPoint_natural, MazurTransfer.OriginalRelativeNormPreimageRepresentationProof20261020.pointsEquiv_natural⟩
#print axioms solution

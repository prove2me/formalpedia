-- Prove2me | solution 1 for MazurTransfer.original_relative_norm_preimage_principal_iso_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:31:28.626772+00:00
-- url     : https://prove2.me/submissions/d113ac61-c13d-4bbd-8f9e-2ca8f762809c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same endomorphism preimage fibre has its original principal-action isomorphism over the same base, realizing the same point action on every test scheme.
Named downstream consumer: the actual finite-flat integral norm torsor and selected mu19 pushforward at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePrincipalIsoData20261020
import Theorems.Thm_MazurTransfer_original_scheme_point_natural_equivalence_induces_iso
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf MazurTransfer.RelativeNormPreimagePointTorsor
open MazurTransfer.RelativeNormPreimageRepresentation MazurTransfer.RelativeNormPreimagePrincipalIso
universe u
namespace MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoBoundary20261020
end MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the GIVEN relative endomorphism's ACTUAL preimage fibre
has a principal-action isomorphism kernel × fibre ≅ fibre × fibre over
the SAME base; it realizes the natural point action on EVERY test scheme.
Named downstream consumer: actual finite-flat integral norm torsors and
selected mu19 pushforwards at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLawFiniteFlatKernelHopf RelativeNormPreimagePointTorsor
open RelativeNormPreimageRepresentation
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)
variable (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
  NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
variable (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
  NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
    L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)




variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))













variable {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
variable (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')









include hOne hMul in
theorem principal_natural (b : SchemeHomOver t (sourceStr L F a)) :
    principalPointsEquiv L F hOne hMul a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (principalPointsEquiv L F hOne hMul a t b) := by
  apply (targetPointsEquiv F a t').injective
  apply Prod.ext
  · apply Subtype.ext
    rw [principal_first, source_first_natural, source_second_natural, target_first_natural, principal_first]
    exact (L.mul_natural t t' ψ hψ _ _).symm
  · apply Subtype.ext
    rw [principal_second, source_second_natural, target_second_natural, principal_second]



include hOne hMul in
theorem principalOverIso_point_map (b : SchemeHomOver t (sourceStr L F a)) :
    (principalPointsEquiv L F hOne hMul a t b).val =
      b.val ≫ (principalOverIso L F hOne hMul a).hom.left :=
  (MazurTransfer.original_scheme_point_natural_equivalence_induces_iso).2 (sourceStr L F a) (targetStr F a)
    (principalPointsEquiv L F hOne hMul a)
    (fun t t' ψ hψ b => principal_natural L F hOne hMul a t t' ψ hψ b) t b

include hOne hMul in
theorem act_unit (y : preimagePoints F (pulledPoint a t)) :
    act L F hMul (⟨L.one t, hOne t⟩ : kernelPoints L F t) y = y :=
  Subtype.ext (L.one_mul t y.val)

include hMul in
theorem act_assoc (k l : kernelPoints L F t) (y : preimagePoints F (pulledPoint a t)) :
    act L F hMul (⟨L.mul t k.val l.val, kernelPoints_mul L F hMul t k l⟩ : kernelPoints L F t) y =
      act L F hMul k (act L F hMul l y) :=
  Subtype.ext (L.mul_assoc t k.val l.val y.val)

end MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020


theorem solution : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (b : SchemeHomOver t (sourceStr L F a)),
principalPointsEquiv L F hOne hMul a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (principalPointsEquiv L F hOne hMul a t b)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t (sourceStr L F a)),
(principalPointsEquiv L F hOne hMul a t b).val =
      b.val ≫ (principalOverIso L F hOne hMul a).hom.left) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : preimagePoints F (pulledPoint a t)),
act L F hMul (⟨L.one t, hOne t⟩ : kernelPoints L F t) y = y) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (k l : kernelPoints L F t) (y : preimagePoints F (pulledPoint a t)),
act L F hMul (⟨L.mul t k.val l.val, kernelPoints_mul L F hMul t k l⟩ : kernelPoints L F t) y =
      act L F hMul k (act L F hMul l y)) := by
  exact ⟨MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020.principal_natural, MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020.principalOverIso_point_map, MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020.act_unit, MazurTransfer.OriginalRelativeNormPreimagePrincipalIsoProof20261020.act_assoc⟩
#print axioms solution

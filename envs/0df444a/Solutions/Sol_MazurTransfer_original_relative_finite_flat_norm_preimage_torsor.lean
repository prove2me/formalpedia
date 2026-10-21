-- Prove2me | solution 1 for MazurTransfer.original_relative_finite_flat_norm_preimage_torsor
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:40:32.34361+00:00
-- url     : https://prove2.me/submissions/eb37e227-7155-4a57-b926-6d2d6e770653

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual fibre of the given finite-flat surjective endomorphism is the original preimage torsor under its same kernel, retaining the principal-action map on every test scheme.
Named downstream consumer: actual integral nineteen norm fibres and their selected mu19 quotient torsors.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeFiniteFlatNormPreimageTorsorData20261020
import Theorems.Thm_MazurTransfer_original_relative_norm_preimage_principal_iso_laws
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeNormPreimageRepresentation MazurTransfer.RelativeNormPreimagePrincipalIso
open MazurTransfer.RelativeFiniteFlatNormPreimageTorsor
universe u
namespace MazurTransfer.OriginalRelativeFiniteFlatNormPreimageTorsorBoundary20261020
end MazurTransfer.OriginalRelativeFiniteFlatNormPreimageTorsorBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL fibre of a finite-flat surjective endomorphism
is an fppf preimage torsor under its SAME represented kernel. Retain the
principal-action map on EVERY test scheme, not an arbitrary isomorphism.
Named downstream consumer: actual integral nineteen norm fibres and their
selected normalized mu19 quotient torsors.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativeFiniteFlatNormPreimageTorsorProof20261020
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeNormPreimageRepresentation RelativeNormPreimagePrincipalIso
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)
variable (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
  NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
variable (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
  NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
    L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)



include hOne hMul in
theorem finite_flat_preimage_torsor [IsFinite F.val] [Flat F.val]
    [LocallyOfFinitePresentation F.val] [Surjective F.val] :
    HasFiniteFlatPreimageTorsor L F hOne hMul a :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    principalOverIso L F hOne hMul a, fun t b => (MazurTransfer.original_relative_norm_preimage_principal_iso_laws).2.1 L F hOne hMul a t b⟩

end MazurTransfer.OriginalRelativeFiniteFlatNormPreimageTorsorProof20261020

theorem solution : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) [IsFinite F.val] [Flat F.val]
    [LocallyOfFinitePresentation F.val] [Surjective F.val],
HasFiniteFlatPreimageTorsor L F hOne hMul a) := by
  exact MazurTransfer.OriginalRelativeFiniteFlatNormPreimageTorsorProof20261020.finite_flat_preimage_torsor
#print axioms solution

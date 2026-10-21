-- Prove2me | solution 1 for MazurTransfer.original_scheme_point_natural_equivalence_induces_iso
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:23:26.838224+00:00
-- url     : https://prove2.me/submissions/a3f87de3-53f5-4c36-b28a-497bba9c50ec

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original natural equivalence on all scheme-valued points induces the original isomorphism over the same base and retains the given point map.
Named downstream consumer: the principal-action scheme isomorphism of the actual integral norm-preimage torsor at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalSchemePointNaturalEquivalenceIsoData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.SchemePointNaturalEquivalenceIso
universe u
namespace MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoBoundary20261020
end MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a natural equivalence on ALL scheme-valued points induces
an isomorphism over the SAME base, retaining the given point map.
Named downstream consumer: principal-action scheme isomorphism of the
actual integral norm-preimage torsor at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoProof20261020
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
variable (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g)
variable (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
  (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
  e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
    GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x))

include hNat in
theorem symm_natural {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t g) :
    (e t').symm (GoodReductionJacobian.schemeHomOverComp ψ hψ y) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ ((e t).symm y) := by
  apply (e t').injective
  rw [Equiv.apply_symm_apply, hNat, Equiv.apply_symm_apply]












include hNat in
theorem schemeIso_point_map {T : Scheme.{u}} (t : T ⟶ B) (x : SchemeHomOver t f) :
    (e t x).val = x.val ≫ (schemeIso f g e hNat).hom := by
  have h := hNat f t x.val x.property (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f)
  have he : GoodReductionJacobian.schemeHomOverComp x.val x.property
      (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f) = x := Subtype.ext (Category.comp_id _)
  rw [he] at h
  exact congrArg Subtype.val h

end MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoProof20261020

theorem solution : (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g) (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f), e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x)), ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t g),
(e t').symm (GoodReductionJacobian.schemeHomOverComp ψ hψ y) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ ((e t).symm y)) ∧ (∀ {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e : ∀ {T : Scheme.{u}} (t : T ⟶ B), SchemeHomOver t f ≃ SchemeHomOver t g) (hNat : ∀ {T T' : Scheme.{u}} (t : T ⟶ B) (t' : T' ⟶ B) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f), e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (e t x)), ∀ {T : Scheme.{u}} (t : T ⟶ B) (x : SchemeHomOver t f),
(e t x).val = x.val ≫ (schemeIso f g e hNat).hom) := by
  exact ⟨MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoProof20261020.symm_natural, MazurTransfer.OriginalSchemePointNaturalEquivalenceIsoProof20261020.schemeIso_point_map⟩
#print axioms solution

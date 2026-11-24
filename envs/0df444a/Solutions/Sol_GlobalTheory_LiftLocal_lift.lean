-- Prove2me | solution 1 for GlobalTheory.LiftLocal.lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:41.888234+00:00
-- url     : https://prove2.me/submissions/8a661d3b-fc4d-4c3e-bab1-037e11282bd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftLocalPointAlongAffineFlatSurjection
import Theorems.Thm_GlobalTheory_LiftLocal_toStalk_bijective
import Theorems.Thm_GlobalTheory_LiftLocal_isLocalHom_of_bijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LiftLocal
namespace GlobalTheory.LiftLocal
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [Scheme.Spec_fromSpecStalk']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
end GlobalTheory.LiftLocal

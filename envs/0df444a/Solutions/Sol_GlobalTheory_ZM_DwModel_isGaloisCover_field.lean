-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.isGaloisCover_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:03.569289+00:00
-- url     : https://prove2.me/submissions/5009ca9c-e7e6-4bfe-9165-eb477156acb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZM.DwModel
private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl
private lemma spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, spMap f = y :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩
private lemma spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'
end GlobalTheory.ZM.DwModel
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisCover (L ≃ₐ[K] L) (fun σ => spMap (σ : L →+* L)) (spMap (algebraMap K L)) where
  finite := inferInstance
  one := by
    show Spec.map _ = _
    convert Spec.map_id (CommRingCat.of L)
    rfl
  mul a c := by
    show spMap (((a * c : L ≃ₐ[K] L) : L →+* L)) = _
    rw [← spMap_comp_moduli_spaces]
    rfl
  inv a := by
    rw [← spMap_comp_moduli_spaces]
    congr 1
    ext r
    exact a.commutes r
  fin := by
    show IsFinite (Spec.map _)
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  etale := by
    show Etale (Spec.map _)
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    show (algebraMap K L).Etale
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  onto := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  fibre K' _ _ y y' h := by
    obtain ⟨f, rfl⟩ := spMap_surjective' y
    obtain ⟨f', rfl⟩ := spMap_surjective' y'
    rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
    have hfa := spMap_inj_lemma_3 h
    let _ : Algebra K K' := (f.comp (algebraMap K L)).toAlgebra
    let φ : L →ₐ[K] K' := { f with commutes' := fun _ => rfl }
    let φ' : L →ₐ[K] K' :=
      { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
    let Φ : (L ≃ₐ[K] L) → (L →ₐ[K] K') := fun a => φ.comp a.toAlgHom
    have hinj : Function.Injective Φ := by
      intro a b hab
      ext x
      exact f.injective (AlgHom.congr_fun hab x)
    have hcard : Nat.card (L →ₐ[K] K') ≤ Nat.card (L ≃ₐ[K] L) := by
      rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
    obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
    refine ⟨a, ?_, fun b hb => ?_⟩
    · show spMap f ≫ spMap (a : L →+* L) = spMap f'
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext x
      exact AlgHom.congr_fun ha x
    · have hb' : f.comp (b : L →+* L) = f' := by
        have hb0 : spMap f ≫ spMap (b : L →+* L) = spMap f' := hb
        rw [← spMap_comp_moduli_spaces] at hb0
        exact spMap_inj_lemma_3 hb0
      apply hinj
      ext x
      exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm
end GlobalTheory.ZM.DwModel

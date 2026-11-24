-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:31.330012+00:00
-- url     : https://prove2.me/submissions/32afc81f-6774-4483-a8d0-1ffac67e0427

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_surjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_bijective
import Theorems.Thm_GlobalTheory_DenseFibreIso_of_local
import Theorems.Thm_GlobalTheory_DenseFibreIso_local_of_ring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Γ' X : Scheme.{0}) (s : X ⟶ Sp R) (f : Γ' ⟶ X) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProper s → Flat s → IsProper f → Flat (f ≫ s) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ IsIso (pullback.snd f (pullback.fst s (spMap x)))) → IsIso f := by
  intro R _ _ Γ' X s f P hP₀ _ _ _ _ h
  have hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p := fun q hq => by
    obtain ⟨p, h1, h2, h3, -⟩ := hP₀ q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hfin : IsFinite f := by
    refine of_local s f @IsFinite P hP fun x hx => ?_
    obtain ⟨K, _, t, ht, hi⟩ := h _ hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := spMap t) x
      (⊥ : PrimeSpectrum K) (PrimeSpectrum.ext ht.symm)
    have hf : (f ⁻¹' {x}).Finite := by
      refine (Set.finite_singleton ((inv (pullback.snd f (pullback.fst s (spMap t))) ≫
        pullback.fst f (pullback.fst s (spMap t))) z)).subset fun y hy => ?_
      obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
        (g := pullback.fst s (spMap t)) y z (hy.trans hz.symm)
      rw [Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id_assoc]
    obtain ⟨V, hV, hV'⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hf
    exact ⟨_, _, _, _, _, isPullback_morphismRestrict f V, inferInstance, by simpa using hV, hV'⟩
  have hcl : IsClosedImmersion f := by
    refine of_local s f @IsClosedImmersion P hP fun x hx => ?_
    obtain ⟨K, _, t, ht, hi⟩ := h _ hx
    let : Algebra R K := t.toAlgebra
    refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht
    have h1 : IsFinite (spMap (algebraMap A B)) :=
      MorphismProperty.of_isPullback (P := @IsFinite) H.flip hfin
    have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
    obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hb.2 m
    exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ ha'⟩
  refine of_local s f (MorphismProperty.isomorphisms _) P hP fun x hx => ?_
  obtain ⟨K, _, t, ht, hi⟩ := h _ hx
  let : Algebra R K := t.toAlgebra
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x ht
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have h2 : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
      rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have : IsNoetherianRing A :=
    isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion j)
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective R K hs hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩
end GlobalTheory.DenseFibreIso

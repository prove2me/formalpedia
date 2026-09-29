-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5b2c92fb-1e44-588c-9267-78fafedc0780

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit.AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit.GoodReductionJacobian"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage IsSchemeTheoreticallyDominant.isReduced LocallyOfFiniteType Spec Spec.map Scheme IsSchemeTheoreticallyDominant.pullbackFst Spec.map_base IsReduced.of_openCover IsSchemeTheoreticallyDominant Flat IsReduced locallyOfFiniteType_of_comp Spec.preimage HasRingHomProperty.Spec_iff IsDominant FormallyUnramified IsSchemeTheoreticallyDominant.of_isDominant HasRingHomProperty"
p2m_open "AlgebraicGeometry"

theorem isReduced_carrier_of_formallyUnramified_Spec {F : Type u} [Field F] {S : CommRingCat.{u}}
    (f : Spec S ⟶ Spec (CommRingCat.of F)) [hfu : FormallyUnramified f] [hft : LocallyOfFiniteType f] :
    _root_.IsReduced S := by
  rw [← Spec.map_preimage f] at hfu hft
  have h1 := (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).1 hfu
  have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
  letI := (Spec.preimage f).hom.toAlgebra
  haveI : Algebra.FormallyUnramified F S := h1
  haveI : Algebra.FiniteType F S := h2
  exact Algebra.FormallyUnramified.isReduced_of_field F S

theorem isReduced_of_formallyUnramified_of_locallyOfFiniteType_of_field {F : Type u} [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) [FormallyUnramified f] [LocallyOfFiniteType f] : IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    haveI hfu : FormallyUnramified (X.affineCover.f i ≫ f) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
    haveI hft : LocallyOfFiniteType (X.affineCover.f i ≫ f) := inferInstance
    haveI := @isReduced_carrier_of_formallyUnramified_Spec F _ _ (X.affineCover.f i ≫ f) hfu hft
    change IsReduced (Spec _)
    infer_instance
  exact IsReduced.of_openCover X X.affineCover

theorem isSchemeTheoreticallyDominant_Spec_map_of_injective {R K : Type u} [CommRing R] [_root_.IsReduced R]
    [CommRing K] {φ : R →+* K} (hφ : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨?_⟩
    rw [Spec.map_base]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem isReduced_pullback_section_of_flat_of_formallyUnramified_baseChange
    {R K : Type u} [CommRing R] [Field K]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsSchemeTheoreticallyDominant ι]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (N : G ⟶ G) (hN : N ≫ g = g) [Flat N]
    (e : Spec (CommRingCat.of R) ⟶ G) (he : e ≫ g = 𝟙 _)
    (N' : pullback g ι ⟶ pullback g ι)
    (hN'₁ : N' ≫ pullback.fst g ι = pullback.fst g ι ≫ N)
    (hN'₂ : N' ≫ pullback.snd g ι = pullback.snd g ι)
    [hN' : FormallyUnramified N'] :
    IsReduced (pullback N e) := by

  haveI : IsSchemeTheoreticallyDominant (pullback.fst (pullback.snd N e) ι) :=
    IsSchemeTheoreticallyDominant.pullbackFst _ ι
  suffices hred : IsReduced (pullback (pullback.snd N e) ι) from
    IsSchemeTheoreticallyDominant.isReduced (pullback.fst (pullback.snd N e) ι)

  have t : IsPullback (pullback.snd g ι) (pullback.fst g ι) ι g := (IsPullback.of_hasPullback g ι).flip
  have sq₁ : IsPullback N' (pullback.fst g ι) (pullback.fst g ι) N :=
    IsPullback.of_right (by rw [hN'₂, hN]; exact t) hN'₁ t

  let e' : Spec (CommRingCat.of K) ⟶ pullback g ι :=
    pullback.lift (ι ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have he'₁ : e' ≫ pullback.fst g ι = ι ≫ e := pullback.lift_fst _ _ _
  have he'₂ : e' ≫ pullback.snd g ι = 𝟙 _ := pullback.lift_snd _ _ _
  have hkg : pullback.fst N e ≫ g = pullback.snd N e := by
    rw [← hN, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let a : pullback (pullback.snd N e) ι ⟶ pullback g ι :=
    pullback.lift (pullback.fst _ ι ≫ pullback.fst N e) (pullback.snd _ ι)
      (by rw [Category.assoc, hkg, pullback.condition])
  have ha₁ : a ≫ pullback.fst g ι = pullback.fst _ ι ≫ pullback.fst N e := pullback.lift_fst _ _ _
  have ha₁' : ∀ {W : Scheme.{u}} (h : G ⟶ W),
      a ≫ pullback.fst g ι ≫ h = pullback.fst _ ι ≫ pullback.fst N e ≫ h := fun h => by
    rw [← Category.assoc, ha₁, Category.assoc]
  have ha₂ : a ≫ pullback.snd g ι = pullback.snd _ ι := pullback.lift_snd _ _ _
  have outer : IsPullback (pullback.fst (pullback.snd N e) ι ≫ pullback.fst N e)
      (pullback.snd (pullback.snd N e) ι) N (ι ≫ e) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback _ ι) (IsPullback.of_hasPullback N e)
  have p : a ≫ N' = pullback.snd _ ι ≫ e' := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hN'₁, ha₁', pullback.condition (f := N) (g := e),
        pullback.condition_assoc (f := pullback.snd N e) (g := ι), he'₁]
    · simp only [Category.assoc]
      rw [hN'₂, ha₂, he'₂, Category.comp_id]
  have sq₂ : IsPullback a (pullback.snd _ ι) N' e' := by
    refine IsPullback.of_right ?_ p sq₁.flip
    rw [he'₁, ha₁]
    exact outer

  haveI : FormallyUnramified (pullback.snd (pullback.snd N e) ι) :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified) sq₂ hN'
  haveI : LocallyOfFiniteType N := by
    have : LocallyOfFiniteType (N ≫ g) := by rw [hN]; infer_instance
    exact locallyOfFiniteType_of_comp N g
  haveI : LocallyOfFiniteType (pullback.snd (pullback.snd N e) ι) := inferInstance
  exact isReduced_of_formallyUnramified_of_locallyOfFiniteType_of_field (pullback.snd (pullback.snd N e) ι)

end AlgebraicGeometry

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "schemeNsmul schemeNsmul_over schemeKer IsCommutative one mul baseChange IsCommutative.baseChange fibre formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing baseChange_schemeNsmul_comp_fst_and_eq_pullback_map"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K))
    [Flat (G.schemeNsmul n)] :
    IsReduced (G.schemeKer n) := by
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  haveI : IsSchemeTheoreticallyDominant ι := isSchemeTheoreticallyDominant_Spec_map_of_injective hRK
  obtain ⟨h1, h2, -⟩ := G.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι n
  haveI : FormallyUnramified ((G.baseChange ι).schemeNsmul n) :=
    formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing (G.baseChange ι) (IsCommutative.baseChange ι (G := G) @hcomm) n hn
  exact isReduced_pullback_section_of_flat_of_formallyUnramified_baseChange ι f (G.schemeNsmul n)
    (G.schemeNsmul_over n) (G.one (𝟙 _)).1 (G.one (𝟙 _)).2 ((G.baseChange ι).schemeNsmul n) h1 h2

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) [Flat (G.schemeNsmul n)] :
    IsReduced (G.schemeKer n) :=
  GoodReductionJacobian.RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit hRK G hcomm n hn

end S_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit (solution)

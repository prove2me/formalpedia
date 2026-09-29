-- Prove2me | solution 1 for NeronModelInfra.NeronModelPropertyBundle.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ca6f244d-c558-590f-9e30-45aaf4655e2c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mNeronOpenAbelian

section Transport

variable {S : Type u} [CommRing S] {X Y : Scheme.{u}}
  {gX : X ⟶ Spec (CommRingCat.of S)} {gY : Y ⟶ Spec (CommRingCat.of S)}

def pushPoint (e : SchemeHomOver gX gY) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x : SchemeHomOver t gX) : SchemeHomOver t gY :=
  ⟨x.1 ≫ e.1, by rw [Category.assoc, e.2, x.2]⟩

@[scoped simp] theorem pushPoint_coe (e : SchemeHomOver gX gY) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t gX) :
    (pushPoint e x).1 = x.1 ≫ e.1 := rfl

noncomputable def pullPoint (e : SchemeHomOver gX gY) [IsIso e.1] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (y : SchemeHomOver t gY) : SchemeHomOver t gX :=
  ⟨y.1 ≫ inv e.1, by
    have h : inv e.1 ≫ gX = gY := by rw [IsIso.inv_comp_eq, e.2]
    rw [Category.assoc, h, y.2]⟩

@[scoped simp] theorem pullPoint_coe (e : SchemeHomOver gX gY) [IsIso e.1] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (y : SchemeHomOver t gY) :
    (pullPoint e y).1 = y.1 ≫ inv e.1 := rfl

theorem pullPoint_pushPoint (e : SchemeHomOver gX gY) [IsIso e.1] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t gX) :
    pullPoint e (pushPoint e x) = x := by
  apply Subtype.ext; simp

theorem pushPoint_pullPoint (e : SchemeHomOver gX gY) [IsIso e.1] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} (y : SchemeHomOver t gY) :
    pushPoint e (pullPoint e y) = y := by
  apply Subtype.ext; simp

theorem pushPoint_schemeHomOverComp (e : SchemeHomOver gX gY) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t gX) :
    pushPoint e (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (pushPoint e x) := by
  apply Subtype.ext; simp

theorem pullPoint_schemeHomOverComp (e : SchemeHomOver gX gY) [IsIso e.1] {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t gY) :
    pullPoint e (schemeHomOverComp ψ hψ y) = schemeHomOverComp ψ hψ (pullPoint e y) := by
  apply Subtype.ext; simp

noncomputable def transportLaw (e : SchemeHomOver gX gY) [IsIso e.1] (L : RelativeGroupLaw S gX) :
    RelativeGroupLaw S gY where
  mul t y₁ y₂ := pushPoint e (L.mul t (pullPoint e y₁) (pullPoint e y₂))
  one t := pushPoint e (L.one t)
  inv t y := pushPoint e (L.inv t (pullPoint e y))
  mul_assoc t y₁ y₂ y₃ := by
    simp only [pullPoint_pushPoint, L.mul_assoc]
  one_mul t y := by
    simp only [pullPoint_pushPoint, L.one_mul, pushPoint_pullPoint]
  mul_one t y := by
    simp only [pullPoint_pushPoint, L.mul_one, pushPoint_pullPoint]
  inv_mul_cancel t y := by
    simp only [pullPoint_pushPoint, L.inv_mul_cancel]
  mul_natural t t' ψ hψ y₁ y₂ := by
    rw [← pushPoint_schemeHomOverComp, L.mul_natural t t' ψ hψ, pullPoint_schemeHomOverComp,
      pullPoint_schemeHomOverComp]

theorem abelianSchemePropertyBundle_of_isIso (e : SchemeHomOver gX gY) [IsIso e.1]
    (hX : AbelianSchemePropertyBundle S gX) : AbelianSchemePropertyBundle S gY := by
  have hg : gY = inv e.1 ≫ gX := by rw [IsIso.eq_inv_comp, e.2]
  haveI := hX.smooth
  haveI := hX.proper
  obtain ⟨L⟩ := hX.hasGroupLaw
  refine ⟨?_, ?_, ?_, ⟨transportLaw e L⟩⟩
  · rw [hg]; infer_instance
  · rw [hg]; infer_instance
  · intro s
    have hs := hX.connectedFibres s
    rw [← (Scheme.homeoOfIso (asIso (inv e.1))).isConnected_preimage] at hs
    rw [hg]
    simp [Set.preimage_preimage] at hs
    exact hs

end Transport

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}

theorem isOpenImmersion_genericFibreRestrict (u : SchemeHomOver gU g) [IsOpenImmersion u.1] :
    IsOpenImmersion (genericFibreRestrict R K g gU u).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap g gU u (by rw [Category.comp_id, u.2])
    (by rw [Category.comp_id, Category.id_comp])]
  infer_instance

theorem isClosed_range_genericFibreRestrict (u : SchemeHomOver gU g) [IsProper gU]
    [IsSeparated g] :
    IsClosed (Set.range (genericFibreRestrict R K g gU u).1.base) := by
  haveI : IsProper ((genericFibreRestrict R K g gU u).1 ≫
      pullback.snd g (specGenericFibreInclusion R K)) := by
    rw [(genericFibreRestrict R K g gU u).2]; infer_instance
  haveI : IsProper (genericFibreRestrict R K g gU u).1 :=
    IsProper.of_comp _ (pullback.snd g (specGenericFibreInclusion R K))
  exact (genericFibreRestrict R K g gU u).1.isClosedMap.isClosed_range

theorem nonempty_genericFibre (L : RelativeGroupLaw R gU) :
    Nonempty ↥(pullback gU (specGenericFibreInclusion R K)) := by
  let e := L.one (specGenericFibreInclusion R K)
  let pt : Spec (CommRingCat.of K) ⟶ pullback gU (specGenericFibreInclusion R K) :=
    pullback.lift e.1 (𝟙 _) (by rw [e.2, Category.id_comp])
  exact ⟨pt.base (IsLocalRing.closedPoint K)⟩

end GenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}

theorem isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g := by

  have hNU : NeronModelPropertyBundle R K gU :=
    NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K hU
  haveI := hU.proper
  haveI := hN.separated
  obtain ⟨LU⟩ := hU.hasGroupLaw
  let u : SchemeHomOver gU g := ⟨i, hi⟩
  haveI : IsOpenImmersion u.1 := ‹IsOpenImmersion i›
  let uK := genericFibreRestrict R K g gU u

  haveI hopen : IsOpenImmersion uK.1 := isOpenImmersion_genericFibreRestrict K u
  have hclopen : IsClopen (Set.range uK.1.base) :=
    ⟨isClosed_range_genericFibreRestrict K u, uK.1.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range uK.1.base).Nonempty := by
    obtain ⟨p⟩ := nonempty_genericFibre K LU
    exact ⟨uK.1.base p, p, rfl⟩
  have hrange : Set.range uK.1.base = Set.univ := by
    rcases isClopen_iff.mp hclopen with h | h
    · exact absurd h hne.ne_empty
    · exact h
  haveI : Epi uK.1.base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    exact hrange
  haveI hisoK : IsIso uK.1 := IsOpenImmersion.isIso uK.1

  let vK : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd gU (specGenericFibreInclusion R K)) :=
    ⟨inv uK.1, by rw [IsIso.inv_comp_eq, uK.2]⟩
  have hiso : IsIso u.1 :=
    neronTwoModels_isoExtension_isIso (K := K) hNU.neronMapping hN.neronMapping hU.smooth
      hN.smooth vK (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1) (u := u) rfl
  haveI : IsIso i := hiso
  exact ⟨hiso, abelianSchemePropertyBundle_of_isIso (⟨i, hi⟩ : SchemeHomOver gU g) hU⟩

end Main

end P2mNeronOpenAbelian
p2m_reactivate "P2MW.S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion.P2mNeronOpenAbelian"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g :=
  P2mNeronOpenAbelian.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion K hN i hi hU

end S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
end P2MW
export P2MW.S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion (solution)

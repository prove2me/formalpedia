-- Prove2me | solution 1 for NeronModelInfra.exists_opens_extension_of_isProper_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ed5123b2-1d3b-5b92-9a70-18ba23028a24

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem isLocalizationAway_of_isFractionRing_of_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K where
  map_units := by
    rintro ⟨y, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero))
  surj := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨(a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩), ?_⟩
    have hu : algebraMap R K u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr u.ne_zero
    have hϖK : algebraMap R K (ϖ ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero)
    have huinv : algebraMap R K ↑u⁻¹ = (algebraMap R K u)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    simp only [map_mul, huinv]
    field_simp
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using IsFractionRing.injective R K h⟩

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_isFractionRing_of_irreducible R K hϖ
  haveI hoi : IsOpenImmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]; exact IsOpenImmersion.of_isLocalization ϖ

  let Ts := {x : T // t.base x = IsLocalRing.closedPoint R}
  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  haveI : QuasiSober Ts := hS.isClosedEmbedding_subtypeVal.quasiSober

  let ι := Option (irreducibleComponents Ts)

  have hZirr : ∀ Z : irreducibleComponents Ts, IsIrreducible (Z.1 : Set Ts) := fun Z => Z.2.1
  have hZcl : ∀ Z : irreducibleComponents Ts, IsClosed (Z.1 : Set Ts) := fun Z =>
    isClosed_of_mem_irreducibleComponents _ Z.2
  let ηZ : irreducibleComponents Ts → Ts := fun Z => (hZirr Z).genericPoint
  have hηZ : ∀ Z, IsGenericPoint (ηZ Z) (Z.1 : Set Ts) := fun Z =>
    (hZirr Z).isGenericPoint_genericPoint (hZcl Z)
  have hgenZ : ∀ Z : irreducibleComponents Ts, ∀ y : T, y ⤳ (ηZ Z).1 →
      t.base y = IsLocalRing.closedPoint R → y = (ηZ Z).1 := by
    intro Z y hy hys
    let y' : Ts := ⟨y, hys⟩
    have hy' : y' ⤳ ηZ Z := Topology.IsInducing.subtypeVal.specializes_iff.mp hy
    have h1 : (Z.1 : Set Ts) ⊆ closure {y'} := by
      rw [← (hηZ Z).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy'))
        isClosed_closure
    have h2 : closure {y'} ⊆ (Z.1 : Set Ts) := Z.2.2 isIrreducible_singleton.closure h1
    have h3 : IsGenericPoint y' (Z.1 : Set Ts) := isGenericPoint_def.mpr (h2.antisymm h1)
    exact congrArg Subtype.val (h3.eq (hηZ Z))
  choose U_ hηU g_ hg_ using fun Z : irreducibleComponents Ts =>
    NeronModelInfra.exists_nhds_extension_of_isProper_of_smooth R K f t uK (ηZ Z).1 (ηZ Z).2 (hgenZ Z)

  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  let ggen : SchemeHomOver (Ugen.ι ≫ t) f :=
    ⟨(Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K), by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% uK.2, ← pullback.condition,
        Scheme.Hom.isoOpensRange_inv_comp_assoc]⟩

  let U : ι → T.Opens := fun i => i.elim Ugen U_
  let g : ∀ i : ι, SchemeHomOver ((U i).ι ≫ t) f := fun i =>
    match i with
    | none => ggen
    | some Z => g_ Z
  let V : T.Opens := ⨆ i, U i

  have hgU : ∀ i, pullback.fst ((U i).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g i).1 =
      pullback.map ((U i).ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) (U i).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K) := by
    intro i
    cases i with
    | none =>
      have hnone : pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫ (Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv =
          pullback.map (Ugen.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) Ugen.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K))]
        simp only [Category.assoc, pullback.map, pullback.lift_fst]
        rw [Scheme.Hom.isoOpensRange_inv_comp]
      show pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫
          ((Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) = _
      rw [reassoc_of% hnone]
      rfl
    | some Z =>
      show pullback.fst ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g_ Z).1 =
        pullback.map ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) (U_ Z).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)
      rw [← genericFibreRestrict_coe_comp_fst (R := R) (K := K) f ((U_ Z).ι ≫ t) (g_ Z), hg_ Z,
        Category.assoc]

  let 𝒰 := Scheme.Opens.iSupOpenCover U
  have hUι : ∀ k, 𝒰.f k ≫ (⨆ i, U i).ι = (U k).ι := fun k => Scheme.homOfLE_ι T (le_iSup U k)
  have hcompat : ∀ i j : ι, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (g i).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (g j).1 := by
    intro i j
    let p : pullback (𝒰.f i) (𝒰.f j) ⟶ Spec (CommRingCat.of R) :=
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι ≫ t
    have h12 : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι := by
      rw [← hUι i, ← hUι j, pullback.condition_assoc]
    have hp₂ : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι ≫ t = p := by
      rw [← reassoc_of% h12]
    have hoi1 : IsOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j)) := inferInstance
    have hsm1 : Smooth (pullback.fst (𝒰.f i) (𝒰.f j)) := inferInstance
    have hsm0 : Smooth (U i).ι := inferInstance
    have hsm2 : Smooth ((U i).ι ≫ t) := MorphismProperty.comp_mem @Smooth _ _ hsm0 inferInstance
    haveI : Smooth p := MorphismProperty.comp_mem @Smooth _ _ hsm1 hsm2
    haveI : Flat p := inferInstance
    let a : SchemeHomOver p f := ⟨pullback.fst _ _ ≫ (g i).1, by
      rw [Category.assoc]; exact congrArg (fun h => pullback.fst (𝒰.f i) (𝒰.f j) ≫ h) (g i).2⟩
    let b : SchemeHomOver p f := ⟨pullback.snd _ _ ≫ (g j).1, by
      rw [Category.assoc]; exact (congrArg (fun h => pullback.snd (𝒰.f i) (𝒰.f j) ≫ h) (g j).2).trans hp₂⟩
    suffices hab : a = b from congrArg Subtype.val hab
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f p
    apply Subtype.ext
    apply pullback.hom_ext
    · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
      have key : ∀ (k : ι) (q : pullback (𝒰.f i) (𝒰.f j) ⟶ (U k).toScheme) (hq : q ≫ (U k).ι ≫ t = p),
          pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (g k).1 =
            pullback.lift (pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (U k).ι) (pullback.snd p (specGenericFibreInclusion R K))
              (by rw [Category.assoc, Category.assoc, hq, pullback.condition]) ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K) := by
        intro k q hq
        have hm : pullback.fst p (specGenericFibreInclusion R K) ≫ q = pullback.map p (specGenericFibreInclusion R K) ((U k).ι ≫ t) (specGenericFibreInclusion R K) q (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id, hq]) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              pullback.fst ((U k).ι ≫ t) (specGenericFibreInclusion R K) := by
          simp only [pullback.map, pullback.lift_fst]
        rw [← Category.assoc (pullback.fst p (specGenericFibreInclusion R K)), hm, Category.assoc, hgU k]
        simp only [← Category.assoc]
        congr 2
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc,
            Category.comp_id]
      change pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ (g i).1 =
        pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ (g j).1
      refine (key i (pullback.fst _ _) rfl).trans ?_
      refine Eq.trans ?_ (key j (pullback.snd _ _) hp₂).symm
      have h12' : pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι =
          pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι := by rw [h12]
      congr 2
    · simp only [genericFibreRestrict_coe_comp_snd]
  let v : V.toScheme ⟶ X := 𝒰.glueMorphisms (fun i => (g i).1) hcompat
  have hv : ∀ i, 𝒰.f i ≫ v = (g i).1 := fun i => 𝒰.ι_glueMorphisms _ _ i
  have hvf : v ≫ f = V.ι ≫ t := by
    apply 𝒰.hom_ext
    intro i
    rw [reassoc_of% (hv i)]
    refine ((g i).2).trans ?_
    change (U i).ι ≫ t = T.homOfLE (le_iSup U i) ≫ (⨆ i, U i).ι ≫ t
    rw [Scheme.homOfLE_ι_assoc]
  refine ⟨V, ⟨v, hvf⟩, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ U none := by
      change x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
      rw [Scheme.Hom.opensRange_pullbackFst]
      change t.base x ∈ (specGenericFibreInclusion R K).opensRange
      rw [Scheme.Hom.mem_opensRange]

      refine ⟨IsLocalRing.closedPoint K, ?_⟩
      apply PrimeSpectrum.ext
      have h1 : ((specGenericFibreInclusion R K).base (IsLocalRing.closedPoint K)).asIdeal = ⊥ := by
        change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
        rw [IsLocalRing.maximalIdeal_eq_bot (R := K), Ideal.comap_bot_of_injective _
          (IsFractionRing.injective R K)]
      have h2 : (t.base x).asIdeal = ⊥ := by
        by_contra hne
        apply hx
        apply PrimeSpectrum.ext
        exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (t.base x).isPrime)
      rw [h1, h2]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, this⟩
  · intro Z hZ
    exact ⟨ηZ ⟨Z, hZ⟩, (hηZ ⟨Z, hZ⟩).mem, TopologicalSpace.Opens.mem_iSup.mpr ⟨some ⟨Z, hZ⟩, hηU ⟨Z, hZ⟩⟩⟩
  · apply pullback.hom_ext
    ·
      simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
      have hrange : Set.range (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base ⊆ Set.range (𝒰.f none).base := by
        rintro _ ⟨z, rfl⟩
        have hz : (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈ Set.range (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base :=
          ⟨z, rfl⟩
        rw [IsOpenImmersion.range_pullbackFst] at hz
        have h1 : Set.range (𝒰.f none).base = ((V.ι ⁻¹ᵁ (U none) : V.toScheme.Opens) : Set V) := by
          change Set.range (T.homOfLE (le_iSup U none)).base = _
          rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
        rw [h1]
        change V.ι.base ((pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z) ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact hz
      let l := IsOpenImmersion.lift (𝒰.f none) (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)) hrange
      have hl : l ≫ 𝒰.f none = pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K) := IsOpenImmersion.lift_fac _ _ _
      have hkey : l ≫ (Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv =
          pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K))]
        simp only [Category.assoc, pullback.map, pullback.lift_fst]
        rw [← hl, Category.assoc]
        congr 1
        simp only [𝒰, Scheme.Opens.iSupOpenCover, V, Scheme.homOfLE_ι]
        exact Scheme.Hom.isoOpensRange_inv_comp _
      rw [← hl, Category.assoc, hv none]
      change l ≫ ((Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) = _
      rw [reassoc_of% hkey]
    · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
      rw [uK.2, pullback.lift_snd, Category.comp_id]

end S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth (solution)

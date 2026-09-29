-- Prove2me | solution 1 for NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb16cd20-b46a-521d-bf45-1ff71fb46f7d

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace GlueModelsGC6

section OpenGenericFibre

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isOpenImmersion_specGenericFibreInclusion : IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine (isLocalization_iff (Submonoid.powers ϖ) K).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      exact isUnit_iff_ne_zero.mpr
        ((IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr (pow_ne_zero n hϖ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨⟨a * ↑v⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have hbK : algebraMap R K b ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hbK, ← map_mul, ← map_mul, hv]
      congr 1
      rw [mul_assoc, ← mul_assoc (↑v⁻¹ : R), Units.inv_mul, one_mul]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective R K h]⟩
  rw [specGenericFibreInclusion_eq]
  exact IsOpenImmersion.of_isLocalization ϖ

end OpenGenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {ι : Type u} [Finite ι] [Nonempty ι]
  (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
  (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)

noncomputable def w (i : ι) : XK ⟶ Y i :=
  haveI := he i
  inv (e i).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite ι] [Nonempty ι] in
include he in
theorem e_w (i : ι) : (e i).1 ≫ w K gK Y f e he i = pullback.fst (f i) (specGenericFibreInclusion R K) := by
  haveI := he i
  rw [w, IsIso.hom_inv_id_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite ι] [Nonempty ι] in
theorem w_f (i : ι) : w K gK Y f e he i ≫ f i = gK ≫ specGenericFibreInclusion R K := by
  haveI := he i
  rw [w, Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq]
  exact (e i).2.symm

scoped instance isOpenImmersion_w (i : ι) : IsOpenImmersion (w K gK Y f e he i) := by
  haveI := he i
  haveI := isOpenImmersion_specGenericFibreInclusion (R := R) K
  dsimp only [w]
  infer_instance

end Main

end GlueModelsGC6
p2m_reactivate "P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift.GlueModelsGC6"

open GlueModelsGC6 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (hdiag : ∀ i j, i ≠ j → ∀ δ : pullback (e i).1 (e j).1 ⟶ pullback (f i) (f j),
      δ ≫ pullback.fst (f i) (f j) = pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K) →
      δ ≫ pullback.snd (f i) (f j) = pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K) →
      IsClosedImmersion δ) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (j : ∀ i, SchemeHomOver (f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g (f i) (j i)).1 ≫ eX.1 = (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by
  classical
  haveI hI : IsOpenImmersion (specGenericFibreInclusion R K) := isOpenImmersion_specGenericFibreInclusion K

  obtain ⟨X, g', hopen, hglue, hcov, hinter, huniv⟩ :=
    AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion XK Y (w K gK Y f e he)
  haveI := hopen

  obtain ⟨g, hg, -⟩ := huniv (Spec (CommRingCat.of R)) f (fun i i' => by rw [w_f, w_f])

  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  let h : XK ⟶ X := w K gK Y f e he a₀ ≫ g' a₀
  have hh : ∀ i, w K gK Y f e he i ≫ g' i = h := fun i => hglue i a₀
  have hhg : h ≫ g = gK ≫ specGenericFibreInclusion R K := by
    simp only [h, Category.assoc, hg, w_f]

  have hrange : Set.range h = Set.range (pullback.fst g (specGenericFibreInclusion R K)) := by
    rw [Scheme.Pullback.range_fst]
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨gK z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hhg]
    · rintro x ⟨t, ht⟩
      have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      have hy : y ∈ Set.range (pullback.fst (f i) (specGenericFibreInclusion R K)) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨t, ?_⟩
        rw [ht, ← Scheme.Hom.comp_apply, hg]
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(e i).1 z, ?_⟩
      rw [← hh i]
      change (g' i) (w K gK Y f e he i ((e i).1 z)) = (g' i) _
      rw [← Scheme.Hom.comp_apply _ (w K gK Y f e he i), e_w]
  let θ := IsOpenImmersion.isoOfRangeEq h (pullback.fst g (specGenericFibreInclusion R K)) hrange
  have hθ : θ.hom ≫ pullback.fst g (specGenericFibreInclusion R K) = h :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hθ2 : θ.hom ≫ pullback.snd g (specGenericFibreInclusion R K) = gK := by
    rw [← cancel_mono (specGenericFibreInclusion R K), Category.assoc, ← pullback.condition,
      ← Category.assoc, hθ, hhg]
  let eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK :=
    ⟨θ.inv, by rw [← hθ2, Iso.inv_hom_id_assoc]⟩

  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι Y g' (fun x => by
    have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, y, rfl⟩)

  have hsm : Smooth g :=
    IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun i => by
      change Smooth (g' i ≫ g); rw [hg]; exact (hf i).1
  have hlft : LocallyOfFiniteType g :=
    IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰 fun i => by
      change LocallyOfFiniteType (g' i ≫ g); rw [hg]; exact (hf i).2.2.1
  have hqc : QuasiCompact g := by
    haveI : CompactSpace ↥X := by
      constructor
      rw [← hcov]
      haveI := Fintype.ofFinite ι
      refine isCompact_iUnion fun i => ?_
      haveI := (hf i).2.2.2
      haveI : CompactSpace ↥(Y i) := QuasiCompact.compactSpace_of_compactSpace (f i)
      exact isCompact_range (g' i).continuous
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have hsep : IsSeparated g := by
    refine ⟨?_⟩
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g)
    rintro ⟨a, b⟩
    change IsClosedImmersion (pullback.snd (pullback.diagonal g)
      (pullback.map (g' a ≫ g) (g' b ≫ g) g g (g' a) (g' b) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))

    have hw' : pullback.fst (g' a) (g' b) ≫ (g' a ≫ g) = pullback.snd (g' a) (g' b) ≫ (g' b ≫ g) := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    let n : pullback (g' a) (g' b) ⟶ pullback (g' a ≫ g) (g' b ≫ g) :=
      pullback.lift (pullback.fst (g' a) (g' b)) (pullback.snd (g' a) (g' b)) hw'
    have hn : pullback.snd (pullback.diagonal g)
        (pullback.map (g' a ≫ g) (g' b ≫ g) g g (g' a) (g' b) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) =
        (pullbackDiagonalMapIdIso (g' a) (g' b) g).hom ≫ n := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullbackDiagonalMapIdIso_hom_fst]
      · rw [Category.assoc, pullback.lift_snd, pullbackDiagonalMapIdIso_hom_snd]
    rw [hn]
    suffices hn' : IsClosedImmersion n by infer_instance
    by_cases hab : a = b
    · subst hab
      have hsepa : IsSeparated (g' a ≫ g) := by rw [hg]; exact (hf a).2.1
      have hn2 : n = pullback.fst (g' a) (g' a) ≫ pullback.diagonal (g' a ≫ g) := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id,
            fst_eq_snd_of_mono_eq]
      rw [hn2]
      infer_instance
    ·
      have hP : IsPullback (w K gK Y f e he a) (w K gK Y f e he b) (g' a) (g' b) := by
        refine (IsOpenImmersion.isPullback (w K gK Y f e he b) (w K gK Y f e he a) (g' b) (g' a)
          (hglue a b) ?_).flip
        ext y
        constructor
        · intro hy
          have hy' : (g' a) y ∈ Set.range (g' a) ∩ Set.range (g' b) := ⟨⟨y, rfl⟩, hy⟩
          rw [hinter a b hab] at hy'
          obtain ⟨z, hz⟩ := hy'
          exact ⟨z, (g' a).isOpenEmbedding.injective (by rwa [← Scheme.Hom.comp_apply])⟩
        · rintro ⟨z, rfl⟩
          show (g' a) ((w K gK Y f e he a) z) ∈ Set.range (g' b)
          have : (g' a) ((w K gK Y f e he a) z) ∈ Set.range (w K gK Y f e he a ≫ g' a) :=
            ⟨z, by rw [Scheme.Hom.comp_apply]⟩
          rw [← hinter a b hab] at this
          exact this.2

      have key : ∀ {fa : Y a ⟶ Spec (CommRingCat.of R)} {fb : Y b ⟶ Spec (CommRingCat.of R)}
          (ha : fa = f a) (hb : fb = f b)
          (hw : w K gK Y f e he a ≫ fa = w K gK Y f e he b ≫ fb),
          IsClosedImmersion (pullback.lift (w K gK Y f e he a) (w K gK Y f e he b) hw : XK ⟶ pullback fa fb) := by
        intro fa fb ha hb hw
        subst ha hb
        haveI := he a
        haveI := he b
        let δ : pullback (e a).1 (e b).1 ⟶ pullback (f a) (f b) :=
          (pullback.fst (e a).1 (e b).1 ≫ (e a).1) ≫ pullback.lift (w K gK Y f e he a) (w K gK Y f e he b) hw
        have hδ : IsClosedImmersion δ := by
          refine hdiag a b hab δ ?_ ?_
          · simp only [δ, Category.assoc, pullback.lift_fst]
            exact congrArg (pullback.fst (e a).1 (e b).1 ≫ ·) (e_w K gK Y f e he a)
          · simp only [δ, Category.assoc, pullback.lift_snd]
            rw [← Category.assoc, pullback.condition, Category.assoc]
            exact congrArg (pullback.snd (e a).1 (e b).1 ≫ ·) (e_w K gK Y f e he b)
        have : pullback.lift (w K gK Y f e he a) (w K gK Y f e he b) hw =
            inv (pullback.fst (e a).1 (e b).1 ≫ (e a).1) ≫ δ := by
          rw [IsIso.eq_inv_comp]
        rw [this]
        infer_instance
      have hm := key (hg a) (hg b)
        (by rw [← Category.assoc, hglue a b, Category.assoc])
      have hn3 : n = hP.isoPullback.inv ≫
          pullback.lift (w K gK Y f e he a) (w K gK Y f e he b)
            (by rw [← Category.assoc, hglue a b, Category.assoc]) := by
        rw [Iso.eq_inv_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
      rw [hn3]
      infer_instance
  refine ⟨X, g, eX, fun i => ⟨g' i, hg i⟩, hsm, hsep, hlft, hqc, inferInstance, fun i => hopen i, fun i => ?_,
    fun x => ?_⟩
  ·
    change (genericFibreRestrict R K g (f i) ⟨g' i, hg i⟩).1 ≫ θ.inv = (e i).1
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hθ, ← hh i, ← Category.assoc, e_w]
    · rw [genericFibreRestrict_coe_comp_snd, Category.assoc, hθ2, (e i).2]
  · have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
    exact Set.mem_iUnion.mp hx

end S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
end P2MW
export P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift (solution)

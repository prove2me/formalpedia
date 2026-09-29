-- Prove2me | solution 1 for NeronModelInfra.exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c691a996-8ee8-52d9-af03-517eb1ab677d

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

namespace P2mRestrictAssoc

section Topo

variable {P : Type*} [TopologicalSpace P]

def DenseIn (S F : Set P) : Prop := F ⊆ closure (S ∩ F)

theorem denseIn_iff_dense_preimage_val (S F : Set P) :
    DenseIn S F ↔ Dense ((Subtype.val : F → P) ⁻¹' S) := by
  rw [DenseIn, Subtype.dense_iff, Subtype.image_preimage_coe, Set.inter_comm]

theorem denseIn_setOf_iff {p : P → Prop} (S : Set P) :
    DenseIn S {q | p q} ↔ Dense ((Subtype.val : {q // p q} → P) ⁻¹' S) :=
  denseIn_iff_dense_preimage_val S {q | p q}

theorem DenseIn.mono {S S' F : Set P} (h : DenseIn S F) (hS : S ⊆ S') : DenseIn S' F :=
  h.trans (closure_mono (Set.inter_subset_inter_left _ hS))

theorem DenseIn.image_iff {W : Type*} [TopologicalSpace W] {φ : W → P} (hφ : IsInducing φ) {F : Set P}
    (hd : DenseIn (Set.range φ) F) (S : Set W) :
    DenseIn (φ '' S) F ↔ DenseIn S (φ ⁻¹' F) := by
  constructor
  · intro h w hw
    rw [hφ.closure_eq_preimage_closure_image, Set.image_inter_preimage]
    exact h hw
  · intro h x hx
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨_, hyO, ⟨w, rfl⟩, hyF⟩ := mem_closure_iff.mp (hd hx) O hO hxO
    obtain ⟨w', hw'O, hw'S, hw'F⟩ :=
      mem_closure_iff.mp (h hyF) (φ ⁻¹' O) (hO.preimage hφ.continuous) hyO
    exact ⟨φ w', hw'O, ⟨w', hw'S, rfl⟩, hw'F⟩

theorem dense_fibre_transfer {W A B : Type*} [TopologicalSpace W] {φ : W → P} (hφ : IsOpenEmbedding φ)
    (pW : W → A) (pP : P → B) (g : A → B) (hg : Function.Injective g)
    (hcomm : ∀ z, pP (φ z) = g (pW z)) {S : Set P} (hS : S ⊆ Set.range φ) {SW : Set W}
    (hSW : SW = φ ⁻¹' S) (a : A)
    (hd : Dense ((Subtype.val : {q // pP q = g a} → P) ⁻¹' S)) :
    Dense ((Subtype.val : {z // pW z = a} → W) ⁻¹' SW) := by
  rw [← denseIn_setOf_iff] at hd ⊢
  have hF : φ ⁻¹' {q | pP q = g a} = {z | pW z = a} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hcomm, hg.eq_iff]
  have hr : DenseIn (Set.range φ) {q | pP q = g a} := hd.mono hS
  have hSe : φ '' (φ ⁻¹' S) = S := Set.image_preimage_eq_of_subset hS
  rw [← hF, hSW]
  exact (DenseIn.image_iff hφ.isInducing hr _).mp (hSe.symm ▸ hd)

end Topo

section GenericPoint

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalization_away {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K where
  map_units := by
    rintro ⟨y, n, rfl⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero))
  surj := by
    intro z
    obtain ⟨⟨a, b, hb⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨⟨a * ↑v⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    simp only at h ⊢
    have hϖn : (ϖ ^ n : R) = b * ↑v⁻¹ := by
      rw [hv, mul_assoc, mul_comm (ϖ ^ n), ← mul_assoc, Units.mul_inv, one_mul]
    rw [hϖn, map_mul, map_mul, ← mul_assoc, h]
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using IsFractionRing.injective R K h⟩

scoped instance isOpenImmersion_specGenericFibreInclusion : IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI := isLocalization_away R K hϖ
  exact IsOpenImmersion.of_isLocalization ϖ

theorem range_specGenericFibreInclusion :
    Set.range (specGenericFibreInclusion R K).base = {q | q ≠ IsLocalRing.closedPoint R} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩ h
    have h1 := congrArg PrimeSpectrum.asIdeal h
    change (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R K)).hom s).asIdeal =
      IsLocalRing.maximalIdeal R at h1
    rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, Ideal.eq_bot_of_prime s.asIdeal,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h1
    exact IsDiscreteValuationRing.not_a_field' (R := R) h1.symm
  · intro hq
    have hbot : q.asIdeal = ⊥ := by
      by_contra hne
      apply hq
      have hmax := Ideal.IsPrime.isMaximal q.isPrime hne
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    change (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R K)).hom ⟨⊥, _⟩).asIdeal = q.asIdeal
    rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, hbot,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

variable {R K}

theorem isDominant_fst_specGenericFibreInclusion {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of R))
    [Smooth g] : IsDominant (pullback.fst g (specGenericFibreInclusion R K)) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  have hopen : IsOpen (g.base '' O) := g.isOpenMap O hO
  let η : ↥(Spec (CommRingCat.of R)) := ⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩
  have hη : η ∈ g.base '' O := by
    have hgz : g.base z ∈ g.base '' O := ⟨z, hz, rfl⟩
    have hsp : η ⤳ g.base z := (PrimeSpectrum.le_iff_specializes η (g.base z)).mp bot_le
    exact hsp.mem_open hopen hgz
  obtain ⟨o, ho, hoη⟩ := hη
  refine ⟨o, ho, ?_⟩
  change g.base o ∈ Set.range (specGenericFibreInclusion R K).base
  rw [hoη, range_specGenericFibreInclusion]
  intro h
  have h1 := congrArg PrimeSpectrum.asIdeal h
  exact IsDiscreteValuationRing.not_a_field' (R := R) h1.symm

end GenericPoint

section Algebra

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

def MulRel {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b τ : SchemeHomOver t f) : Prop :=
  NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t τ) e =
    LXK.mul (pullback.snd t (specGenericFibreInclusion R K))
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t a) e)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t b) e)

variable {K LXK f e}

theorem grj_comp_eq {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {g : A ⟶ B}
    (ψ : SchemeHomOver t' t) (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x = NeronModelInfra.schemeHomOverComp ψ x := rfl

theorem MulRel.comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    {a b τ : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (ψ : SchemeHomOver t' t) :
    MulRel K LXK f e (NeronModelInfra.schemeHomOverComp ψ a) (NeronModelInfra.schemeHomOverComp ψ b)
      (NeronModelInfra.schemeHomOverComp ψ τ) := by
  unfold MulRel at h ⊢
  have h2 := congrArg (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K t t' ψ)) h
  rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp] at h2
  rw [h2, ← grj_comp_eq, LXK.mul_natural, grj_comp_eq, grj_comp_eq, ← schemeHomOverComp_assoc,
    ← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]

theorem comp_e_injective [IsIso e.1] {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of K)}
    {x y : SchemeHomOver s (pullback.snd f (specGenericFibreInclusion R K))}
    (h : NeronModelInfra.schemeHomOverComp x e = NeronModelInfra.schemeHomOverComp y e) : x = y := by
  apply Subtype.ext
  rw [← cancel_mono e.1]
  exact congrArg Subtype.val h

theorem MulRel.gfr_assoc [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b c ab bc abc₁ abc₂ : SchemeHomOver t f}
    (h₁ : MulRel K LXK f e a b ab) (h₂ : MulRel K LXK f e b c bc)
    (h₃ : MulRel K LXK f e ab c abc₁) (h₄ : MulRel K LXK f e a bc abc₂) :
    genericFibreRestrict R K f t abc₁ = genericFibreRestrict R K f t abc₂ := by
  apply comp_e_injective (e := e)
  unfold MulRel at h₁ h₂ h₃ h₄
  rw [h₃, h₄, h₁, h₂, LXK.mul_assoc]

theorem fst_comp_eq_of_gfr_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {x y : SchemeHomOver t f}
    (h : genericFibreRestrict R K f t x = genericFibreRestrict R K f t y) :
    pullback.fst t (specGenericFibreInclusion R K) ≫ x.1 =
      pullback.fst t (specGenericFibreInclusion R K) ≫ y.1 := by
  rw [← genericFibreRestrict_coe_comp_fst, ← genericFibreRestrict_coe_comp_fst, h]

theorem mulRel_iff_display (U : (pullback f f).Opens) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f)
    (c d : SchemeHomOver (pullback.fst f f ≫ f) f) :
    MulRel K LXK f e
      (NeronModelInfra.schemeHomOverComp (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) _) c)
      (NeronModelInfra.schemeHomOverComp (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) _) d) τ ↔
    (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
      pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d) e)).1 := by
  set incl : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f) := ⟨U.ι, rfl⟩
  have hmap : pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
      (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1 :=
    (genericFibreRestrict_coe_eq_pullbackMap _ _ incl _ _).symm
  have key : (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1 ≫
      (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d) e)).1 =
      (LXK.mul (pullback.snd (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl c)) e)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl d)) e)).1 := by
    have h := congrArg Subtype.val (LXK.mul_natural _ _ (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1
      (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).2
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d) e))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [h, grj_comp_eq, grj_comp_eq, ← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc,
      ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]
  rw [hmap, key, MulRel]
  exact Subtype.ext_iff

theorem mulRel_of_display (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (w : SchemeHomOver t (W.ι ≫ pullback.fst f f ≫ f)) (a b τ : SchemeHomOver t f)
    (ha : a.1 = w.1 ≫ W.ι ≫ pullback.fst f f) (hb : b.1 = w.1 ≫ W.ι ≫ pullback.snd f f)
    (hτ : τ.1 = w.1 ≫ m.1) : MulRel K LXK f e a b τ := by
  have relm := ((mulRel_iff_display (K := K) (LXK := LXK) (e := e) W m ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩).mpr hmK).comp w
  have ea : a = NeronModelInfra.schemeHomOverComp w
      (NeronModelInfra.schemeHomOverComp (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) _)
        (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f)) :=
    Subtype.ext (by rw [ha]; rfl)
  have eb : b = NeronModelInfra.schemeHomOverComp w
      (NeronModelInfra.schemeHomOverComp (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) _)
        (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f)) :=
    Subtype.ext (by rw [hb]; rfl)
  have eτ : τ = NeronModelInfra.schemeHomOverComp w m := Subtype.ext (by rw [hτ]; rfl)
  rw [ea, eb, eτ]
  exact relm

end Algebra

section Restrict

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
variable (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)

def jj : pullback (X'.ι ≫ f) (X'.ι ≫ f) ⟶ pullback f f :=
  pullback.map (X'.ι ≫ f) (X'.ι ≫ f) f f X'.ι X'.ι (𝟙 _) (Category.comp_id _) (Category.comp_id _)

@[reassoc (attr := simp)]
theorem jj_fst : jj f X' ≫ pullback.fst f f = pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jj_snd : jj f X' ≫ pullback.snd f f = pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι :=
  pullback.lift_snd _ _ _

scoped instance isOpenImmersion_jj : IsOpenImmersion (jj f X') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := X'.ι ≫ f) (g := X'.ι ≫ f) (f' := f) (g' := f)
    (i₁ := X'.ι) (i₂ := X'.ι) inferInstance inferInstance rfl rfl

theorem range_jj : Set.range (jj f X').base =
    {q | (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X'} := by
  rw [jj, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
  rfl

theorem jj_injective : Function.Injective (jj f X').base := (jj f X').isOpenEmbedding.injective

theorem fst_jj_apply (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) :
    (pullback.fst f f).base ((jj f X').base q) = X'.ι.base ((pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q) := by
  rw [← Scheme.Hom.comp_apply, jj_fst, Scheme.Hom.comp_apply]

theorem snd_jj_apply (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) :
    (pullback.snd f f).base ((jj f X').base q) = X'.ι.base ((pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q) := by
  rw [← Scheme.Hom.comp_apply, jj_snd, Scheme.Hom.comp_apply]

def UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens := jj f X' ⁻¹ᵁ U

theorem mem_UY (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) : q ∈ UY f X' U ↔ (jj f X').base q ∈ U := Iff.rfl

theorem coe_UY : (UY f X' U : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) = (jj f X').base ⁻¹' (U : Set _) := rfl

theorem range_UYι_jj : Set.range ((UY f X' U).ι ≫ jj f X').base ⊆ Set.range U.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact z.2

def w₀ : (UY f X' U : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((UY f X' U).ι ≫ jj f X') (range_UYι_jj f X' U)

@[reassoc (attr := simp)]
theorem w₀_ι : w₀ f X' U ≫ U.ι = (UY f X' U).ι ≫ jj f X' := IsOpenImmersion.lift_fac _ _ _

scoped instance isOpenImmersion_w₀ : IsOpenImmersion (w₀ f X' U) := by
  haveI : IsOpenImmersion (w₀ f X' U ≫ U.ι) := by rw [w₀_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ U.ι

def θ : (UY f X' U : Scheme.{u}) ⟶ (W : Scheme.{u}) := w₀ f X' U ≫ (pullback f f).homOfLE hUW

@[reassoc (attr := simp)]
theorem θ_ι : θ f W X' U hUW ≫ W.ι = (UY f X' U).ι ≫ jj f X' := by
  rw [θ, Category.assoc, Scheme.homOfLE_ι, w₀_ι]

scoped instance isOpenImmersion_θ : IsOpenImmersion (θ f W X' U hUW) := by
  unfold θ; infer_instance

theorem θ_apply_coe (z : ↥(UY f X' U)) :
    ((θ f W X' U hUW).base z).1 = (jj f X').base z.1 := by
  rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, θ_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]

variable (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
  (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')

include hU₂ in
theorem U_subset_range_jj : (U : Set ↑(pullback f f)) ⊆ Set.range (jj f X').base := by
  intro q hq
  rw [range_jj]
  exact ⟨(hU₂ q hq).1, (hU₂ q hq).2.1⟩

include hU₂ in

theorem range_θ : Set.range (θ f W X' U hUW).base = {w | W.ι.base w ∈ U} := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    change W.ι.base ((θ f W X' U hUW).base z) ∈ U
    rw [Scheme.Opens.ι_apply, θ_apply_coe]
    exact z.2
  · intro hw
    obtain ⟨q', hq'⟩ := U_subset_range_jj f W m X' U hUW hU₂ hw
    have hq'U : q' ∈ UY f X' U := by
      change (jj f X').base q' ∈ U
      rw [hq']
      exact hw
    refine ⟨⟨q', hq'U⟩, ?_⟩
    apply Subtype.ext
    rw [θ_apply_coe]
    exact hq'

include hU₂ in
theorem range_θm : Set.range (θ f W X' U hUW ≫ m.1).base ⊆ Set.range X'.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  have hz : (jj f X').base z.1 ∈ U := z.2
  have key := (hU₂ _ hz).2.2
  have hθz : (θ f W X' U hUW).base z = ⟨(jj f X').base z.1, hUW hz⟩ := Subtype.ext (θ_apply_coe f W X' U hUW z)
  rw [hθz]
  exact key

def mY₁ : (UY f X' U : Scheme.{u}) ⟶ (X' : Scheme.{u}) :=
  IsOpenImmersion.lift X'.ι (θ f W X' U hUW ≫ m.1) (range_θm f W m X' U hUW hU₂)

@[reassoc (attr := simp)]
theorem mY₁_ι : mY₁ f W m X' U hUW hU₂ ≫ X'.ι = θ f W X' U hUW ≫ m.1 := IsOpenImmersion.lift_fac _ _ _

theorem mY₁_over : mY₁ f W m X' U hUW hU₂ ≫ (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f) := by
  rw [mY₁_ι_assoc, m.2, θ_ι_assoc, jj_fst_assoc]

def mY : SchemeHomOver ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f) :=
  ⟨mY₁ f W m X' U hUW hU₂, mY₁_over f W m X' U hUW hU₂⟩

theorem mY_coe : (mY f W m X' U hUW hU₂).1 = mY₁ f W m X' U hUW hU₂ := rfl

def PhiY : (UY f X' U : Scheme.{u}) ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) :=
  pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f))
    (mY f W m X' U hUW hU₂).1 ((Category.assoc _ _ _).trans (mY f W m X' U hUW hU₂).2.symm)

def PsiY : (UY f X' U : Scheme.{u}) ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) :=
  pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (mY f W m X' U hUW hU₂).1
    ((UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
    ((mY f W m X' U hUW hU₂).2.trans (by rw [Category.assoc, pullback.condition]))

@[reassoc (attr := simp)]
theorem PhiY_fst : PhiY f W m X' U hUW hU₂ ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem PhiY_snd : PhiY f W m X' U hUW hU₂ ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
    mY₁ f W m X' U hUW hU₂ := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem PsiY_fst : PsiY f W m X' U hUW hU₂ ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
    mY₁ f W m X' U hUW hU₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem PsiY_snd : PsiY f W m X' U hUW hU₂ ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift_snd _ _ _

def Phi : (W : Scheme.{u}) ⟶ pullback f f :=
  pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1 ((Category.assoc _ _ _).trans m.2.symm)

def Psi : (W : Scheme.{u}) ⟶ pullback f f :=
  pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

@[reassoc (attr := simp)]
theorem Phi_fst : Phi f W m ≫ pullback.fst f f = W.ι ≫ pullback.fst f f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Phi_snd : Phi f W m ≫ pullback.snd f f = m.1 := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem Psi_fst : Psi f W m ≫ pullback.fst f f = m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Psi_snd : Psi f W m ≫ pullback.snd f f = W.ι ≫ pullback.snd f f := pullback.lift_snd _ _ _

theorem PhiY_jj : PhiY f W m X' U hUW hU₂ ≫ jj f X' = θ f W X' U hUW ≫ Phi f W m := by
  apply pullback.hom_ext
  · rw [Category.assoc, jj_fst, PhiY_fst_assoc, Category.assoc, Phi_fst, θ_ι_assoc, jj_fst]
  · rw [Category.assoc, jj_snd, PhiY_snd_assoc, mY₁_ι, Category.assoc, Phi_snd]

theorem PsiY_jj : PsiY f W m X' U hUW hU₂ ≫ jj f X' = θ f W X' U hUW ≫ Psi f W m := by
  apply pullback.hom_ext
  · rw [Category.assoc, jj_fst, PsiY_fst_assoc, mY₁_ι, Category.assoc, Psi_fst]
  · rw [Category.assoc, jj_snd, PsiY_snd_assoc, Category.assoc, Psi_snd, θ_ι_assoc, jj_snd]

theorem isOpenImmersion_PhiY (hΦ : IsOpenImmersion (Phi f W m)) : IsOpenImmersion (PhiY f W m X' U hUW hU₂) := by
  haveI : IsOpenImmersion (PhiY f W m X' U hUW hU₂ ≫ jj f X') := by rw [PhiY_jj]; infer_instance
  exact IsOpenImmersion.of_comp _ (jj f X')

theorem isOpenImmersion_PsiY (hΨ : IsOpenImmersion (Psi f W m)) : IsOpenImmersion (PsiY f W m X' U hUW hU₂) := by
  haveI : IsOpenImmersion (PsiY f W m X' U hUW hU₂ ≫ jj f X') := by rw [PsiY_jj]; infer_instance
  exact IsOpenImmersion.of_comp _ (jj f X')

theorem range_comp_base {A B C : Scheme.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Set.range (φ ≫ ψ).base = ψ.base '' Set.range φ.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

include hU₂ in
theorem image_Phi_eq : (Phi f W m).base '' {w | W.ι.base w ∈ U} =
    (jj f X').base '' Set.range (PhiY f W m X' U hUW hU₂).base := by
  rw [← range_θ f W m X' U hUW hU₂, ← range_comp_base, ← range_comp_base, PhiY_jj]

include hU₂ in
theorem image_Psi_eq : (Psi f W m).base '' {w | W.ι.base w ∈ U} =
    (jj f X').base '' Set.range (PsiY f W m X' U hUW hU₂).base := by
  rw [← range_θ f W m X' U hUW hU₂, ← range_comp_base, ← range_comp_base, PsiY_jj]

variable (hU₃ : ∀ x : X, x ∈ X' →
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
        (U : Set ↑(pullback f f))) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
        (U : Set ↑(pullback f f))) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
        ((Phi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
        ((Phi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
        ((Psi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
        ((Psi f W m).base '' {w | W.ι.base w ∈ U})))

theorem X'ι_injective : Function.Injective X'.ι.base := X'.ι.isOpenEmbedding.injective

include hU₂ hU₃ in
theorem dense_UY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' (UY f X' U : Set _)) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f X')
    (U_subset_range_jj f W m X' U hUW hU₂) (coe_UY f X' U) x (hU₃ x.1 x.2).1

include hU₂ hU₃ in
theorem dense_UY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' (UY f X' U : Set _)) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f X')
    (U_subset_range_jj f W m X' U hUW hU₂) (coe_UY f X' U) x (hU₃ x.1 x.2).2.1

theorem range_PhiY_eq : Set.range (PhiY f W m X' U hUW hU₂).base =
    (jj f X').base ⁻¹' ((Phi f W m).base '' {w | W.ι.base w ∈ U}) := by
  rw [image_Phi_eq f W m X' U hUW hU₂, Set.preimage_image_eq _ (jj_injective f X')]

theorem range_PsiY_eq : Set.range (PsiY f W m X' U hUW hU₂).base =
    (jj f X').base ⁻¹' ((Psi f W m).base '' {w | W.ι.base w ∈ U}) := by
  rw [image_Psi_eq f W m X' U hUW hU₂, Set.preimage_image_eq _ (jj_injective f X')]

include hUW hU₂ in
theorem image_Phi_subset : (Phi f W m).base '' {w | W.ι.base w ∈ U} ⊆ Set.range (jj f X').base := by
  rw [image_Phi_eq f W m X' U hUW hU₂]
  exact Set.image_subset_range _ _

include hUW hU₂ in
theorem image_Psi_subset : (Psi f W m).base '' {w | W.ι.base w ∈ U} ⊆ Set.range (jj f X').base := by
  rw [image_Psi_eq f W m X' U hUW hU₂]
  exact Set.image_subset_range _ _

include hU₃ in
theorem dense_PhiY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PhiY f W m X' U hUW hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f X')
    (image_Phi_subset f W m X' U hUW hU₂) (range_PhiY_eq f W m X' U hUW hU₂) x (hU₃ x.1 x.2).2.2.1

include hU₃ in
theorem dense_PhiY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PhiY f W m X' U hUW hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f X')
    (image_Phi_subset f W m X' U hUW hU₂) (range_PhiY_eq f W m X' U hUW hU₂) x (hU₃ x.1 x.2).2.2.2.1

include hU₃ in
theorem dense_PsiY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PsiY f W m X' U hUW hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f X')
    (image_Psi_subset f W m X' U hUW hU₂) (range_PsiY_eq f W m X' U hUW hU₂) x
    (hU₃ x.1 x.2).2.2.2.2.1

include hU₃ in
theorem dense_PsiY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PsiY f W m X' U hUW hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f X')
    (image_Psi_subset f W m X' U hUW hU₂) (range_PsiY_eq f W m X' U hUW hU₂) x
    (hU₃ x.1 x.2).2.2.2.2.2

theorem mem_UY_of_ne_closedPoint [IsLocalRing R]
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)))
    (hq : (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R) :
    q ∈ UY f X' U := by
  change (jj f X').base q ∈ U
  apply hU₁
  have h : (pullback.fst f f ≫ f).base ((jj f X').base q) =
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q := by
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, jj_fst, Category.assoc]
  rw [h]
  exact hq

theorem restrict_clause {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u}))
    (ha : a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f) (hb : b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f) :
    ∃ v : T ⟶ (UY f X' U : Scheme.{u}),
      v ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧
      v ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = b ∧
      v ≫ (mY f W m X' U hUW hU₂).1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1 := by
  have hab : a ≫ (X'.ι ≫ f) = b ≫ (X'.ι ≫ f) := by
    rw [reassoc_of% ha, reassoc_of% hb, pullback.condition]
  let v₀ : T ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift a b hab
  have hv₀ : v₀ ≫ jj f X' = w ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, jj_fst, pullback.lift_fst_assoc, ha, Category.assoc]
    · rw [Category.assoc, jj_snd, pullback.lift_snd_assoc, hb, Category.assoc]
  have hr : Set.range v₀.base ⊆ Set.range (UY f X' U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (jj f X').base (v₀.base x) ∈ U
    rw [← Scheme.Hom.comp_apply, hv₀, Scheme.Hom.comp_apply]
    exact (w.base x).2
  let v : T ⟶ (UY f X' U : Scheme.{u}) := IsOpenImmersion.lift (UY f X' U).ι v₀ hr
  have hv : v ≫ (UY f X' U).ι = v₀ := IsOpenImmersion.lift_fac _ _ _
  have hvw : v ≫ w₀ f X' U = w := by
    rw [← cancel_mono U.ι, Category.assoc, w₀_ι, reassoc_of% hv, hv₀]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [reassoc_of% hv, pullback.lift_fst]
  · rw [reassoc_of% hv, pullback.lift_snd]
  · rw [mY_coe, mY₁_ι, θ, Category.assoc, reassoc_of% hvw]

end Restrict

section AssocFrame

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

abbrev DD : Scheme.{u} := pullback (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

abbrev Q12 : DD y D ⟶ D := pullback.fst (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

abbrev Q23 : DD y D ⟶ D := pullback.snd (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

@[reassoc]
theorem Q12_snd : Q12 y D ≫ D.ι ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem fst_y : pullback.fst y y ≫ y = pullback.snd y y ≫ y :=
  pullback.condition

@[reassoc]
theorem M_y : M.1 ≫ y = D.ι ≫ pullback.fst y y ≫ y := M.2

def mulFst : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ M.1) (Q23 y D ≫ D.ι ≫ pullback.snd y y)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

def mulSnd : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ D.ι ≫ pullback.fst y y) (Q23 y D ≫ M.1)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

@[reassoc (attr := simp)]
theorem mulFst_fst : mulFst y D M ≫ pullback.fst y y = Q12 y D ≫ M.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulFst_snd : mulFst y D M ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.snd y y :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_fst : mulSnd y D M ≫ pullback.fst y y = Q12 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_snd : mulSnd y D M ≫ pullback.snd y y = Q23 y D ≫ M.1 := pullback.lift_snd _ _ _

def A : (DD y D).Opens := mulFst y D M ⁻¹ᵁ D ⊓ mulSnd y D M ⁻¹ᵁ D

theorem mem_A (x : ↑(DD y D)) : x ∈ A y D M ↔ (mulFst y D M).base x ∈ D ∧ (mulSnd y D M).base x ∈ D := by
  simp only [A, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage]

theorem range_A_mulFst : Set.range ((A y D M).ι ≫ mulFst y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact ((mem_A y D M x.1).mp x.2).1

theorem range_A_mulSnd : Set.range ((A y D M).ι ≫ mulSnd y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  exact ((mem_A y D M x.1).mp x.2).2

def dF : (A y D M : Scheme.{u}) ⟶ D :=
  IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulFst y D M) (range_A_mulFst y D M)

def dG : (A y D M : Scheme.{u}) ⟶ D :=
  IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulSnd y D M) (range_A_mulSnd y D M)

@[reassoc (attr := simp)]
theorem dF_ι : dF y D M ≫ D.ι = (A y D M).ι ≫ mulFst y D M := IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem dG_ι : dG y D M ≫ D.ι = (A y D M).ι ≫ mulSnd y D M := IsOpenImmersion.lift_fac _ _ _

def FF : (A y D M : Scheme.{u}) ⟶ Y := dF y D M ≫ M.1

def GG : (A y D M : Scheme.{u}) ⟶ Y := dG y D M ≫ M.1

def tA : (A y D M : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  (A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y

scoped instance smooth_tA [Smooth y] : Smooth (tA y D M) := by
  unfold tA; infer_instance

theorem FF_y : FF y D M ≫ y = tA y D M := by
  simp only [FF, tA, Category.assoc, M_y, dF_ι_assoc, mulFst_fst_assoc]

theorem GG_y : GG y D M ≫ y = tA y D M := by
  simp only [GG, tA, Category.assoc, M_y, dG_ι_assoc, mulSnd_fst_assoc]

theorem assoc_of_FF_eq_GG (hFG : FF y D M = GG y D M)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y))
    (h₁ : u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y)
    (h₂ : p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1)
    (h₃ : p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y)
    (h₄ : q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y)
    (h₅ : q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1) :
    p.1 ≫ M.1 = q.1 ≫ M.1 := by

  let τ₀ : T ⟶ DD y D := pullback.lift u.1 v.1 h₁
  have hF : τ₀ ≫ mulFst y D M = p.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulFst_fst, pullback.lift_fst_assoc, Category.assoc, h₂]
    · rw [Category.assoc, mulFst_snd, pullback.lift_snd_assoc, Category.assoc, h₃]
  have hG : τ₀ ≫ mulSnd y D M = q.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulSnd_fst, pullback.lift_fst_assoc, Category.assoc, h₄]
    · rw [Category.assoc, mulSnd_snd, pullback.lift_snd_assoc, Category.assoc, h₅]
  have hr : Set.range τ₀.base ⊆ Set.range (A y D M).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine (mem_A y D M _).mpr ⟨?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hF, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (p.1.base x).2
    · rw [← Scheme.Hom.comp_apply, hG, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (q.1.base x).2
  let τ : T ⟶ A y D M := IsOpenImmersion.lift (A y D M).ι τ₀ hr
  have hτ : τ ≫ (A y D M).ι = τ₀ := IsOpenImmersion.lift_fac _ _ _
  have hp : p.1 = τ ≫ dF y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dF_ι, reassoc_of% hτ, hF]
  have hq : q.1 = τ ≫ dG y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dG_ι, reassoc_of% hτ, hG]
  have key := congrArg (fun φ => τ ≫ φ) hFG
  simp only [FF, GG] at key
  rw [hp, hq, Category.assoc, Category.assoc]
  exact key

end AssocFrame

section Assoc

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Smooth f] [IsSeparated f]
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
variable (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
variable (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
variable (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
  (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth f] [IsSeparated f] [IsIso e.1] in
include hmK in

theorem mulRel_UY {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (z : T ⟶ (UY f X' U : Scheme.{u})) (a b τ : SchemeHomOver t f)
    (ha : a.1 = z ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι)
    (hb : b.1 = z ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι)
    (hτ : τ.1 = z ≫ (mY f W m X' U hUW hU₂).1 ≫ X'.ι) : MulRel K LXK f e a b τ := by
  have hw : (z ≫ θ f W X' U hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t := by
    rw [← a.2, ha]
    simp only [Category.assoc, θ_ι_assoc, jj_fst_assoc]
  refine mulRel_of_display W m hmK ⟨z ≫ θ f W X' U hUW, hw⟩ a b τ ?_ ?_ ?_
  · rw [ha, Category.assoc, θ_ι_assoc, jj_fst]
  · rw [hb, Category.assoc, θ_ι_assoc, jj_snd]
  · rw [hτ, mY_coe, mY₁_ι, Category.assoc]

include hmK in

theorem FF_eq_GG :
    FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) = GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) := by
  haveI : IsReduced (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂))
  haveI : IsDominant (pullback.fst (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂))
      (specGenericFibreInclusion R K)) :=
    isDominant_fst_specGenericFibreInclusion _
  refine ext_of_isDominant_of_isSeparated (X'.ι ≫ f) ?_
    (pullback.fst (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) (specGenericFibreInclusion R K)) ?_
  · rw [FF_y, GG_y]

  let t : (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
    tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)
  have ht : t = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι ≫ f := rfl
  let a : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X' U).ι ≫
      pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by simp only [Category.assoc, ht]⟩
  have ha : a.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let b : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X' U).ι ≫
      pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [← fst_y (X'.ι ≫ f)]⟩
  have hb : b.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let c : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X' U).ι ≫
      pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [← fst_y (X'.ι ≫ f), ← Q12_snd_assoc (X'.ι ≫ f) (UY f X' U), ← fst_y (X'.ι ≫ f)]⟩
  have hc : c.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫
      (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let ab : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [M_y (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)]⟩
  have hab : ab.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι := rfl
  let bc : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [M_y (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂), ← Q12_snd_assoc (X'.ι ≫ f) (UY f X' U),
          ← fst_y (X'.ι ≫ f)]⟩
  have hbc : bc.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι := rfl
  let abc₁ : SchemeHomOver t f :=
    ⟨FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι, by rw [Category.assoc, FF_y]⟩
  have habc₁ : abc₁.1 = FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι := rfl
  let abc₂ : SchemeHomOver t f :=
    ⟨GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι, by rw [Category.assoc, GG_y]⟩
  have habc₂ : abc₂.1 = GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι := rfl

  have r₁ : MulRel K LXK f e a b ab :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂
      ((A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U)) a b ab
      (by rw [ha, Category.assoc]) (by rw [hb, Category.assoc]) (by rw [hab, Category.assoc])
  have r₂ : MulRel K LXK f e b c bc :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂
      ((A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U)) b c bc
      (by rw [hb, Category.assoc, Q12_snd_assoc]) (by rw [hc, Category.assoc]) (by rw [hbc, Category.assoc])
  have r₃ : MulRel K LXK f e ab c abc₁ :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂ (dF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) ab c abc₁
      (by rw [hab, dF_ι_assoc, mulFst_fst_assoc]) (by rw [hc, dF_ι_assoc, mulFst_snd_assoc])
      (by rw [habc₁, FF, Category.assoc])
  have r₄ : MulRel K LXK f e a bc abc₂ :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂ (dG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) a bc abc₂
      (by rw [ha, dG_ι_assoc, mulSnd_fst_assoc]) (by rw [hbc, dG_ι_assoc, mulSnd_snd_assoc])
      (by rw [habc₂, GG, Category.assoc])
  have key := fst_comp_eq_of_gfr_eq (MulRel.gfr_assoc r₁ r₂ r₃ r₄)
  rw [habc₁, habc₂] at key
  rw [← cancel_mono X'.ι, Category.assoc, Category.assoc]
  exact key

include hmK in

theorem hassocY {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)))
    (h₁ : u.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
      v.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f))
    (h₂ : p.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ (mY f W m X' U hUW hU₂).1)
    (h₃ : p.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
      v.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
    (h₄ : q.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
      u.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f))
    (h₅ : q.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ (mY f W m X' U hUW hU₂).1) :
    p.1 ≫ (mY f W m X' U hUW hU₂).1 = q.1 ≫ (mY f W m X' U hUW hU₂).1 :=
  assoc_of_FF_eq_GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)
    (FF_eq_GG K LXK f e W m hmK X' U hUW hU₂) t u v p q h₁ h₂ h₃ h₄ h₅

end Assoc

end P2mRestrictAssoc
p2m_reactivate "P2MW.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw.P2mRestrictAssoc"

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw.P2mRestrictAssoc"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :
    ∃ (UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens)
      (mY : SchemeHomOver (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f))),
        u.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        p.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ mY.1 →
        p.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ mY.1 →
        p.1 ≫ mY.1 = q.1 ≫ mY.1) ∧
      (∀ q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)),
        (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R → q ∈ UY) ∧
      (∀ {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u})),
        a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f → b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f →
        ∃ v : T ⟶ (UY : Scheme.{u}),
          v ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧ v ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = b ∧
          v ≫ mY.1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1) := by
  refine ⟨P2mRestrictAssoc.UY f X' U, P2mRestrictAssoc.mY f W m X' U hUW hU₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun x => P2mRestrictAssoc.dense_UY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => P2mRestrictAssoc.dense_UY_snd f W m X' U hUW hU₂ hU₃ x
  · exact P2mRestrictAssoc.isOpenImmersion_PhiY f W m X' U hUW hU₂ hΦ
  · exact fun x => P2mRestrictAssoc.dense_PhiY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => P2mRestrictAssoc.dense_PhiY_snd f W m X' U hUW hU₂ hU₃ x
  · exact P2mRestrictAssoc.isOpenImmersion_PsiY f W m X' U hUW hU₂ hΨ
  · exact fun x => P2mRestrictAssoc.dense_PsiY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => P2mRestrictAssoc.dense_PsiY_snd f W m X' U hUW hU₂ hU₃ x
  · intro T t u v p q h₁ h₂ h₃ h₄ h₅
    exact P2mRestrictAssoc.hassocY K LXK f e W m hmK X' U hUW hU₂ t u v p q h₁ h₂ h₃ h₄ h₅
  · exact fun q hq => P2mRestrictAssoc.mem_UY_of_ne_closedPoint f X' U hU₁ q hq
  · intro T w a b ha hb
    exact P2mRestrictAssoc.restrict_clause f W m X' U hUW hU₂ w a b ha hb

end S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
end P2MW
export P2MW.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw (solution)

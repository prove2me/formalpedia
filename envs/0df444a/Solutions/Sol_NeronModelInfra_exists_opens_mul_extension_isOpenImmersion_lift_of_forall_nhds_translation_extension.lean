-- Prove2me | solution 1 for NeronModelInfra.exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/08607e31-883a-5d34-9219-7506b5b654e0

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mBirLaw

section MaxPtsOuter

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section MaxPts

variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))

def IsMaxSp (x : P) : Prop :=
  p.base x = IsLocalRing.closedPoint R ∧
    ∀ y : P, y ⤳ x → p.base y = IsLocalRing.closedPoint R → y = x

def spFib : Set P := {x | p.base x = IsLocalRing.closedPoint R}

theorem isClosed_spFib : IsClosed (spFib p) :=
  (IsLocalRing.isClosed_singleton_closedPoint R).preimage p.base.hom.continuous

theorem IsMaxSp.isGenericPoint {x : P} (hx : IsMaxSp p x) {Z : Set P} (hZ : IsIrreducible Z)
    (hZs : Z ⊆ spFib p) (hxZ : x ∈ Z) : IsGenericPoint x (closure Z) := by
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.closure isClosed_closure
  have hζx : ζ ⤳ x := hζ.specializes (subset_closure hxZ)
  have hζs : p.base ζ = IsLocalRing.closedPoint R := by
    have : ζ ∈ closure Z := hζ.mem
    exact (closure_minimal hZs (isClosed_spFib p)) this
  rwa [← hx.2 ζ hζx hζs]

theorem image_subset_spFib (Z : Set {x : P // p.base x = IsLocalRing.closedPoint R}) :
    Subtype.val '' Z ⊆ spFib p := by
  rintro _ ⟨z, -, rfl⟩; exact z.2

open Classical in

theorem finite_isMaxSp [IsLocallyNoetherian P] [CompactSpace P] : {x : P | IsMaxSp p x}.Finite := by
  haveI : IsNoetherian P := {}
  haveI : TopologicalSpace.NoetherianSpace {x : P // p.base x = IsLocalRing.closedPoint R} :=
    TopologicalSpace.NoetherianSpace.set (spFib p)
  let c : P → Set {x : P // p.base x = IsLocalRing.closedPoint R} := fun x =>
    if hx : p.base x = IsLocalRing.closedPoint R then
      irreducibleComponent (⟨x, hx⟩ : {x : P // p.base x = IsLocalRing.closedPoint R}) else ∅
  refine Set.Finite.of_finite_image (f := c) ?_ ?_
  · refine (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      (α := {x : P // p.base x = IsLocalRing.closedPoint R})).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [c, dif_pos hx.1]
    exact irreducibleComponent_mem_irreducibleComponents _
  · intro x hx y hy hxy
    have hx' : IsMaxSp p x := hx
    have hy' : IsMaxSp p y := hy
    simp only [c, dif_pos hx'.1, dif_pos hy'.1] at hxy
    have h1 := hx'.isGenericPoint p
      ((irreducibleComponent_mem_irreducibleComponents
        (⟨x, hx'.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
        continuous_subtype_val.continuousOn) (image_subset_spFib p _) ⟨_, mem_irreducibleComponent, rfl⟩
    have h2 := hy'.isGenericPoint p
      ((irreducibleComponent_mem_irreducibleComponents
        (⟨y, hy'.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
        continuous_subtype_val.continuousOn) (image_subset_spFib p _) ⟨_, mem_irreducibleComponent, rfl⟩
    rw [hxy] at h1
    exact h1.eq h2

theorem IsMaxSp.mem_of_forall_irreducibleComponents {x : P} (hx : IsMaxSp p x) (V : P.Opens)
    (hV : ∀ Z ∈ irreducibleComponents {x : P // p.base x = IsLocalRing.closedPoint R}, ∃ y ∈ Z, y.1 ∈ V) :
    x ∈ V := by
  obtain ⟨y, hyZ, hyV⟩ := hV _ (irreducibleComponent_mem_irreducibleComponents
    (⟨x, hx.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R}))
  have hgen := hx.isGenericPoint p
    ((irreducibleComponent_mem_irreducibleComponents
      (⟨x, hx.1⟩ : {x : P // p.base x = IsLocalRing.closedPoint R})).1.image _
      continuous_subtype_val.continuousOn)
    (image_subset_spFib p _) ⟨_, mem_irreducibleComponent, rfl⟩
  have hxy : x ⤳ y.1 := hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩)
  exact hxy.mem_open V.2 hyV

variable {p}

theorem isMaxSp_comp_iff {W : Scheme.{u}} (i : W ⟶ P) [IsOpenImmersion i] (x : W) :
    IsMaxSp (i ≫ p) x ↔ IsMaxSp p (i.base x) := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨by simpa using hx, fun y hy hys => ?_⟩
    have hyr : y ∈ Set.range i.base := hy.mem_open i.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hyr
    rw [hmax y ((i.isOpenEmbedding.isInducing.specializes_iff).mp hy) (by simpa using hys)]
  · rintro ⟨hx, hmax⟩
    refine ⟨by simpa using hx, fun y hy hys => ?_⟩
    apply i.isOpenEmbedding.injective
    exact hmax _ (hy.map i.base.hom.continuous) (by simpa using hys)

theorem IsMaxSp.of_opens {U : P.Opens} {x : U} (hx : IsMaxSp (U.ι ≫ p) x) : IsMaxSp p x.1 :=
  (isMaxSp_comp_iff U.ι x).mp hx

theorem IsMaxSp.to_opens (U : P.Opens) {x : P} (hx : IsMaxSp p x) (hxU : x ∈ U) :
    IsMaxSp (U.ι ≫ p) ⟨x, hxU⟩ :=
  (isMaxSp_comp_iff U.ι ⟨x, hxU⟩).mpr hx

end MaxPts

end MaxPtsOuter

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
    have hϖn : (ϖ ^ n : R) = b * ↑v⁻¹ := by rw [hv, mul_assoc, mul_comm (ϖ ^ n), ← mul_assoc, Units.mul_inv, one_mul]
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
    change (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R K)).hom s).asIdeal = IsLocalRing.maximalIdeal R at h1
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
    rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, hbot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

variable {R K}

theorem range_fst_specGenericFibreInclusion {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) :
    Set.range (pullback.fst p (specGenericFibreInclusion R K)).base = {x | p.base x ≠ IsLocalRing.closedPoint R} := by
  rw [Scheme.Pullback.range_fst, range_specGenericFibreInclusion]
  rfl

theorem base_ne_closedPoint {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (x : S) :
    (s ≫ specGenericFibreInclusion R K).base x ≠ IsLocalRing.closedPoint R := by
  have : (specGenericFibreInclusion R K).base (s.base x) ∈ Set.range (specGenericFibreInclusion R K).base :=
    ⟨_, rfl⟩
  rw [range_specGenericFibreInclusion] at this
  simp at this
  exact this

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

theorem MulRel.gfr_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {a b τ τ' : SchemeHomOver t f}
    (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a b τ') :
    genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ' :=
  comp_e_injective (h.trans h'.symm)

theorem MulRel.gfr_snd_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b τ a' b' τ' : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a' b' τ')
    (hτ : genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ')
    (ha : genericFibreRestrict R K f t a = genericFibreRestrict R K f t a') :
    genericFibreRestrict R K f t b = genericFibreRestrict R K f t b' := by
  unfold MulRel at h h'
  rw [hτ, ha, h'] at h
  letI := LXK.pointGroup (pullback.snd t (specGenericFibreInclusion R K))
  exact comp_e_injective (mul_left_cancel h).symm

theorem MulRel.gfr_fst_eq [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b τ a' b' τ' : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (h' : MulRel K LXK f e a' b' τ')
    (hτ : genericFibreRestrict R K f t τ = genericFibreRestrict R K f t τ')
    (hb : genericFibreRestrict R K f t b = genericFibreRestrict R K f t b') :
    genericFibreRestrict R K f t a = genericFibreRestrict R K f t a' := by
  unfold MulRel at h h'
  rw [hτ, hb, h'] at h
  letI := LXK.pointGroup (pullback.snd t (specGenericFibreInclusion R K))
  exact comp_e_injective (mul_right_cancel h).symm

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
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl c)) e)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl d)) e)).1 := by
    have h := congrArg Subtype.val (LXK.mul_natural _ _ (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1
      (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).2
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d) e))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [h, grj_comp_eq, grj_comp_eq, ← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc,
      ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]
  rw [hmap, key, MulRel]
  exact Subtype.ext_iff

end Algebra

section Shear

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

abbrev prj₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩

abbrev prj₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩

def fstK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp z (genericFibreRestrict R K f _ (prj₁ f))

def sndK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp z (genericFibreRestrict R K f _ (prj₂ f))

noncomputable def pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift
      (pullback.lift (a.1 ≫ pullback.fst f _) (b.1 ≫ pullback.fst f _)
        (by simp only [Category.assoc, pullback.condition, reassoc_of% a.2, reassoc_of% b.2]))
      t (by rw [pullback.lift_fst_assoc, Category.assoc, pullback.condition, reassoc_of% a.2]),
    pullback.lift_snd _ _ _⟩

variable {K f}

theorem fstK_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    (fstK K f z).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      z.1 ≫ pullback.fst _ (specGenericFibreInclusion R K) ≫ pullback.fst f f := by
  simp only [fstK, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, genericFibreRestrict_coe_comp_fst]

theorem sndK_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    (sndK K f z).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      z.1 ≫ pullback.fst _ (specGenericFibreInclusion R K) ≫ pullback.snd f f := by
  simp only [sndK, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, genericFibreRestrict_coe_comp_fst]

theorem extK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {z z' : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))}
    (h1 : fstK K f z = fstK K f z') (h2 : sndK K f z = sndK K f z') : z = z' := by
  apply Subtype.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, fstK_coe] using congrArg (fun w => w.1 ≫ pullback.fst f _) h1
    · simpa only [Category.assoc, sndK_coe] using congrArg (fun w => w.1 ≫ pullback.fst f _) h2
  · rw [z.2, z'.2]

@[scoped simp] theorem fstK_pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : fstK K f (pairK K f a b) = a := by
  apply Subtype.ext; apply pullback.hom_ext
  · rw [fstK_coe]; simp only [pairK, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [(fstK K f _).2, a.2]

@[scoped simp] theorem sndK_pairK {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a b : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : sndK K f (pairK K f a b) = b := by
  apply Subtype.ext; apply pullback.hom_ext
  · rw [sndK_coe]; simp only [pairK, pullback.lift_fst_assoc, pullback.lift_snd]
  · rw [(sndK K f _).2, b.2]

theorem fstK_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t)
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    fstK K f (NeronModelInfra.schemeHomOverComp ψ z) = NeronModelInfra.schemeHomOverComp ψ (fstK K f z) :=
  schemeHomOverComp_assoc _ _ _

theorem sndK_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t)
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    sndK K f (NeronModelInfra.schemeHomOverComp ψ z) = NeronModelInfra.schemeHomOverComp ψ (sndK K f z) :=
  schemeHomOverComp_assoc _ _ _

theorem fstK_id :
    fstK K f (schemeHomOverId (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) =
      genericFibreRestrict R K f _ (prj₁ f) := schemeHomOverComp_id_left _

theorem sndK_id :
    sndK K f (schemeHomOverId (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) =
      genericFibreRestrict R K f _ (prj₂ f) := schemeHomOverComp_id_left _

theorem inv_natural {S : Type u} [CommRing S] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S g) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  exact (inv_eq_of_mul_eq_one_left h).symm

variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
variable (K f)

noncomputable def eInv : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨inv e.1, by rw [IsIso.inv_comp_eq, e.2]⟩

omit [IsIso e.1] in

abbrev rd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) : SchemeHomOver t gK :=
  NeronModelInfra.schemeHomOverComp a e

omit [IsIso e.1] in
theorem rd_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t) (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    rd K f e (NeronModelInfra.schemeHomOverComp ψ a) = NeronModelInfra.schemeHomOverComp ψ (rd K f e a) :=
  schemeHomOverComp_assoc _ _ _

@[scoped simp] theorem rd_comp_eInv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t gK) :
    rd K f e (NeronModelInfra.schemeHomOverComp x (eInv K f e)) = x := by
  have h : NeronModelInfra.schemeHomOverComp (eInv K f e) e = schemeHomOverId gK :=
    Subtype.ext (IsIso.inv_hom_id e.1)
  rw [rd, schemeHomOverComp_assoc, h, schemeHomOverComp_id_right]

@[scoped simp] theorem rd_comp_eInv' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp (rd K f e a) (eInv K f e) = a := by
  have h : NeronModelInfra.schemeHomOverComp e (eInv K f e) = schemeHomOverId _ :=
    Subtype.ext (IsIso.hom_inv_id e.1)
  rw [rd, schemeHomOverComp_assoc, h, schemeHomOverComp_id_right]

def shL : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f (genericFibreRestrict R K f _ (prj₁ f))
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
      (eInv K f e))

def shL' : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f (genericFibreRestrict R K f _ (prj₁ f))
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))))
        (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
      (eInv K f e))

def shR : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
      (eInv K f e))
    (genericFibreRestrict R K f _ (prj₂ f))

def shR' : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)) :=
  pairK K f
    (NeronModelInfra.schemeHomOverComp
      (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f)))
        (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₂ f)))))
      (eInv K f e))
    (genericFibreRestrict R K f _ (prj₂ f))

omit [IsIso e.1] in

theorem grj_rd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (ψ : SchemeHomOver t' t) (a : SchemeHomOver t (pullback.snd f (specGenericFibreInclusion R K))) :
    GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 (rd K f e a) = rd K f e (NeronModelInfra.schemeHomOverComp ψ a) :=
  (rd_comp K f e ψ a).symm

section GroupIdentities

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S g)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a b : SchemeHomOver t g)

theorem inv_mul_mul : G.mul t (G.inv t a) (G.mul t a b) = b := by
  rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul]

theorem mul_inv_mul : G.mul t a (G.mul t (G.inv t a) b) = b := by
  rw [← G.mul_assoc, G.mul_inv_cancel, G.one_mul]

theorem mul_mul_inv : G.mul t (G.mul t a b) (G.inv t b) = a := by
  rw [G.mul_assoc, G.mul_inv_cancel, G.mul_one]

theorem mul_inv_mul' : G.mul t (G.mul t a (G.inv t b)) b = a := by
  rw [G.mul_assoc, G.inv_mul_cancel, G.mul_one]

end GroupIdentities

theorem fstK_shL : fstK K f (shL K f LXK e) = genericFibreRestrict R K f _ (prj₁ f) := fstK_pairK _ _
theorem sndK_shL : sndK K f (shL K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
    (eInv K f e) := sndK_pairK _ _
theorem fstK_shL' : fstK K f (shL' K f LXK e) = genericFibreRestrict R K f _ (prj₁ f) := fstK_pairK _ _
theorem sndK_shL' : sndK K f (shL' K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f)))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
    (eInv K f e) := sndK_pairK _ _
theorem fstK_shR : fstK K f (shR K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
    (eInv K f e) := fstK_pairK _ _
theorem sndK_shR : sndK K f (shR K f LXK e) = genericFibreRestrict R K f _ (prj₂ f) := sndK_pairK _ _
theorem fstK_shR' : fstK K f (shR' K f LXK e) = NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (LXK.inv _ (rd K f e (genericFibreRestrict R K f _ (prj₂ f)))))
    (eInv K f e) := fstK_pairK _ _
theorem sndK_shR' : sndK K f (shR' K f LXK e) = genericFibreRestrict R K f _ (prj₂ f) := sndK_pairK _ _

omit [IsIso e.1] in

theorem rd_fstK_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    GoodReductionJacobian.schemeHomOverComp z.1 z.2 (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) =
      rd K f e (fstK K f z) := grj_rd K f e z _

omit [IsIso e.1] in
theorem rd_sndK_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (z : SchemeHomOver t (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) :
    GoodReductionJacobian.schemeHomOverComp z.1 z.2 (rd K f e (genericFibreRestrict R K f _ (prj₂ f))) =
      rd K f e (sndK K f z) := grj_rd K f e z _

theorem shL_comp_shL' : NeronModelInfra.schemeHomOverComp (shL K f LXK e) (shL' K f LXK e) = schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_shL', fstK_id]; exact fstK_shL K f LXK e
  · rw [sndK_comp, sndK_id, sndK_shL', ← schemeHomOverComp_assoc, ← grj_comp_eq (shL K f LXK e) (LXK.mul _ _ _),
      LXK.mul_natural, inv_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shL, sndK_shL, rd_comp_eInv,
      inv_mul_mul, rd_comp_eInv']

theorem shL'_comp_shL : NeronModelInfra.schemeHomOverComp (shL' K f LXK e) (shL K f LXK e) = schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_shL, fstK_id]; exact fstK_shL' K f LXK e
  · rw [sndK_comp, sndK_id, sndK_shL, ← schemeHomOverComp_assoc, ← grj_comp_eq (shL' K f LXK e) (LXK.mul _ _ _),
      LXK.mul_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shL', sndK_shL', rd_comp_eInv,
      mul_inv_mul, rd_comp_eInv']

theorem shR_comp_shR' : NeronModelInfra.schemeHomOverComp (shR K f LXK e) (shR' K f LXK e) = schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_id, fstK_shR', ← schemeHomOverComp_assoc, ← grj_comp_eq (shR K f LXK e) (LXK.mul _ _ _),
      LXK.mul_natural, inv_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shR, sndK_shR, rd_comp_eInv,
      mul_mul_inv, rd_comp_eInv']
  · rw [sndK_comp, sndK_shR', sndK_id]; exact sndK_shR K f LXK e

theorem shR'_comp_shR : NeronModelInfra.schemeHomOverComp (shR' K f LXK e) (shR K f LXK e) = schemeHomOverId _ := by
  apply extK
  · rw [fstK_comp, fstK_id, fstK_shR, ← schemeHomOverComp_assoc, ← grj_comp_eq (shR' K f LXK e) (LXK.mul _ _ _),
      LXK.mul_natural,
      rd_fstK_comp, rd_sndK_comp, fstK_shR', sndK_shR', rd_comp_eInv,
      mul_inv_mul', rd_comp_eInv']
  · rw [sndK_comp, sndK_shR, sndK_id]; exact sndK_shR' K f LXK e

scoped instance isIso_shL : IsIso (shL K f LXK e).1 :=
  ⟨(shL' K f LXK e).1, congrArg Subtype.val (shL_comp_shL' K f LXK e), congrArg Subtype.val (shL'_comp_shL K f LXK e)⟩

scoped instance isIso_shR : IsIso (shR K f LXK e).1 :=
  ⟨(shR' K f LXK e).1, congrArg Subtype.val (shR_comp_shR' K f LXK e), congrArg Subtype.val (shR'_comp_shR K f LXK e)⟩

end Shear

section Pieces

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

abbrev incl (U : (pullback f f).Opens) : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f) :=
  ⟨U.ι, rfl⟩

def muK [IsIso e.1] : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
    (pullback.snd f (specGenericFibreInclusion R K)) :=
  NeronModelInfra.schemeHomOverComp
    (LXK.mul _ (rd K f e (genericFibreRestrict R K f _ (prj₁ f))) (rd K f e (genericFibreRestrict R K f _ (prj₂ f))))
    (eInv K f e)

variable {K LXK f e}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem mulRel_iff_eq_comp_muK [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (w : SchemeHomOver t (pullback.fst f f ≫ f)) (τ : SchemeHomOver t f) :
    MulRel K LXK f e (NeronModelInfra.schemeHomOverComp w (prj₁ f)) (NeronModelInfra.schemeHomOverComp w (prj₂ f)) τ ↔
      genericFibreRestrict R K f t τ =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ t w) (muK K LXK f e) := by
  have key : NeronModelInfra.schemeHomOverComp
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ t w) (muK K LXK f e)) e =
      LXK.mul _ (rd K f e (genericFibreRestrict R K f t (NeronModelInfra.schemeHomOverComp w (prj₁ f))))
        (rd K f e (genericFibreRestrict R K f t (NeronModelInfra.schemeHomOverComp w (prj₂ f)))) := by
    rw [muK, ← schemeHomOverComp_assoc, ← grj_comp_eq _ (LXK.mul _ _ _), LXK.mul_natural, grj_rd, grj_rd,
      ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]
    exact rd_comp_eInv K f e _
  constructor
  · intro h
    apply comp_e_injective (e := e)
    rw [key]; exact h
  · intro h
    unfold MulRel
    rw [h, key]

variable [IsIso e.1]

omit [IsDiscreteValuationRing R] in

theorem restrict_eq_restrict [IsSeparated f] [Flat f] {U U₁ U₂ : (pullback f f).Opens} (h₁ : U ≤ U₁) (h₂ : U ≤ U₂)
    (τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst f f ≫ f) f) (τ₂ : SchemeHomOver (U₂.ι ≫ pullback.fst f f ≫ f) f)
    (r₁ : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U₁) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f U₁) (prj₂ f)) τ₁)
    (r₂ : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U₂) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f U₂) (prj₂ f)) τ₂) :
    (pullback f f).homOfLE h₁ ≫ τ₁.1 = (pullback f f).homOfLE h₂ ≫ τ₂.1 := by
  let l₁ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (U₁.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE h₁, by rw [Scheme.homOfLE_ι_assoc]⟩
  let l₂ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (U₂.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE h₂, by rw [Scheme.homOfLE_ι_assoc]⟩
  have e₁ : NeronModelInfra.schemeHomOverComp l₁ (incl f U₁) = incl f U := Subtype.ext ((pullback f f).homOfLE_ι h₁)
  have e₂ : NeronModelInfra.schemeHomOverComp l₂ (incl f U₂) = incl f U := Subtype.ext ((pullback f f).homOfLE_ι h₂)
  have r₁' := r₁.comp l₁
  have r₂' := r₂.comp l₂
  rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₁] at r₁'
  rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₂] at r₂'
  have h := NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f
    (U.ι ≫ pullback.fst f f ≫ f) (r₁'.gfr_eq r₂')
  exact congrArg Subtype.val h

omit [IsFractionRing R K] [IsIso e.1] in

theorem exists_sigma_of_right
    (hR : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f)) τ)
    (η : ↑(pullback f f)) (hη : IsMaxSp (pullback.fst f f ≫ f) η) :
    ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (σ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
      IsOpenImmersion (pullback.lift (f := f) (g := f) σ.1 (U.ι ≫ pullback.snd f f)
        (σ.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f))
        (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f)) σ := by
  let s : pullback f f ⟶ pullback f f := (pullbackSymmetry f f).hom
  have hs : s ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  have hsη : IsMaxSp (pullback.fst f f ≫ f) (s.base η) := by
    rw [← isMaxSp_comp_iff s η, hs]; exact hη
  obtain ⟨U', hηU', τ', oi', rel'⟩ := hR _ hsη
  refine ⟨s ⁻¹ᵁ U', hηU', ?_⟩
  let ψ : SchemeHomOver ((s ⁻¹ᵁ U').ι ≫ pullback.fst f f ≫ f) (U'.ι ≫ pullback.fst f f ≫ f) :=
    ⟨s ∣_ U', by rw [morphismRestrict_ι_assoc, hs]⟩
  refine ⟨NeronModelInfra.schemeHomOverComp ψ τ', ?_, ?_⟩
  · have heq : pullback.lift (f := f) (g := f) (NeronModelInfra.schemeHomOverComp ψ τ').1
        ((s ⁻¹ᵁ U').ι ≫ pullback.snd f f)
        ((NeronModelInfra.schemeHomOverComp ψ τ').2.trans (by rw [Category.assoc, pullback.condition])) =
        (s ∣_ U') ≫ pullback.lift (f := f) (g := f) (U'.ι ≫ pullback.fst f f) τ'.1
          ((Category.assoc _ _ _).trans τ'.2.symm) ≫ s := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd]
        rfl
      · rw [pullback.lift_snd, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd,
          pullback.lift_fst, morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_fst]
    rw [heq]
    infer_instance
  · have h1 : NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp (incl f U') (prj₂ f)) =
        NeronModelInfra.schemeHomOverComp (incl f (s ⁻¹ᵁ U')) (prj₁ f) := by
      apply Subtype.ext
      change (s ∣_ U') ≫ U'.ι ≫ pullback.snd f f = (s ⁻¹ᵁ U').ι ≫ pullback.fst f f
      rw [morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_snd]
    have h2 : NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp (incl f U') (prj₁ f)) =
        NeronModelInfra.schemeHomOverComp (incl f (s ⁻¹ᵁ U')) (prj₂ f) := by
      apply Subtype.ext
      change (s ∣_ U') ≫ U'.ι ≫ pullback.fst f f = (s ⁻¹ᵁ U').ι ≫ pullback.snd f f
      rw [morphismRestrict_ι_assoc, pullbackSymmetry_hom_comp_fst]
    have r := rel'.comp ψ
    rw [h1, h2] at r
    exact r

omit [IsDomain R] [IsDiscreteValuationRing R] [IsIso e.1] in

theorem injective_of_local {Y : Scheme.{u}} (Φ' : Y ⟶ pullback f f)
    (hcov : ∀ y : Y, ∃ (U : Scheme.{u}) (i : U ⟶ Y) (_ : IsOpenImmersion i), y ∈ i.opensRange ∧ IsOpenImmersion (i ≫ Φ'))
    (hagree : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ Y), b ≫ Φ' = O.ι → b' ≫ Φ' = O.ι → b = b') :
    Function.Injective Φ'.base := by
  intro y y' hyy'
  obtain ⟨U, i, hi, ⟨u, rfl⟩, hio⟩ := hcov y
  obtain ⟨U', i', hi', ⟨u', rfl⟩, hio'⟩ := hcov y'
  let O : (pullback f f).Opens := (i ≫ Φ').opensRange ⊓ (i' ≫ Φ').opensRange
  have hO : Set.range O.ι.base ⊆ Set.range (i ≫ Φ').base := by
    rw [Scheme.Opens.range_ι]; exact fun _ hx => hx.1
  have hO' : Set.range O.ι.base ⊆ Set.range (i' ≫ Φ').base := by
    rw [Scheme.Opens.range_ι]; exact fun _ hx => hx.2
  let b : (O : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift (i ≫ Φ') O.ι hO ≫ i
  let b' : (O : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift (i' ≫ Φ') O.ι hO' ≫ i'
  have hb : b ≫ Φ' = O.ι := by rw [Category.assoc, IsOpenImmersion.lift_fac]
  have hb' : b' ≫ Φ' = O.ι := by rw [Category.assoc, IsOpenImmersion.lift_fac]
  have hbb' := hagree O b b' hb hb'
  have hq : Φ'.base (i.base u) ∈ O := ⟨⟨u, rfl⟩, ⟨u', by simpa using hyy'.symm⟩⟩
  have h1 : b.base ⟨_, hq⟩ = i.base u := by
    change i.base ((IsOpenImmersion.lift (i ≫ Φ') O.ι hO).base ⟨_, hq⟩) = i.base u
    congr 1
    apply (i ≫ Φ').isOpenEmbedding.injective
    change ((IsOpenImmersion.lift (i ≫ Φ') O.ι hO) ≫ i ≫ Φ').base _ = _
    rw [IsOpenImmersion.lift_fac]
    rfl
  have h2 : b'.base ⟨_, hq⟩ = i'.base u' := by
    change i'.base ((IsOpenImmersion.lift (i' ≫ Φ') O.ι hO').base ⟨_, hq⟩) = i'.base u'
    congr 1
    apply (i' ≫ Φ').isOpenEmbedding.injective
    change ((IsOpenImmersion.lift (i' ≫ Φ') O.ι hO') ≫ i' ≫ Φ').base _ = _
    rw [IsOpenImmersion.lift_fac]
    exact hyy'
  rw [← h1, ← h2, hbb']

omit [IsIso e.1] in

theorem maximal_mem_range [IsLocallyNoetherian (pullback f f)] [CompactSpace ↑(pullback f f)]
    (W : (pullback f f).Opens) (Φ' : (W : Scheme.{u}) ⟶ pullback f f)
    [IsOpenImmersion Φ'] (hover : Φ' ≫ pullback.fst f f ≫ f = W.ι ≫ pullback.fst f f ≫ f)
    (hW : ∀ x, IsMaxSp (pullback.fst f f ≫ f) x → x ∈ W)
    (y : ↑(pullback f f)) (hy : IsMaxSp (pullback.fst f f ≫ f) y) : y ∈ Set.range Φ'.base := by
  haveI : Finite {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} :=
    (finite_isMaxSp (pullback.fst f f ≫ f)).to_subtype
  let g : {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} →
      {x : ↑(pullback f f) // IsMaxSp (pullback.fst f f ≫ f) x} := fun x =>
    ⟨Φ'.base ⟨x.1, hW x.1 x.2⟩, by
      rw [← isMaxSp_comp_iff Φ', hover, isMaxSp_comp_iff W.ι]
      exact x.2⟩
  have hg : Function.Injective g := by
    intro x x' h
    have h' := Φ'.isOpenEmbedding.injective (congrArg Subtype.val h)
    have h'' := Subtype.ext_iff.mp h'
    exact Subtype.ext h''
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hg ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val hx⟩

end Pieces

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem main
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) := by
  haveI : IsLocallyNoetherian (pullback f f) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  haveI : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)

  have hL' : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f)) τ := by
    intro η hη
    obtain ⟨U, hηU, τ, oi, hτ⟩ := hL η hη.1 hη.2
    exact ⟨U, hηU, τ, oi, (mulRel_iff_display U τ (prj₁ f) (prj₂ f)).mpr hτ⟩
  have hR' : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f U) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f U) (prj₁ f)) τ := by
    intro η hη
    obtain ⟨U, hηU, τ, oi, hτ⟩ := hR η hη.1 hη.2
    exact ⟨U, hηU, τ, oi, (mulRel_iff_display U τ (prj₂ f) (prj₁ f)).mpr hτ⟩
  have hσ := exists_sigma_of_right hR'

  have hloc : ∀ η : ↑(pullback f f), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) g).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K) (pullback.fst f f ≫ f)
            (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ (muK K LXK f e).1 := by
    intro η h1 h2
    obtain ⟨U, hηU, τ, -, rel⟩ := hL' η ⟨h1, h2⟩
    refine ⟨U, hηU, τ, ?_⟩
    rw [(mulRel_iff_eq_comp_muK (incl f U) τ).mp rel, NeronModelInfra.schemeHomOverComp_coe,
      genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f U) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)]
  obtain ⟨V, v, hV₁, hV₂, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_forall_nhds_extension R K f (pullback.fst f f ≫ f) (muK K LXK f e)
      hloc
  have relv : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f V) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f V) (prj₂ f)) v := by
    rw [mulRel_iff_eq_comp_muK]
    apply Subtype.ext
    rw [hvK, NeronModelInfra.schemeHomOverComp_coe, genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f V)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)]
  have hVmax : ∀ x, IsMaxSp (pullback.fst f f ≫ f) x → x ∈ V := fun x hx =>
    hx.mem_of_forall_irreducibleComponents _ V hV₂

  choose UL hUL τL oiL relL using hL'
  choose UR hUR σR oiR relR using hσ

  let jP := pullback.fst (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let Wη : ∀ η : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) η → (pullback f f).Opens :=
    fun η h => V ⊓ UL η h ⊓ UR η h
  let W : (pullback f f).Opens :=
    (V ⊓ jP.opensRange) ⊔ ⨆ (η : ↑(pullback f f)) (h : IsMaxSp (pullback.fst f f ≫ f) η), Wη η h
  have hWV : W ≤ V := sup_le inf_le_left (iSup₂_le fun η h => inf_le_left.trans inf_le_left)
  have hWηW : ∀ η h, Wη η h ≤ W := fun η h =>
    (le_iSup₂ (f := fun η (h : IsMaxSp (pullback.fst f f ≫ f) η) => Wη η h) η h).trans le_sup_right
  have hWηL : ∀ η h, Wη η h ≤ UL η h := fun η h => inf_le_left.trans inf_le_right
  have hWηR : ∀ η h, Wη η h ≤ UR η h := fun η h => inf_le_right
  let lWV : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) (V.ι ≫ pullback.fst f f ≫ f) :=
    ⟨(pullback f f).homOfLE hWV, by rw [Scheme.homOfLE_ι_assoc]⟩
  let m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f := NeronModelInfra.schemeHomOverComp lWV v
  have relm : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f W) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f W) (prj₂ f)) m := by
    have h := relv.comp lWV
    have e₁ : NeronModelInfra.schemeHomOverComp lWV (incl f V) = incl f W :=
      Subtype.ext ((pullback f f).homOfLE_ι hWV)
    rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, e₁] at h
    exact h
  have hW₁ : ∀ x : ↑(pullback f f), (pullback.fst f f ≫ f).base x ≠ IsLocalRing.closedPoint R → x ∈ W := by
    intro x hx
    apply TopologicalSpace.Opens.mem_sup.mpr
    left
    have hx' : x ∈ Set.range jP.base := by rw [range_fst_specGenericFibreInclusion]; exact hx
    exact TopologicalSpace.Opens.mem_inf.mpr ⟨hV₁ x hx, hx'⟩
  have hW₂ : ∀ x : ↑(pullback f f), IsMaxSp (pullback.fst f f ≫ f) x → x ∈ W := fun x hx =>
    hWηW x hx (TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hVmax x hx, hUL x hx⟩, hUR x hx⟩)

  let Φ := pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1 ((Category.assoc _ _ _).trans m.2.symm)
  let Ψ := pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))
  have hΦloc : ∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Φ) := by
    intro η h
    have heq : (pullback f f).homOfLE (hWηW η h) ≫ Φ =
        (pullback f f).homOfLE (hWηL η h) ≫ pullback.lift (f := f) (g := f) ((UL η h).ι ≫ pullback.fst f f)
          (τL η h).1 ((Category.assoc _ _ _).trans (τL η h).2.symm) := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, Scheme.homOfLE_ι_assoc,
          Scheme.homOfLE_ι_assoc]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
        exact restrict_eq_restrict (hWηW η h) (hWηL η h) m (τL η h) relm (relL η h)
    rw [heq]
    haveI := oiL η h
    infer_instance
  have hΨloc : ∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Ψ) := by
    intro η h
    have heq : (pullback f f).homOfLE (hWηW η h) ≫ Ψ =
        (pullback f f).homOfLE (hWηR η h) ≫ pullback.lift (f := f) (g := f) (σR η h).1
          ((UR η h).ι ≫ pullback.snd f f) ((σR η h).2.trans (by rw [Category.assoc, pullback.condition])) := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact restrict_eq_restrict (hWηW η h) (hWηR η h) m (σR η h) relm (relR η h)
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, Scheme.homOfLE_ι_assoc,
          Scheme.homOfLE_ι_assoc]
    rw [heq]
    haveI := oiR η h
    infer_instance

  let jW := pullback.fst (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  haveI hgfW : IsOpenImmersion (genericFibreRestrict R K _ _ (incl f W)).1 := by
    rw [genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f W) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion W.ι))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) rfl (Category.id_comp _).symm
  have hgm : genericFibreRestrict R K f _ m =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ _ (incl f W)) (muK K LXK f e) :=
    (mulRel_iff_eq_comp_muK (incl f W) m).mp relm
  have hjWm : jW ≫ m.1 = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (muK K LXK f e).1 ≫
      pullback.fst f (specGenericFibreInclusion R K) := by
    rw [← genericFibreRestrict_coe_comp_fst f _ m, hgm, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  have hjWι : jW ≫ W.ι = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ jP :=
    (genericFibreRestrict_coe_comp_fst _ _ (incl f W)).symm
  have hΦgen : jW ≫ Φ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shL K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shL,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shL, hjWm]
      rfl
  have hΨgen : jW ≫ Ψ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ (shR K f LXK e).1 ≫ jP := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, ← fstK_coe, fstK_shR, hjWm]
      rfl
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, ← sndK_coe, sndK_shR,
        genericFibreRestrict_coe_comp_fst, reassoc_of% hjWι]
  have hΦgen' : IsOpenImmersion (jW ≫ Φ) := by rw [hΦgen]; infer_instance
  have hΨgen' : IsOpenImmersion (jW ≫ Ψ) := by rw [hΨgen]; infer_instance

  have hcov : ∀ (Θ : (W : Scheme.{u}) ⟶ pullback f f), IsOpenImmersion (jW ≫ Θ) →
      (∀ η h, IsOpenImmersion ((pullback f f).homOfLE (hWηW η h) ≫ Θ)) →
      ∀ y : ↑W, ∃ (U : Scheme.{u}) (i : U ⟶ W) (_ : IsOpenImmersion i), y ∈ i.opensRange ∧
        IsOpenImmersion (i ≫ Θ) := by
    intro Θ hgen hloc' y
    rcases TopologicalSpace.Opens.mem_sup.mp y.2 with hy | hy
    · refine ⟨_, jW, inferInstance, ?_, hgen⟩
      change y ∈ Set.range jW.base
      rw [range_fst_specGenericFibreInclusion]
      have hy2 : y.1 ∈ Set.range jP.base := (TopologicalSpace.Opens.mem_inf.mp hy).2
      rw [range_fst_specGenericFibreInclusion] at hy2
      exact hy2
    · obtain ⟨η, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      obtain ⟨hη, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      refine ⟨_, (pullback f f).homOfLE (hWηW η hη), inferInstance, ?_, hloc' η hη⟩
      exact ⟨⟨y.1, hy⟩, by rw [Scheme.homOfLE_apply']; exact Subtype.ext rfl⟩

  have hagreeΦ : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ W), b ≫ Φ = O.ι → b' ≫ Φ = O.ι →
      b = b' := by
    intro O b b' hb hb'
    have hbf : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Φ = O.ι → (b ≫ W.ι) ≫ pullback.fst f f = O.ι ≫ pullback.fst f f :=
      fun {b} hb => by rw [← hb, Category.assoc, Category.assoc, pullback.lift_fst]
    have hbm : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Φ = O.ι → b ≫ m.1 = O.ι ≫ pullback.snd f f :=
      fun {b} hb => by rw [← hb, Category.assoc, pullback.lift_snd]
    have key : ∀ (b : (O : Scheme.{u}) ⟶ W) (hb : b ≫ Φ = O.ι),
        MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (⟨b ≫ W.ι, by rw [Category.assoc, reassoc_of% (hbf hb)]⟩ :
            SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f)) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f)) := by
      intro b hb
      let bO : SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) :=
        ⟨b, by rw [reassoc_of% (hbf hb)]⟩
      have h := relm.comp bO
      have e₁ : NeronModelInfra.schemeHomOverComp bO (NeronModelInfra.schemeHomOverComp (incl f W) (prj₁ f)) =
          NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f) := Subtype.ext (by simpa using hbf hb)
      have e₂ : NeronModelInfra.schemeHomOverComp bO m = NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f) :=
        Subtype.ext (hbm hb)
      rw [e₁, e₂, ← schemeHomOverComp_assoc] at h
      exact h
    have hτ := (key b hb).gfr_snd_eq (key b' hb') rfl rfl
    have h2 := congrArg Subtype.val
      (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f (O.ι ≫ pullback.fst f f ≫ f) hτ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h2
    rw [← cancel_mono W.ι]
    apply pullback.hom_ext
    · rw [hbf hb, hbf hb']
    · simpa only [Category.assoc] using h2
  have hagreeΨ : ∀ (O : (pullback f f).Opens) (b b' : (O : Scheme.{u}) ⟶ W), b ≫ Ψ = O.ι → b' ≫ Ψ = O.ι →
      b = b' := by
    intro O b b' hb hb'
    have hbs : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι → (b ≫ W.ι) ≫ pullback.snd f f = O.ι ≫ pullback.snd f f :=
      fun {b} hb => by rw [← hb, Category.assoc, Category.assoc, pullback.lift_snd]
    have hbm : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι → b ≫ m.1 = O.ι ≫ pullback.fst f f :=
      fun {b} hb => by rw [← hb, Category.assoc, pullback.lift_fst]
    have hover : ∀ {b : (O : Scheme.{u}) ⟶ W}, b ≫ Ψ = O.ι →
        (b ≫ W.ι) ≫ pullback.fst f f ≫ f = O.ι ≫ pullback.fst f f ≫ f := fun {b} hb => by
      rw [pullback.condition, Category.assoc, reassoc_of% (hbs hb)]
    have key : ∀ (b : (O : Scheme.{u}) ⟶ W) (hb : b ≫ Ψ = O.ι),
        MulRel K LXK f e
          (NeronModelInfra.schemeHomOverComp (⟨b ≫ W.ι, hover hb⟩ :
            SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f)) (prj₁ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f))
          (NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f)) := by
      intro b hb
      let bO : SchemeHomOver (O.ι ≫ pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) :=
        ⟨b, by rw [← Category.assoc]; exact hover hb⟩
      have h := relm.comp bO
      have e₁ : NeronModelInfra.schemeHomOverComp bO (NeronModelInfra.schemeHomOverComp (incl f W) (prj₂ f)) =
          NeronModelInfra.schemeHomOverComp (incl f O) (prj₂ f) := Subtype.ext (by simpa using hbs hb)
      have e₂ : NeronModelInfra.schemeHomOverComp bO m = NeronModelInfra.schemeHomOverComp (incl f O) (prj₁ f) :=
        Subtype.ext (hbm hb)
      rw [e₁, e₂, ← schemeHomOverComp_assoc] at h
      exact h
    have hτ := (key b hb).gfr_fst_eq (key b' hb') rfl rfl
    have h2 := congrArg Subtype.val
      (NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f (O.ι ≫ pullback.fst f f ≫ f) hτ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h2
    rw [← cancel_mono W.ι]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · rw [hbs hb, hbs hb']

  have hΦ : IsOpenImmersion Φ :=
    IsOpenImmersion.of_forall_source_exists Φ (injective_of_local Φ (hcov Φ hΦgen' hΦloc) hagreeΦ)
      (hcov Φ hΦgen' hΦloc)
  have hΨ : IsOpenImmersion Ψ :=
    IsOpenImmersion.of_forall_source_exists Ψ (injective_of_local Ψ (hcov Ψ hΨgen' hΨloc) hagreeΨ)
      (hcov Ψ hΨgen' hΨloc)
  refine ⟨W, m, hW₁, fun x h1 h2 => hW₂ x ⟨h1, h2⟩, (mulRel_iff_display W m (prj₁ f) (prj₂ f)).mp relm, hΦ,
    fun y h1 h2 => ?_, hΨ, fun y h1 h2 => ?_⟩
  · exact maximal_mem_range W Φ (by rw [pullback.lift_fst_assoc, Category.assoc]) hW₂ y ⟨h1, h2⟩
  · exact maximal_mem_range W Ψ (by rw [pullback.lift_fst_assoc, m.2]) hW₂ y ⟨h1, h2⟩

end Main

end P2mBirLaw
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension.P2mBirLaw"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :=
  P2mBirLaw.main K LXK f e hL hR

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension.P2mBirLaw"

end S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension (solution)

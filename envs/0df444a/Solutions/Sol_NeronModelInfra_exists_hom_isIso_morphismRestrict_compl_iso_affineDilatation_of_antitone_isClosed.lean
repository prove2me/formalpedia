-- Prove2me | solution 1 for NeronModelInfra.exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2be0779f-aab1-5a59-af7b-11ecd7eb8532

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_RingTheory_AffineDilatation
import Theorems.Thm_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
import Theorems.Thm_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NeronModelInfra

universe u

noncomputable section

namespace P2mStrataGlue

section SeparatedCriterion

variable {X₁ X : Scheme.{u}} (v : X₁ ⟶ X) (𝒲 : X₁.OpenCover)

abbrev sqMap (i : 𝒲.I₀) : pullback (𝒲.f i ≫ v) (𝒲.f i ≫ v) ⟶ pullback v v :=
  pullback.map _ _ _ _ (𝒲.f i) (𝒲.f i) (𝟙 X) (Category.comp_id _) (Category.comp_id _)

scoped instance (i : 𝒲.I₀) : IsOpenImmersion (sqMap v 𝒲 i) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

theorem isSeparated_of_openCover [∀ i, IsSeparated (𝒲.f i ≫ v)]
    (h : ∀ z₁ z₂ : X₁, v z₁ = v z₂ → ∃ i, z₁ ∈ Set.range (𝒲.f i) ∧ z₂ ∈ Set.range (𝒲.f i)) :
    IsSeparated v := by
  have hcov : ⨆ i, (sqMap v 𝒲 i).opensRange = ⊤ := by
    rw [← top_le_iff]
    rintro z -
    obtain ⟨i, h₁, h₂⟩ := h (pullback.fst v v z) (pullback.snd v v z)
      (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    change z ∈ ((sqMap v 𝒲 i).opensRange : Set _)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map]
    exact ⟨h₁, h₂⟩
  have key : ∀ i, IsClosedImmersion (pullback.diagonal v ∣_ (sqMap v 𝒲 i).opensRange) := by
    intro i
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictOpensRange _ _)]
    have H := pullback_map_diagonal_isPullback (𝒲.f i) (𝒲.f i) v
    have e : pullback.snd (pullback.diagonal v) (sqMap v 𝒲 i) = H.isoPullback.inv ≫
        pullback.map _ _ _ _ (𝟙 _) (𝟙 _) v (Category.id_comp _).symm (Category.id_comp _).symm := by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
    rw [e, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
    haveI : IsIso (pullback.diagonal (𝒲.f i)) := (pullback.isIso_diagonal_iff _).mpr inferInstance
    have e2 : pullback.map _ _ _ _ (𝟙 _) (𝟙 _) v (Category.id_comp (𝒲.f i ≫ v)).symm
        (Category.id_comp (𝒲.f i ≫ v)).symm =
        inv (pullback.diagonal (𝒲.f i)) ≫ pullback.diagonal (𝒲.f i ≫ v) := by
      rw [IsIso.eq_inv_comp]
      ext <;> simp
    rw [e2, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
    exact IsSeparated.isClosedImmersion_diagonal
  exact ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov key⟩

end SeparatedCriterion

section Restrict

variable {X₁ X : Scheme.{u}} (v : X₁ ⟶ X)

theorem isIso_morphismRestrict_of_le {U W : X.Opens} (hW : IsIso (v ∣_ W)) (h : U ≤ W) : IsIso (v ∣_ U) := by
  have hUeq : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  have h1 : (MorphismProperty.isomorphisms Scheme.{u}) ((v ∣_ W) ∣_ (W.ι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme.{u}) hW _
  rwa [(MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ hUeq)] at h1

theorem isIso_pullback_snd_of_range_subset {T : Scheme.{u}} (k : T ⟶ X) (W : X.Opens) (hW : IsIso (v ∣_ W))
    (hk : ∀ t : T, k t ∈ W) : IsIso (pullback.snd v k) := by
  have hr : Set.range k ⊆ Set.range W.ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]; exact hk t
  let g := IsOpenImmersion.lift W.ι k hr
  have hg : g ≫ W.ι = k := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso (pullback.snd v W.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]; infer_instance
  have : ∀ (k' : T ⟶ X), k' = g ≫ W.ι → IsIso (pullback.snd v k') := by
    rintro k' rfl
    have e : pullback.snd v (g ≫ W.ι) =
        (pullbackLeftPullbackSndIso v W.ι g).inv ≫ pullback.snd (pullback.snd v W.ι) g := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [e]
    infer_instance
  exact this k hg.symm

theorem isIso_pullback_map {S T : Scheme.{u}} (f : X ⟶ S) (ι : T ⟶ S) (W : X.Opens) (hW : IsIso (v ∣_ W))
    (hι : ∀ t : ↥(pullback f ι), pullback.fst f ι t ∈ W) :
    IsIso (pullback.map (v ≫ f) ι f ι v (𝟙 T) (𝟙 S) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  haveI := isIso_pullback_snd_of_range_subset v (pullback.fst f ι) W hW hι
  have e : pullback.map (v ≫ f) ι f ι v (𝟙 T) (𝟙 S) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (pullbackRightPullbackFstIso f ι v).inv ≫ pullback.snd v (pullback.fst f ι) := by
    apply pullback.hom_ext
    · simp [pullbackRightPullbackFstIso_inv_snd_fst]
    · simp [pullbackRightPullbackFstIso_inv_snd_snd]
  rw [e]
  infer_instance

theorem isIso_of_isOpenImmersion_of_surjective {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g]
    (h : Function.Surjective g) : IsIso g := by
  haveI : Epi g.base := (TopCat.epi_iff_surjective _).mpr h
  exact (isIso_iff_isOpenImmersion_and_epi_base g).mpr ⟨inferInstance, inferInstance⟩

theorem isIso_ι_morphismRestrict (U W : X.Opens) (h : W ≤ U) : IsIso (U.ι ∣_ W) := by
  refine isIso_of_isOpenImmersion_of_surjective _ ?_
  rintro ⟨x, hx⟩
  refine ⟨⟨⟨x, h hx⟩, show U.ι ⟨x, h hx⟩ ∈ W from hx⟩, Subtype.ext ?_⟩
  rw [morphismRestrict_base_coe]
  rfl

theorem isIso_morphismRestrict_of_comp {Q : Scheme.{u}} (j : Q ⟶ X₁) [IsOpenImmersion j] (w : Q ⟶ X)
    (hw : j ≫ v = w) (W : X.Opens) (hW : IsIso (w ∣_ W)) (hcov : ∀ z : X₁, v z ∈ W → z ∈ Set.range j) :
    IsIso (v ∣_ W) := by
  subst hw
  let e := IsOpenImmersion.isoOfRangeEq (v ⁻¹ᵁ W).ι (((j ≫ v) ⁻¹ᵁ W).ι ≫ j) (by
    rw [Scheme.Opens.range_ι]
    ext z
    constructor
    · intro hz
      obtain ⟨q, rfl⟩ := hcov z hz
      exact ⟨⟨q, show (j ≫ v) q ∈ W by rwa [Scheme.Hom.comp_apply]⟩,
        by rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]⟩
    · rintro ⟨q, rfl⟩
      have hq : (j ≫ v) q.1 ∈ W := q.2
      rw [Scheme.Hom.comp_apply] at hq
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact hq)
  have he : e.hom ≫ ((j ≫ v) ⁻¹ᵁ W).ι ≫ j = (v ⁻¹ᵁ W).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : v ∣_ W = e.hom ≫ ((j ≫ v) ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, ← Category.assoc _ j v,
      ← Category.assoc e.hom, ← Category.assoc e.hom, Category.assoc e.hom, he]
  rw [this]
  infer_instance

end Restrict

section Points

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem algebraMap_injective {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (h : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R') :
    Function.Injective (algebraMap R R') := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  have hprime : (RingHom.ker (algebraMap R R')).IsPrime := RingHom.ker_isPrime _
  have hne' : RingHom.ker (algebraMap R R') ≠ ⊥ := fun h0 => hne (by
    have : r ∈ RingHom.ker (algebraMap R R') := hr
    rw [h0] at this; exact this)
  have hmax := hprime.isMaximal hne'
  have heq : RingHom.ker (algebraMap R R') = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  have : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = ⊥ := by
    rw [← heq, Ideal.map_eq_bot_iff_le_ker]
  rw [this] at h
  exact IsDiscreteValuationRing.not_a_field R' h.symm

theorem specMap_apply_ne_closedPoint {R' : Type u} [CommRing R'] (g : R →+* R')
    (hinj : Function.Injective g) (q : PrimeSpectrum R') (hq : q.asIdeal = ⊥) :
    (Spec.map (CommRingCat.ofHom g)) q ≠ IsLocalRing.closedPoint R := by
  intro h
  have h' := congrArg PrimeSpectrum.asIdeal h
  rw [Spec.map_apply] at h'
  change Ideal.comap g q.asIdeal = IsLocalRing.maximalIdeal R at h'
  rw [hq, Ideal.comap_bot_of_injective _ hinj] at h'
  exact IsDiscreteValuationRing.not_a_field R h'.symm

theorem range_subset_of_apply_closedPoint_mem {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    {W : X.Opens} (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x (IsLocalRing.closedPoint R') ∈ W) : Set.range x ⊆ Set.range W.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact ((IsLocalRing.specializes_closedPoint t).map x.continuous).mem_open W.isOpen hx

end Points

section Dictionary

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem primeIdealOf_fromSpec (q : PrimeSpectrum Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, hq⟩ = q := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem fromSpec_mem (q : PrimeSpectrum Γ(X, U)) : hU.fromSpec q ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩

theorem mem_iff_vanishingIdeal_le (Z : Set X) (hZ : IsClosed Z) (y : X) (hy : y ∈ U) :
    y ∈ Z ↔ PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Z}) ≤
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have hset : (fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Z} = hU.fromSpec ⁻¹' Z := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      change hU.fromSpec (hU.primeIdealOf y) ∈ Z
      rw [IsAffineOpen.fromSpec_primeIdealOf]; exact hy
    · intro hq
      exact ⟨⟨hU.fromSpec q, fromSpec_mem hU q⟩, hq, primeIdealOf_fromSpec hU q _⟩
  rw [hset, ← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hc : IsClosed (hU.fromSpec ⁻¹' Z) := hZ.preimage hU.fromSpec.continuous
  erw [hc.closure_eq, Set.mem_preimage]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ Z
  rw [IsAffineOpen.fromSpec_primeIdealOf]

end Dictionary

section Setup

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

def XK : X.Opens :=
  f ⁻¹ᵁ ⟨{IsLocalRing.closedPoint R}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩

theorem mem_XK {x : X} : x ∈ XK f ↔ f x ≠ IsLocalRing.closedPoint R := Iff.rfl

variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i))

def C (m : ℕ) : X.Opens := ⟨(Y m)ᶜ, (hY m).isOpen_compl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_C {m : ℕ} {x : X} : x ∈ C Y hY m ↔ x ∉ Y m := Iff.rfl

theorem XK_le_C (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R) (m : ℕ) : XK f ≤ C Y hY m :=
  fun x hx hxY => hx (hYs m x hxY)

abbrev idealOf (U : X.Opens) (hU : IsAffineOpen U) (Z : Set X) : Ideal Γ(X, U) :=
  PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Z})

abbrev secOf (U : X.Opens) (π : R) : Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))

structure Dil (Z : Set X) where
  D : Scheme.{u}
  p : D ⟶ X
  affine : IsAffineHom p
  loft : LocallyOfFiniteType p
  isIso_restrict : ∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)
  apply_mem : ∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Z
  chart : ∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R), IsLocalRing.maximalIdeal R = Ideal.span {π} →
    ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
        Spec (CommRingCat.of (AffineDilatation.Ring (idealOf U hU Z) (secOf f U π))),
      (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
          (AffineDilatation.Ring (idealOf U hU Z) (secOf f U π)))) ≫ hU.fromSpec

attribute [scoped instance] Dil.affine Dil.loft

def ChartConcl {X₁ : Scheme.{u}} (v : X₁ ⟶ X) (i : ℕ) (U : X.Opens) (hU : IsAffineOpen U) (π : R) : Prop :=
  ∃ (W : X₁.Opens)
    (e : (W : Scheme.{u}) ≅ Spec (CommRingCat.of (AffineDilatation.Ring (idealOf U hU (Y i)) (secOf f U π)))),
    W.ι ≫ v = e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (AffineDilatation.Ring (idealOf U hU (Y i)) (secOf f U π)))) ≫ hU.fromSpec ∧
    ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
        (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
        (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
        x₁.1 (IsLocalRing.closedPoint R') ∈ W

structure Prev (n : ℕ) where
  Q : Scheme.{u}
  w : Q ⟶ X
  sep : IsSeparated w
  loft : LocallyOfFiniteType w
  qc : QuasiCompact w
  isoK : IsIso (w ∣_ XK f)
  isoC : IsIso (w ∣_ C Y hY 0)
  notMem : ∀ q : Q, w q ∉ Y n
  lift : ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
    Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
    ∀ x : Spec (CommRingCat.of R') ⟶ X, x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      x (IsLocalRing.closedPoint R') ∉ Y n → ∃ x₁ : Spec (CommRingCat.of R') ⟶ Q, x₁ ≫ w = x
  chart : ∀ i, i < n → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ U, y ∉ Y (i + 1)) →
    ∀ π : R, IsLocalRing.maximalIdeal R = Ideal.span {π} → ChartConcl f Y w i U hU π

attribute [scoped instance] Prev.sep Prev.loft Prev.qc Prev.isoK Prev.isoC

end Setup

section Base

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)

def prevZero : Prev f Y hY 0 where
  Q := ↑(C Y hY 0)
  w := (C Y hY 0).ι
  sep := inferInstance
  loft := inferInstance
  qc := by
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    infer_instance
  isoK := isIso_ι_morphismRestrict _ _ (XK_le_C f Y hY hYs 0)
  isoC := isIso_ι_morphismRestrict _ _ le_rfl
  notMem := fun q => q.2
  lift := by
    intro R' _ _ _ _ _ x _ hx₀
    exact ⟨IsOpenImmersion.lift (C Y hY 0).ι x (range_subset_of_apply_closedPoint_mem (W := C Y hY 0) x hx₀),
      IsOpenImmersion.lift_fac _ _ _⟩
  chart := fun i hi => absurd hi (Nat.not_lt_zero i)

end Base

section Step

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable {Y : ℕ → Set X} (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)
variable {n : ℕ} (𝔓 : Prev f Y hY n) (𝔇 : Dil f (Y n))

def E : 𝔇.D.Opens := 𝔇.p ⁻¹ᵁ C Y hY (n + 1)

abbrev U₀ : 𝔇.D.Opens := 𝔇.p ⁻¹ᵁ XK f

include hYs in
theorem U₀_le_E : U₀ 𝔇 ≤ E hY 𝔇 := fun _ hd => XK_le_C f Y hY hYs (n + 1) hd

scoped instance : IsIso (𝔇.p ∣_ XK f) := 𝔇.isIso_restrict _ fun _ hx => hx

def iE : (↑(U₀ 𝔇) : Scheme.{u}) ⟶ ↑(E hY 𝔇) := 𝔇.D.homOfLE (U₀_le_E hY hYs 𝔇)

scoped instance : IsOpenImmersion (iE hY hYs 𝔇) := by
  delta iE; infer_instance

def iQ : (↑(U₀ 𝔇) : Scheme.{u}) ⟶ 𝔓.Q := (𝔇.p ∣_ XK f) ≫ inv (𝔓.w ∣_ XK f) ≫ (𝔓.w ⁻¹ᵁ XK f).ι

scoped instance : IsOpenImmersion (iQ hY 𝔓 𝔇) := by
  delta iQ; infer_instance

theorem iQ_w : iQ hY 𝔓 𝔇 ≫ 𝔓.w = (U₀ 𝔇).ι ≫ 𝔇.p := by
  rw [iQ, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]

theorem iE_p : iE hY hYs 𝔇 ≫ (E hY 𝔇).ι ≫ 𝔇.p = (U₀ 𝔇).ι ≫ 𝔇.p := by
  rw [iE, ← Category.assoc, Scheme.homOfLE_ι]

def X₁ : Scheme.{u} := pushout (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)

def jE : (↑(E hY 𝔇) : Scheme.{u}) ⟶ X₁ hY hYs 𝔓 𝔇 := pushout.inl _ _

def jQ : 𝔓.Q ⟶ X₁ hY hYs 𝔓 𝔇 := pushout.inr _ _

scoped instance : IsOpenImmersion (jE hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.left))

scoped instance : IsOpenImmersion (jQ hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.right))

def v : X₁ hY hYs 𝔓 𝔇 ⟶ X :=
  pushout.desc ((E hY 𝔇).ι ≫ 𝔇.p) 𝔓.w (by rw [iE_p, iQ_w])

@[scoped simp] theorem jE_v : jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇 = (E hY 𝔇).ι ≫ 𝔇.p := pushout.inl_desc _ _ _
@[scoped simp] theorem jQ_v : jQ hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇 = 𝔓.w := pushout.inr_desc _ _ _

theorem jE_iE : iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇 = iQ hY 𝔓 𝔇 ≫ jQ hY hYs 𝔓 𝔇 := pushout.condition

theorem v_jE_apply (e : ↥(E hY 𝔇)) : v hY hYs 𝔓 𝔇 (jE hY hYs 𝔓 𝔇 e) = 𝔇.p e.1 := by
  rw [← Scheme.Hom.comp_apply, jE_v, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]

theorem v_jQ_apply (q : 𝔓.Q) : v hY hYs 𝔓 𝔇 (jQ hY hYs 𝔓 𝔇 q) = 𝔓.w q := by
  rw [← Scheme.Hom.comp_apply, jQ_v]

theorem cover (z : X₁ hY hYs 𝔓 𝔇) : (∃ e, jE hY hYs 𝔓 𝔇 e = z) ∨ ∃ q, jQ hY hYs 𝔓 𝔇 q = z := by
  obtain ⟨i, xi, rfl⟩ :=
    Scheme.IsLocallyDirected.ι_jointly_surjective (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) z
  rcases i with (_ | _ | _)
  · left
    refine ⟨iE hY hYs 𝔇 xi, ?_⟩
    change (iE hY hYs 𝔇 ≫ pushout.inl (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) xi = _
    rw [← colimit.w (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.Hom.fst]
    rfl
  · exact Or.inl ⟨xi, rfl⟩
  · exact Or.inr ⟨xi, rfl⟩

theorem mem_U₀ (e : ↥(E hY 𝔇)) (he : 𝔇.p e.1 ∉ Y n) : e.1 ∈ U₀ 𝔇 := fun h => he (𝔇.apply_mem _ h)

theorem jE_mem_range_jQ (e : ↥(E hY 𝔇)) (he : 𝔇.p e.1 ∉ Y n) :
    jE hY hYs 𝔓 𝔇 e ∈ Set.range (jQ hY hYs 𝔓 𝔇) := by
  refine ⟨iQ hY 𝔓 𝔇 ⟨e.1, mem_U₀ hY 𝔇 e he⟩, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← jE_iE, Scheme.Hom.comp_apply]
  congr 1
  exact 𝔇.D.homOfLE_apply' _ e.1 _

theorem mem_range_jE (z : X₁ hY hYs 𝔓 𝔇) (hz : v hY hYs 𝔓 𝔇 z ∈ Y n) :
    z ∈ Set.range (jE hY hYs 𝔓 𝔇) := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · exact ⟨e, rfl⟩
  · rw [v_jQ_apply] at hz; exact absurd hz (𝔓.notMem q)

theorem mem_range_jQ (z : X₁ hY hYs 𝔓 𝔇) (hz : v hY hYs 𝔓 𝔇 z ∉ Y n) :
    z ∈ Set.range (jQ hY hYs 𝔓 𝔇) := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · rw [v_jE_apply] at hz
    exact jE_mem_range_jQ hY hYs 𝔓 𝔇 e hz
  · exact ⟨q, rfl⟩

theorem v_notMem (hanti : ∀ i, Y (i + 1) ⊆ Y i) (z : X₁ hY hYs 𝔓 𝔇) : v hY hYs 𝔓 𝔇 z ∉ Y (n + 1) := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · rw [v_jE_apply]; exact e.2
  · rw [v_jQ_apply]; exact fun h => 𝔓.notMem q (hanti n h)

def cov : (X₁ hY hYs 𝔓 𝔇).OpenCover :=
  Scheme.IsLocallyDirected.openCover (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇))

theorem cov_f_zero : (cov hY hYs 𝔓 𝔇).f WalkingSpan.zero = iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇 :=
  (colimit.w (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.Hom.fst).symm

theorem cov_f_left : (cov hY hYs 𝔓 𝔇).f WalkingSpan.left = jE hY hYs 𝔓 𝔇 := rfl

theorem cov_f_right : (cov hY hYs 𝔓 𝔇).f WalkingSpan.right = jQ hY hYs 𝔓 𝔇 := rfl

scoped instance isSeparated_v : IsSeparated (v hY hYs 𝔓 𝔇) := by
  haveI : ∀ i, IsSeparated ((cov hY hYs 𝔓 𝔇).f i ≫ v hY hYs 𝔓 𝔇) := by
    rintro (_ | _ | _)
    · rw [cov_f_zero, Category.assoc, jE_v]; infer_instance
    · rw [cov_f_left, jE_v]; infer_instance
    · rw [cov_f_right, jQ_v]; infer_instance
  refine isSeparated_of_openCover (v hY hYs 𝔓 𝔇) (cov hY hYs 𝔓 𝔇) ?_
  intro z₁ z₂ h
  by_cases h₁ : v hY hYs 𝔓 𝔇 z₁ ∈ Y n
  · refine ⟨WalkingSpan.left, ?_, ?_⟩ <;> rw [cov_f_left]
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)
  · refine ⟨WalkingSpan.right, ?_, ?_⟩ <;> rw [cov_f_right]
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)

scoped instance locallyOfFiniteType_v : LocallyOfFiniteType (v hY hYs 𝔓 𝔇) := by
  refine IsZariskiLocalAtSource.of_openCover (cov hY hYs 𝔓 𝔇) ?_
  rintro (_ | _ | _)
  · rw [cov_f_zero, Category.assoc, jE_v]; infer_instance
  · rw [cov_f_left, jE_v]; infer_instance
  · rw [cov_f_right, jQ_v]; infer_instance

scoped instance quasiCompact_v [LocallyOfFiniteType f] : QuasiCompact (v hY hYs 𝔓 𝔇) := by
  haveI : IsLocallyNoetherian 𝔇.D := LocallyOfFiniteType.isLocallyNoetherian (𝔇.p ≫ f)
  haveI : QuasiCompact ((E hY 𝔇).ι ≫ 𝔇.p) := inferInstance
  constructor
  intro U hUo hUc
  have hset : v hY hYs 𝔓 𝔇 ⁻¹' U =
      jE hY hYs 𝔓 𝔇 '' (((E hY 𝔇).ι ≫ 𝔇.p) ⁻¹' U) ∪ jQ hY hYs 𝔓 𝔇 '' (𝔓.w ⁻¹' U) := by
    ext z
    constructor
    · intro hz
      rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
      · left; refine ⟨e, ?_, rfl⟩
        rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, jE_v] at hz; exact hz
      · right; refine ⟨q, ?_, rfl⟩
        rw [Set.mem_preimage, ← v_jQ_apply hY hYs 𝔓 𝔇 q]; exact hz
    · rintro (⟨e, he, rfl⟩ | ⟨q, hq, rfl⟩)
      · show (jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇) e ∈ U
        rw [jE_v]; exact he
      · show v hY hYs 𝔓 𝔇 (jQ hY hYs 𝔓 𝔇 q) ∈ U
        rw [v_jQ_apply]; exact hq
  rw [hset]
  exact ((QuasiCompact.isCompact_preimage (f := (E hY 𝔇).ι ≫ 𝔇.p) U hUo hUc).image
    (jE hY hYs 𝔓 𝔇).continuous).union
    ((QuasiCompact.isCompact_preimage (f := 𝔓.w) U hUo hUc).image (jQ hY hYs 𝔓 𝔇).continuous)

theorem isIso_restrict_XK : IsIso (v hY hYs 𝔓 𝔇 ∣_ XK f) :=
  isIso_morphismRestrict_of_comp (v hY hYs 𝔓 𝔇) (jQ hY hYs 𝔓 𝔇) 𝔓.w (jQ_v hY hYs 𝔓 𝔇) (XK f) 𝔓.isoK
    fun z hz => mem_range_jQ hY hYs 𝔓 𝔇 z fun h => hz (hYs n _ h)

theorem isIso_restrict_C (hanti : ∀ i, Y (i + 1) ⊆ Y i) : IsIso (v hY hYs 𝔓 𝔇 ∣_ C Y hY 0) :=
  isIso_morphismRestrict_of_comp (v hY hYs 𝔓 𝔇) (jQ hY hYs 𝔓 𝔇) 𝔓.w (jQ_v hY hYs 𝔓 𝔇) (C Y hY 0) 𝔓.isoC
    fun z hz => mem_range_jQ hY hYs 𝔓 𝔇 z fun h => hz ((antitone_nat_of_succ_le hanti) (Nat.zero_le n) h)

section Lift

variable (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
variable (hR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')

include hR' in
theorem algebraMap_ne_zero {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    algebraMap R R' π ≠ 0 := by
  intro h0
  rw [hπ, Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_zero] at hR'
  exact IsDiscreteValuationRing.not_a_field R' hR'.symm

include hY hR' in

theorem exists_lift_D (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hx₀ : x (IsLocalRing.closedPoint R') ∈ Y n) :
    ∃ x₁ : Spec (CommRingCat.of R') ⟶ 𝔇.D, x₁ ≫ 𝔇.p = x := by
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπirr.maximalIdeal_eq
  obtain ⟨_, ⟨U, hU, rfl⟩, hx₀U, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint R'))) isOpen_univ
  obtain ⟨e, he⟩ := 𝔇.chart U hU π hπ
  have hle : (⊤ : (Spec (CommRingCat.of R')).Opens) ≤ x ⁻¹ᵁ U := by
    rintro t -
    have := range_subset_of_apply_closedPoint_mem (W := U) x hx₀U ⟨t, rfl⟩
    rwa [Scheme.Opens.range_ι] at this

  let φ' : Γ(X, U) ⟶ CommRingCat.of R' := x.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom
  have hφ'x : Spec.map φ' ≫ hU.fromSpec = x := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  let I : Ideal Γ(X, U) := idealOf U hU (Y n)
  let a : Γ(X, U) := secOf f U π
  have hφ'a : φ'.hom a = algebraMap R R' π := by
    simp only [φ', a, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply (X.presheaf.map _) (x.appLE U ⊤ hle), Scheme.Hom.map_appLE]
    have h1 : x.appLE ⊤ ⊤ (hle.trans (x.preimage_mono le_top)) = x.appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [h1, ← CommRingCat.comp_apply f.appTop x.appTop, ← Scheme.Hom.comp_appTop, hx,
      ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R')).hom, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R)).hom,
      Iso.inv_hom_id]
    rfl
  letI alg : Algebra Γ(X, U) R' := φ'.hom.toAlgebra
  have hreg : IsSMulRegular R' a := by
    intro r s hrs
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hφ'a] at hrs
    exact mul_left_cancel₀ (algebraMap_ne_zero R' hR' hπ) hrs

  have hIle : I.map (algebraMap Γ(X, U) R') ≤ Ideal.span {algebraMap Γ(X, U) R' a} := by
    rw [RingHom.algebraMap_toAlgebra, hφ'a, ← Set.image_singleton, ← Ideal.map_span, ← hπ, hR',
      Ideal.map_le_iff_le_comap]
    set q := Spec.map φ' (IsLocalRing.closedPoint R') with hq
    have hq0 : hU.fromSpec q = x (IsLocalRing.closedPoint R') := by
      rw [hq, ← Scheme.Hom.comp_apply, hφ'x]
    have hqY : hU.fromSpec q ∈ Y n := hq0 ▸ hx₀
    have h := (mem_iff_vanishingIdeal_le hU (Y n) (hY n) (hU.fromSpec q) (fromSpec_mem hU q)).mp hqY
    rw [primeIdealOf_fromSpec] at h
    have hq' : q.asIdeal = Ideal.comap φ'.hom (IsLocalRing.maximalIdeal R') := by
      rw [hq, Spec.map_apply]; rfl
    rw [← hq']
    exact h
  obtain ⟨⟨ψ⟩, -⟩ := AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular I a hreg hIle
  have hψ : CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring I a)) ≫
      CommRingCat.ofHom ψ.toRingHom = φ' := by
    ext g
    change ψ (algebraMap Γ(X, U) (AffineDilatation.Ring I a) g) = φ'.hom g
    rw [ψ.commutes]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ e.inv ≫ (𝔇.p ⁻¹ᵁ U).ι, ?_⟩
  rw [Category.assoc, Category.assoc, he, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, hψ, hφ'x]

include hR' in

theorem exists_lift (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hxn : x (IsLocalRing.closedPoint R') ∉ Y (n + 1)) :
    ∃ x₁ : Spec (CommRingCat.of R') ⟶ X₁ hY hYs 𝔓 𝔇, x₁ ≫ v hY hYs 𝔓 𝔇 = x := by
  by_cases hx₀ : x (IsLocalRing.closedPoint R') ∈ Y n
  swap
  ·
    obtain ⟨x₁, hx₁⟩ := 𝔓.lift R' hR' x hx hx₀
    exact ⟨x₁ ≫ jQ hY hYs 𝔓 𝔇, by rw [Category.assoc, jQ_v, hx₁]⟩

  obtain ⟨xD, hxD⟩ := exists_lift_D hY 𝔇 R' hR' x hx hx₀
  have hmem : xD (IsLocalRing.closedPoint R') ∈ E hY 𝔇 := by
    change 𝔇.p (xD (IsLocalRing.closedPoint R')) ∉ Y (n + 1)
    rwa [← Scheme.Hom.comp_apply, hxD]
  have hr := range_subset_of_apply_closedPoint_mem (W := E hY 𝔇) xD hmem
  refine ⟨IsOpenImmersion.lift (E hY 𝔇).ι xD hr ≫ jE hY hYs 𝔓 𝔇, ?_⟩
  rw [Category.assoc, jE_v, ← Category.assoc, IsOpenImmersion.lift_fac, hxD]

end Lift

theorem chart_new (U : X.Opens) (hU : IsAffineOpen U) (hUY : ∀ y ∈ U, y ∉ Y (n + 1)) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) : ChartConcl f Y (v hY hYs 𝔓 𝔇) n U hU π := by
  obtain ⟨e, he⟩ := 𝔇.chart U hU π hπ
  have hle : 𝔇.p ⁻¹ᵁ U ≤ E hY 𝔇 := fun d hd => hUY _ hd
  let g := 𝔇.D.homOfLE hle ≫ jE hY hYs 𝔓 𝔇
  let e₀ := IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by rw [Scheme.Opens.range_ι]; rfl)
  have he₀ : e₀.hom ≫ g = g.opensRange.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine ⟨g.opensRange, e₀ ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, ← he, ← he₀, Category.assoc, Category.assoc, jE_v, ← Category.assoc _ _ 𝔇.p,
      Scheme.homOfLE_ι]
  · intro R' _ _ _ _ _ x₁ hYmem hUmem
    obtain ⟨d, hd⟩ := mem_range_jE hY hYs 𝔓 𝔇 (x₁.1 (IsLocalRing.closedPoint R')) hYmem
    have hdU : d.1 ∈ 𝔇.p ⁻¹ᵁ U := by
      change 𝔇.p d.1 ∈ U
      rwa [← v_jE_apply hY hYs 𝔓 𝔇 d, hd]
    change x₁.1 (IsLocalRing.closedPoint R') ∈ Set.range g
    refine ⟨⟨d.1, hdU⟩, ?_⟩
    change jE hY hYs 𝔓 𝔇 (𝔇.D.homOfLE hle ⟨d.1, hdU⟩) = _
    rw [Scheme.homOfLE_apply']
    exact hd

theorem chart_old (hanti : ∀ i, Y (i + 1) ⊆ Y i) (i : ℕ) (hi : i < n) (U : X.Opens) (hU : IsAffineOpen U)
    (hUY : ∀ y ∈ U, y ∉ Y (i + 1)) (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    ChartConcl f Y (v hY hYs 𝔓 𝔇) i U hU π := by
  obtain ⟨W', e', he', hcatch⟩ := 𝔓.chart i hi U hU hUY π hπ
  let j := jQ hY hYs 𝔓 𝔇
  refine ⟨j ''ᵁ W', (j.isoImage W').symm ≪≫ e', ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he', ← Scheme.Hom.isoImage_inv_ι j W',
      Category.assoc, Category.assoc, jQ_v]
  · intro R' _ _ _ _ hR' x₁ hYmem hUmem

    have hnot : (x₁.1 ≫ v hY hYs 𝔓 𝔇) (IsLocalRing.closedPoint R') ∉ Y n := fun h =>
      hUY _ hUmem ((antitone_nat_of_succ_le hanti) (Nat.succ_le_of_lt hi) h)
    have hrange : Set.range x₁.1 ⊆ Set.range j := by
      have h1 : x₁.1 (IsLocalRing.closedPoint R') ∈ j.opensRange :=
        mem_range_jQ hY hYs 𝔓 𝔇 _ (by rwa [Scheme.Hom.comp_apply] at hnot)
      have h2 := range_subset_of_apply_closedPoint_mem (W := j.opensRange) x₁.1 h1
      rwa [Scheme.Opens.range_ι] at h2
    let y := IsOpenImmersion.lift j x₁.1 hrange
    have hy : y ≫ j = x₁.1 := IsOpenImmersion.lift_fac _ _ _
    have hyover : y ≫ 𝔓.w ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [← jQ_v hY hYs 𝔓 𝔇, ← Category.assoc, ← Category.assoc, hy, Category.assoc]; exact x₁.2
    have h1 : (y ≫ 𝔓.w) (IsLocalRing.closedPoint R') = (x₁.1 ≫ v hY hYs 𝔓 𝔇) (IsLocalRing.closedPoint R') := by
      rw [← jQ_v hY hYs 𝔓 𝔇, ← Category.assoc, hy]
    have hW' := hcatch R' hR' ⟨y, hyover⟩ (by rw [h1]; exact hYmem) (by rw [h1]; exact hUmem)
    change x₁.1 (IsLocalRing.closedPoint R') ∈ j ''ᵁ W'
    rw [← hy, Scheme.Hom.comp_apply]
    exact ⟨_, hW', rfl⟩

def prevSucc [LocallyOfFiniteType f] (hanti : ∀ i, Y (i + 1) ⊆ Y i) : Prev f Y hY (n + 1) where
  Q := X₁ hY hYs 𝔓 𝔇
  w := v hY hYs 𝔓 𝔇
  sep := inferInstance
  loft := inferInstance
  qc := inferInstance
  isoK := isIso_restrict_XK hY hYs 𝔓 𝔇
  isoC := isIso_restrict_C hY hYs 𝔓 𝔇 hanti
  notMem := v_notMem hY hYs 𝔓 𝔇 hanti
  lift := fun R' _ _ _ _ hR' x hx hxn => exists_lift hY hYs 𝔓 𝔇 R' hR' x hx hxn
  chart := by
    intro i hi U hU hUY π hπ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact chart_old hY hYs 𝔓 𝔇 hanti i hi U hU hUY π hπ
    · exact chart_new hY hYs 𝔓 𝔇 U hU hUY π hπ

end Step

section Consequences

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable {Y : ℕ → Set X} (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)
variable {X₁ : Scheme.{u}} (v : X₁ ⟶ X) (hC : IsIso (v ∣_ C Y hY 0))

include hYs hC in

theorem isIso_genericFibre (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
      v (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  refine isIso_pullback_map v f _ (C Y hY 0) hC fun t => ?_
  intro hmem
  have h1 : f (pullback.fst f (specGenericFibreInclusion R K) t) =
      (specGenericFibreInclusion R K) (pullback.snd f (specGenericFibreInclusion R K) t) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have h2 := hYs 0 _ hmem
  rw [h1] at h2
  exact specMap_apply_ne_closedPoint (algebraMap R K) (IsFractionRing.injective R K) _
    (Ideal.eq_bot_of_prime _) h2

variable [IsSeparated v]
variable (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
variable (hR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')

include hYs hC hR' in

theorem lift_unique (x₁ x₂ : Spec (CommRingCat.of R') ⟶ X₁) (h : x₁ ≫ v = x₂ ≫ v)
    (hx : x₁ ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) : x₁ = x₂ := by
  haveI := hC
  let K' := FractionRing R'
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  have happ : ι.appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (algebraMap R' K') ≫
      (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsDominant ι := isDominant_of_of_appTop_injective (by
    rw [happ]
    exact (Scheme.ΓSpecIso (CommRingCat.of K')).commRingCatIsoToRingEquiv.symm.injective.comp
      ((IsFractionRing.injective R' K').comp
        (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.injective))
  refine ext_of_isDominant_of_isSeparated v h ι ?_

  have hinj : Function.Injective ((algebraMap R' K').comp (algebraMap R R')) :=
    (IsFractionRing.injective R' K').comp (algebraMap_injective hR')
  have hmem : ∀ y : Spec (CommRingCat.of R') ⟶ X₁,
      y ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      Set.range (ι ≫ y) ⊆ Set.range (v ⁻¹ᵁ C Y hY 0).ι := by
    rintro y hy _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change v ((ι ≫ y) t) ∉ Y 0
    intro hmemY
    have h1 := hYs 0 _ hmemY
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hy, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp] at h1
    exact specMap_apply_ne_closedPoint _ hinj t (Ideal.eq_bot_of_prime _) h1
  have hx₂ : x₂ ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [← Category.assoc, ← h, Category.assoc, hx]
  let a := IsOpenImmersion.lift (v ⁻¹ᵁ C Y hY 0).ι (ι ≫ x₁) (hmem x₁ hx)
  let b := IsOpenImmersion.lift (v ⁻¹ᵁ C Y hY 0).ι (ι ≫ x₂) (hmem x₂ hx₂)
  have ha : a ≫ (v ⁻¹ᵁ C Y hY 0).ι = ι ≫ x₁ := IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ (v ⁻¹ᵁ C Y hY 0).ι = ι ≫ x₂ := IsOpenImmersion.lift_fac _ _ _
  have hab : a = b := by
    rw [← cancel_mono (v ∣_ C Y hY 0), ← cancel_mono (C Y hY 0).ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, reassoc_of% ha, reassoc_of% hb, h]
  rw [← ha, ← hb, hab]

end Consequences

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i)
  (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)

include hanti hYs in
theorem nonempty_prev : ∀ n, Nonempty (Prev f Y hY n)
  | 0 => ⟨prevZero f Y hY hYs⟩
  | n + 1 => by
    obtain ⟨𝔓⟩ := nonempty_prev n
    obtain ⟨D, p, h1, h2, h3, h4, h5⟩ :=
      NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed f (Y n) (hY n)
        (hYs n)
    let 𝔇 : Dil f (Y n) := ⟨D, p, h1, h2, h3, h4, h5⟩
    exact ⟨prevSucc hY hYs 𝔓 𝔇 hanti⟩

end Main

end P2mStrataGlue
p2m_reactivate "P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.P2mStrataGlue"

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.P2mStrataGlue"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (t : ℕ) (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i) (hYt : Y t = ∅)
    (hYs : ∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType v ∧ QuasiCompact v ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ ⟨(Y 0)ᶜ, (hY 0).isOpen_compl⟩) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
        Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃! x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f), x₁.1 ≫ v = x.1) ∧
      (∀ (i : ℕ), i < t → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) →
        ∀ (π : R), IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ (W : X₁.Opens)
          (e : (W : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))),
          W.ι ≫ v = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec ∧
          ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
            Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
            ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
              x₁.1 (IsLocalRing.closedPoint R') ∈ W) := by
  have hYs' : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R :=
    fun m y hy => hYs y ((antitone_nat_of_succ_le hanti) (Nat.zero_le m) hy)
  obtain ⟨𝔓⟩ := P2mStrataGlue.nonempty_prev f Y hY hanti hYs' t
  refine ⟨𝔓.Q, 𝔓.w, 𝔓.sep, 𝔓.loft, 𝔓.qc, P2mStrataGlue.isIso_genericFibre hY hYs' 𝔓.w 𝔓.isoC K, 𝔓.isoC, ?_,
    fun i hi U hU hUY π hπ => 𝔓.chart i hi U hU hUY π hπ⟩
  intro R' _ _ _ _ hR' x
  obtain ⟨x₁, hx₁⟩ := 𝔓.lift R' hR' x.1 x.2 (by rw [hYt]; exact Set.notMem_empty _)
  refine ⟨⟨x₁, by rw [← Category.assoc, hx₁]; exact x.2⟩, hx₁, ?_⟩
  rintro ⟨x₂, hx₂'⟩ hx₂
  exact Subtype.ext (P2mStrataGlue.lift_unique hY hYs' 𝔓.w 𝔓.isoC R' hR' x₂ x₁ (hx₂.trans hx₁.symm) hx₂')

end S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
end P2MW
export P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed (solution)

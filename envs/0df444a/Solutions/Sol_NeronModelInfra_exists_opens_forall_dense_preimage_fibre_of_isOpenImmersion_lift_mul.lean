-- Prove2me | solution 1 for NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5d5780b3-7d59-5081-ae79-6fee2b1e6d09

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd
import Theorems.Thm_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

universe u

namespace P2mStrictify

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

theorem DenseIn.of_subset {S F : Set P} (h : F ⊆ S) : DenseIn S F :=
  fun _ hx => subset_closure ⟨h hx, hx⟩

theorem DenseIn.of_inter_subset {S S' F : Set P} (h : DenseIn S F) (hS : S ∩ F ⊆ S') : DenseIn S' F :=
  h.trans (closure_mono fun _ hx => ⟨hS hx, hx.2⟩)

theorem DenseIn.inter_of_isOpen_left {S T F : Set P} (hS : DenseIn S F) (hT : DenseIn T F)
    (ho : IsOpen S) : DenseIn (S ∩ T) F := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨y, hyO, hyS, hyF⟩ := mem_closure_iff.mp (hS hx) O hO hxO
  obtain ⟨z, ⟨hzO, hzS⟩, hzT, hzF⟩ := mem_closure_iff.mp (hT hyF) (O ∩ S) (hO.inter ho) ⟨hyO, hyS⟩
  exact ⟨z, hzO, ⟨hzS, hzT⟩, hzF⟩

theorem DenseIn.inter_of_isOpen_right {S T F : Set P} (hS : DenseIn S F) (hT : DenseIn T F)
    (ho : IsOpen T) : DenseIn (S ∩ T) F := by
  rw [Set.inter_comm]; exact hT.inter_of_isOpen_left hS ho

theorem DenseIn.of_forall_exists_specializes {S F : Set P}
    (h : ∀ x ∈ F, ∃ θ ∈ F, θ ∈ S ∧ θ ⤳ x) : DenseIn S F := by
  intro x hx
  obtain ⟨θ, hθF, hθS, hθx⟩ := h x hx
  exact closure_mono (Set.singleton_subset_iff.mpr (show θ ∈ S ∩ F from ⟨hθS, hθF⟩)) hθx.mem_closure

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

theorem DenseIn.image_homeomorph {P' : Type*} [TopologicalSpace P'] (σ : P ≃ₜ P') {S F : Set P}
    (h : DenseIn S F) : DenseIn (σ '' S) (σ '' F) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Set.image_inter σ.injective, ← σ.image_closure]
  exact ⟨y, h hy, rfl⟩

theorem six_denseIn {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    (p₁ p₂ : P → X) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (ι : W → P) (hι : IsOpenEmbedding ι) (m : W → X) (hm : Continuous m)
    (Φ Ψ : W → P) (hΦ : IsInducing Φ) (hΨ : IsInducing Ψ)
    (hΦ₁ : ∀ w, p₁ (Φ w) = p₁ (ι w)) (hΦ₂ : ∀ w, p₂ (Φ w) = m w)
    (hΨ₁ : ∀ w, p₁ (Ψ w) = m w) (hΨ₂ : ∀ w, p₂ (Ψ w) = p₂ (ι w))
    (X' : Set X) (hX' : IsOpen X') (a : X) (ha : a ∈ X')
    (h₁ : DenseIn (Set.range ι ∩ Set.range Φ ∩ Set.range Ψ) (p₁ ⁻¹' {a}))
    (h₂ : DenseIn (Set.range ι ∩ Set.range Φ ∩ Set.range Ψ) (p₂ ⁻¹' {a}))
    (h₃ : DenseIn (p₂ ⁻¹' X') (p₁ ⁻¹' {a}))
    (h₄ : DenseIn (p₁ ⁻¹' X') (p₂ ⁻¹' {a})) :
    DenseIn (ι '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (ι '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) ∧
    DenseIn (Φ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (Φ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) ∧
    DenseIn (Ψ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₁ ⁻¹' {a}) ∧
    DenseIn (Ψ '' {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'}) (p₂ ⁻¹' {a}) := by
  set UW : Set W := {w | p₁ (ι w) ∈ X' ∧ p₂ (ι w) ∈ X' ∧ m w ∈ X'} with hUW
  set F : Set P := p₁ ⁻¹' {a} with hF
  set F' : Set P := p₂ ⁻¹' {a} with hF'

  set A : Set W := ι ⁻¹' (p₁ ⁻¹' X') with hA
  set B : Set W := ι ⁻¹' (p₂ ⁻¹' X') with hB
  set M : Set W := m ⁻¹' X' with hM
  have hAo : IsOpen A := (hX'.preimage hp₁).preimage hι.continuous
  have hBo : IsOpen B := (hX'.preimage hp₂).preimage hι.continuous
  have hMo : IsOpen M := hX'.preimage hm
  have hUW' : UW = A ∩ B ∩ M := by
    ext w; simp only [hUW, hA, hB, hM, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]

  have hιF : DenseIn (Set.range ι) F := h₁.mono fun _ h => h.1.1
  have hΦF : DenseIn (Set.range Φ) F := h₁.mono fun _ h => h.1.2
  have hΨF : DenseIn (Set.range Ψ) F := h₁.mono fun _ h => h.2
  have hιF' : DenseIn (Set.range ι) F' := h₂.mono fun _ h => h.1.1
  have hΦF' : DenseIn (Set.range Φ) F' := h₂.mono fun _ h => h.1.2
  have hΨF' : DenseIn (Set.range Ψ) F' := h₂.mono fun _ h => h.2

  have eΦF : Φ ⁻¹' F = ι ⁻¹' F := by
    ext w; simp only [hF, Set.mem_preimage, Set.mem_singleton_iff, hΦ₁]
  have eΨF' : Ψ ⁻¹' F' = ι ⁻¹' F' := by
    ext w; simp only [hF', Set.mem_preimage, Set.mem_singleton_iff, hΨ₂]
  have eΦF' : Φ ⁻¹' F' = m ⁻¹' {a} := by
    ext w; simp only [hF', Set.mem_preimage, Set.mem_singleton_iff, hΦ₂]
  have eΨF : Ψ ⁻¹' F = m ⁻¹' {a} := by
    ext w; simp only [hF, Set.mem_preimage, Set.mem_singleton_iff, hΨ₁]

  have iA : ι '' A = Set.range ι ∩ p₁ ⁻¹' X' := Set.image_preimage_eq_range_inter
  have iB : ι '' B = Set.range ι ∩ p₂ ⁻¹' X' := Set.image_preimage_eq_range_inter
  have ΦA : Φ '' A = Set.range Φ ∩ p₁ ⁻¹' X' := by
    have : A = Φ ⁻¹' (p₁ ⁻¹' X') := by ext w; simp only [hA, Set.mem_preimage, hΦ₁]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΦM : Φ '' M = Set.range Φ ∩ p₂ ⁻¹' X' := by
    have : M = Φ ⁻¹' (p₂ ⁻¹' X') := by ext w; simp only [hM, Set.mem_preimage, hΦ₂]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΨM : Ψ '' M = Set.range Ψ ∩ p₁ ⁻¹' X' := by
    have : M = Ψ ⁻¹' (p₁ ⁻¹' X') := by ext w; simp only [hM, Set.mem_preimage, hΨ₁]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have ΨB : Ψ '' B = Set.range Ψ ∩ p₂ ⁻¹' X' := by
    have : B = Ψ ⁻¹' (p₂ ⁻¹' X') := by ext w; simp only [hB, Set.mem_preimage, hΨ₂]
    rw [this]; exact Set.image_preimage_eq_range_inter
  have oX'₁ : IsOpen (p₁ ⁻¹' X') := hX'.preimage hp₁
  have oX'₂ : IsOpen (p₂ ⁻¹' X') := hX'.preimage hp₂

  have dF : DenseIn UW (ι ⁻¹' F) := by
    have dB : DenseIn B (ι ⁻¹' F) := by
      rw [← DenseIn.image_iff hι.isInducing hιF, iB]; exact hιF.inter_of_isOpen_right h₃ oX'₂
    have dM : DenseIn M (ι ⁻¹' F) := by
      rw [← eΦF, ← DenseIn.image_iff hΦ hΦF, ΦM]; exact hΦF.inter_of_isOpen_right h₃ oX'₂
    refine (dB.inter_of_isOpen_left dM hBo).of_inter_subset ?_
    rintro w ⟨⟨hwB, hwM⟩, hwF⟩
    rw [hUW']
    refine ⟨⟨?_, hwB⟩, hwM⟩
    change p₁ (ι w) ∈ X'
    have : p₁ (ι w) = a := by simpa [hF] using hwF
    rw [this]; exact ha

  have dF' : DenseIn UW (ι ⁻¹' F') := by
    have dA : DenseIn A (ι ⁻¹' F') := by
      rw [← DenseIn.image_iff hι.isInducing hιF', iA]; exact hιF'.inter_of_isOpen_right h₄ oX'₁
    have dM : DenseIn M (ι ⁻¹' F') := by
      rw [← eΨF', ← DenseIn.image_iff hΨ hΨF', ΨM]; exact hΨF'.inter_of_isOpen_right h₄ oX'₁
    refine (dA.inter_of_isOpen_left dM hAo).of_inter_subset ?_
    rintro w ⟨⟨hwA, hwM⟩, hwF⟩
    rw [hUW']
    refine ⟨⟨hwA, ?_⟩, hwM⟩
    change p₂ (ι w) ∈ X'
    have : p₂ (ι w) = a := by simpa [hF'] using hwF
    rw [this]; exact ha

  have dm : DenseIn UW (m ⁻¹' {a}) := by
    have dA : DenseIn A (m ⁻¹' {a}) := by
      rw [← eΦF', ← DenseIn.image_iff hΦ hΦF', ΦA]; exact hΦF'.inter_of_isOpen_right h₄ oX'₁
    have dB : DenseIn B (m ⁻¹' {a}) := by
      rw [← eΨF, ← DenseIn.image_iff hΨ hΨF, ΨB]; exact hΨF.inter_of_isOpen_right h₃ oX'₂
    refine (dA.inter_of_isOpen_left dB hAo).of_inter_subset ?_
    rintro w ⟨⟨hwA, hwB⟩, hwm⟩
    rw [hUW']
    refine ⟨⟨hwA, hwB⟩, ?_⟩
    change m w ∈ X'
    have : m w = a := by simpa using hwm
    rw [this]; exact ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (DenseIn.image_iff hι.isInducing hιF UW).mpr dF
  · exact (DenseIn.image_iff hι.isInducing hιF' UW).mpr dF'
  · exact (DenseIn.image_iff hΦ hΦF UW).mpr (eΦF ▸ dF)
  · exact (DenseIn.image_iff hΦ hΦF' UW).mpr (eΦF' ▸ dm)
  · exact (DenseIn.image_iff hΨ hΨF UW).mpr (eΨF ▸ dm)
  · exact (DenseIn.image_iff hΨ hΨF' UW).mpr (eΨF' ▸ dF')

end Topo

section MaxGen

theorem exists_maximal_specializes {α : Type*} [TopologicalSpace α] [QuasiSober α] [T0Space α] (q : α) :
    ∃ θ : α, θ ⤳ q ∧ ∀ y : α, y ⤳ θ → y = θ := by
  obtain ⟨θ, hθ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q)) isClosed_irreducibleComponent
  refine ⟨θ, hθ.specializes mem_irreducibleComponent, fun y hy => ?_⟩
  have hsub : irreducibleComponent q ⊆ closure {y} := by
    rw [← hθ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hy.mem_closure) isClosed_closure
  have hy' : IsGenericPoint y (irreducibleComponent q) :=
    (eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub)
  exact hy'.eq hθ

end MaxGen

section MaxPts

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))

def IsMaxSp (x : P) : Prop :=
  p.base x = IsLocalRing.closedPoint R ∧
    ∀ y : P, y ⤳ x → p.base y = IsLocalRing.closedPoint R → y = x

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

end Pieces

section FibreMax

theorem exists_fibre_maximal {P Y : Scheme.{u}} (g : P ⟶ Y) (q : P) :
    ∃ θ : P, g.base θ = g.base q ∧ θ ⤳ q ∧ ∀ y : P, g.base y = g.base q → y ⤳ θ → y = θ := by
  let ε := g.fiberHomeo (g.base q)
  obtain ⟨θ, hθq, hθmax⟩ := exists_maximal_specializes (ε.symm ⟨q, rfl⟩)
  refine ⟨(g.fiberι _).base θ, ?_, ?_, ?_⟩
  · have h := (ε θ).2
    simpa [ε] using h
  · have h := hθq.map (g.fiberι _).continuous
    simpa [ε] using h
  · intro y hy hyθ
    have hy' : (g.fiberι _).base (ε.symm ⟨y, hy⟩) = y := g.fiberι_fiberHomeo_symm _ ⟨y, hy⟩
    have h : ε.symm ⟨y, hy⟩ ⤳ θ := by
      rw [← (g.fiberι _).isEmbedding.isInducing.specializes_iff, hy']
      exact hyθ
    rw [← hy', hθmax _ h]

end FibreMax

section Main

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
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
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      (∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U) ∧
      (∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
        m.1.base ⟨q, hUW hq⟩ ∈ X') ∧
      (∀ x : X, x ∈ X' →
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
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) := by
  haveI : IsLocallyNoetherian (pullback f f) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  haveI : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)
  haveI := hΦ
  haveI := hΨ
  set Φ := pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
    ((Category.assoc _ _ _).trans m.2.symm) with hΦdef
  set Ψ := pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition])) with hΨdef

  have Φfst : Φ ≫ pullback.fst f f = W.ι ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have Φsnd : Φ ≫ pullback.snd f f = m.1 := pullback.lift_snd _ _ _
  have Ψfst : Ψ ≫ pullback.fst f f = m.1 := pullback.lift_fst _ _ _
  have Ψsnd : Ψ ≫ pullback.snd f f = W.ι ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have Φfst' : ∀ w, (pullback.fst f f).base (Φ.base w) = (pullback.fst f f).base (W.ι.base w) := fun w => by
    rw [← Scheme.Hom.comp_apply, Φfst, Scheme.Hom.comp_apply]
  have Φsnd' : ∀ w, (pullback.snd f f).base (Φ.base w) = m.1.base w := fun w => by
    rw [← Scheme.Hom.comp_apply, Φsnd]
  have Ψfst' : ∀ w, (pullback.fst f f).base (Ψ.base w) = m.1.base w := fun w => by
    rw [← Scheme.Hom.comp_apply, Ψfst]
  have Ψsnd' : ∀ w, (pullback.snd f f).base (Ψ.base w) = (pullback.snd f f).base (W.ι.base w) := fun w => by
    rw [← Scheme.Hom.comp_apply, Ψsnd, Scheme.Hom.comp_apply]
  have hcond : ∀ q : ↑(pullback f f), f.base ((pullback.fst f f).base q) = f.base ((pullback.snd f f).base q) :=
    fun q => by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hmover : ∀ w : ↑W, f.base (m.1.base w) = f.base ((pullback.fst f f).base (W.ι.base w)) := fun w => by
    rw [← Scheme.Hom.comp_apply, m.2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have hpf : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q = f.base ((pullback.fst f f).base q) :=
    fun q => Scheme.Hom.comp_apply _ _ q

  set σ : pullback f f ⟶ pullback f f := (pullbackSymmetry f f).hom with hσdef
  have σfst : ∀ q, (pullback.fst f f).base (σ.base q) = (pullback.snd f f).base q := fun q => by
    rw [← Scheme.Hom.comp_apply, hσdef, pullbackSymmetry_hom_comp_fst]
  have σsnd : ∀ q, (pullback.snd f f).base (σ.base q) = (pullback.fst f f).base q := fun q => by
    rw [← Scheme.Hom.comp_apply, hσdef, pullbackSymmetry_hom_comp_snd]
  have σσ' : σ ≫ σ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσdef, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd, Category.id_comp]
    · rw [Category.assoc, hσdef, pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst, Category.id_comp]
  have σσ : ∀ q, σ.base (σ.base q) = q := fun q => by
    rw [← Scheme.Hom.comp_apply, σσ']; rfl
  let σh : ↑(pullback f f) ≃ₜ ↑(pullback f f) := Scheme.homeoOfIso (pullbackSymmetry f f)
  have σh_apply : ∀ q, σh q = σ.base q := fun q => rfl
  have hσover : σ ≫ pullback.fst f f ≫ f = pullback.fst f f ≫ f := by
    rw [hσdef, pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  have σmax : ∀ q, IsMaxSp (pullback.fst f f ≫ f) q → IsMaxSp (pullback.fst f f ≫ f) (σ.base q) := by
    intro q hq
    rw [← isMaxSp_comp_iff σ q, hσover]; exact hq

  have σF : ∀ a : X, σh '' {q | (pullback.fst f f).base q = a} = {q | (pullback.snd f f).base q = a} := by
    intro a; ext q; constructor
    · rintro ⟨q', hq', rfl⟩; simpa [σh_apply, σsnd] using hq'
    · intro hq; exact ⟨σ.base q, by simpa [σfst] using hq, by rw [σh_apply, σσ]⟩
  have σpre : ∀ T : Set X, σh '' ((fun q => (pullback.snd f f).base q) ⁻¹' T) =
      (fun q => (pullback.fst f f).base q) ⁻¹' T := by
    intro T; ext q; constructor
    · rintro ⟨q', hq', rfl⟩; simpa [σh_apply, σfst] using hq'
    · intro hq; exact ⟨σ.base q, by simpa [σsnd] using hq, by rw [σh_apply, σσ]⟩

  have relm : MulRel K LXK f e (NeronModelInfra.schemeHomOverComp (incl f W) (prj₁ f))
      (NeronModelInfra.schemeHomOverComp (incl f W) (prj₂ f)) m :=
    (mulRel_iff_display W m (prj₁ f) (prj₂ f)).mpr hmK
  let jP := pullback.fst (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let jW := pullback.fst (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
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
  have hrange_gfr : ∀ q₁ : ↑(pullback (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)),
      q₁ ∈ Set.range (genericFibreRestrict R K _ _ (incl f W)).1.base := by
    intro q₁
    rw [genericFibreRestrict_coe_eq_pullbackMap _ _ (incl f W) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm), Scheme.Pullback.range_map]
    refine ⟨?_, ⟨(pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)).base q₁, by simp⟩⟩
    change jP.base q₁ ∈ Set.range W.ι.base
    rw [Scheme.Opens.range_ι]
    apply hW₁
    have : jP.base q₁ ∈ Set.range jP.base := ⟨q₁, rfl⟩
    rwa [range_fst_specGenericFibreInclusion] at this
  have hgen_of : ∀ (Θ : (W : Scheme.{u}) ⟶ pullback f f)
      (sh : SchemeHomOver (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))) [IsIso sh.1],
      jW ≫ Θ = (genericFibreRestrict R K _ _ (incl f W)).1 ≫ sh.1 ≫ jP →
      ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
        q ∈ Set.range Θ.base := by
    intro Θ sh _ hgen q hq
    have hq' : q ∈ Set.range jP.base := by rw [range_fst_specGenericFibreInclusion]; exact hq
    obtain ⟨q₀, rfl⟩ := hq'
    obtain ⟨q₁, rfl⟩ := (Scheme.homeoOfIso (asIso sh.1)).surjective q₀
    obtain ⟨w₀, hw₀⟩ := hrange_gfr q₁
    refine ⟨jW.base w₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, hgen, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw₀]
    rfl
  have hgenΦ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
      q ∈ Set.range Φ.base := hgen_of Φ (shL K f LXK e) hΦgen
  have hgenΨ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R →
      q ∈ Set.range Ψ.base := hgen_of Ψ (shR K f LXK e) hΨgen

  let Z : (pullback f f).Opens := W ⊓ Φ.opensRange ⊓ Ψ.opensRange
  have hZcoe : (Z : Set ↑(pullback f f)) = Set.range W.ι.base ∩ Set.range Φ.base ∩ Set.range Ψ.base := by
    simp only [Z, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]
  have hZmax : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z := by
    intro p h1 h2
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hW₂ p h1 h2, ?_⟩, ?_⟩
    · exact hΦ₂ p h1 h2
    · exact hΨ₂ p h1 h2
  have hZgen : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ Z := by
    intro p hp
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨hW₁ p hp, ?_⟩, ?_⟩
    · exact hgenΦ p hp
    · exact hgenΨ p hp
  let Z' : (pullback f f).Opens := σ ⁻¹ᵁ Z
  have hZ'max : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z' := by
    intro p h1 h2
    have h := σmax p ⟨h1, h2⟩
    exact hZmax _ h.1 h.2

  let F₁ : X → Set ↑(pullback f f) := fun a => {q | (pullback.fst f f).base q = a}
  let F₂ : X → Set ↑(pullback f f) := fun a => {q | (pullback.snd f f).base q = a}
  let G : Set X := {a | DenseIn (Z : Set ↑(pullback f f)) (F₁ a) ∧ DenseIn (Z : Set ↑(pullback f f)) (F₂ a)}
  let X' : X.Opens := ⟨interior G, isOpen_interior⟩
  have hX'G : ∀ a, a ∈ X' → a ∈ G := fun a ha => interior_subset ha

  have hGgen : ∀ a : X, f.base a ≠ IsLocalRing.closedPoint R → a ∈ G := by
    intro a ha
    constructor
    · refine DenseIn.of_subset fun q hq => hZgen q ?_
      rw [hpf]; change (pullback.fst f f).base q = a at hq; rw [hq]; exact ha
    · refine DenseIn.of_subset fun q hq => hZgen q ?_
      rw [hpf, hcond]; change (pullback.snd f f).base q = a at hq; rw [hq]; exact ha
  have hopen_gen : IsOpen {a : X | f.base a ≠ IsLocalRing.closedPoint R} := by
    have : IsClosed {a : X | f.base a = IsLocalRing.closedPoint R} :=
      (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
    simpa [Set.compl_setOf] using this.isOpen_compl
  have hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X' := by
    intro x hx
    exact interior_maximal (fun a (ha : a ∈ {a : X | f.base a ≠ IsLocalRing.closedPoint R}) => hGgen a ha)
      hopen_gen hx

  have hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X' := by
    intro ξ hξ hξmax
    obtain ⟨N₁, hξN₁, hN₁⟩ :=
      NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem f Z hZmax ξ hξ hξmax
    obtain ⟨N₂, hξN₂, hN₂⟩ :=
      NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem f Z' hZ'max ξ hξ hξmax
    change ξ ∈ interior G
    rw [mem_interior]
    refine ⟨(N₁ : Set X) ∩ (N₂ : Set X), ?_, N₁.2.inter N₂.2, ⟨hξN₁, hξN₂⟩⟩
    rintro a ⟨ha₁, ha₂⟩
    by_cases has : f.base a = IsLocalRing.closedPoint R
    · constructor
      · exact (denseIn_setOf_iff (p := fun q => (pullback.fst f f).base q = a) (Z : Set ↑(pullback f f))).mpr
          (hN₁ a ha₁ has)
      · have h := (denseIn_setOf_iff (p := fun q => (pullback.fst f f).base q = a)
          (Z' : Set ↑(pullback f f))).mpr (hN₂ a ha₂ has)
        have h' := h.image_homeomorph σh
        rw [σF a] at h'
        refine h'.mono ?_
        rintro _ ⟨q, hq, rfl⟩
        exact hq
    · exact hGgen a has

  have hsndmax : ∀ (a : X), f.base a = IsLocalRing.closedPoint R → ∀ θ : ↑(pullback f f),
      (pullback.fst f f).base θ = a →
      (∀ y : ↑(pullback f f), (pullback.fst f f).base y = a → y ⤳ θ → y = θ) →
      (pullback.snd f f).base θ ∈ X' := by
    intro a ha θ hθa hθmax
    apply hX'₂
    · rw [← hcond, hθa]; exact ha
    · intro y hy hys
      obtain ⟨θ', hθ'θ, hθ'a, hθ'y⟩ :=
        NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd f θ (by rw [hθa]; exact ha) y hy hys
      rw [← hθ'y, hθmax θ' (hθ'a.trans hθa) hθ'θ]
  have hD₃ : ∀ a : X, a ∈ X' → DenseIn ((fun q => (pullback.snd f f).base q) ⁻¹' (X' : Set X)) (F₁ a) := by
    intro a ha
    by_cases has : f.base a = IsLocalRing.closedPoint R
    · apply DenseIn.of_forall_exists_specializes
      intro q hq
      obtain ⟨θ, hθa, hθq, hθmax⟩ := exists_fibre_maximal (pullback.fst f f) q
      change (pullback.fst f f).base q = a at hq
      rw [hq] at hθa hθmax
      exact ⟨θ, hθa, hsndmax a has θ hθa hθmax, hθq⟩
    · refine DenseIn.of_subset fun q hq => hX'₁ _ ?_
      change (pullback.fst f f).base q = a at hq
      rw [← hcond, hq]; exact has
  have hD₄ : ∀ a : X, a ∈ X' → DenseIn ((fun q => (pullback.fst f f).base q) ⁻¹' (X' : Set X)) (F₂ a) := by
    intro a ha
    have h := (hD₃ a ha).image_homeomorph σh
    rwa [σF a, σpre] at h

  let UWo : (W : Scheme.{u}).Opens := (W.ι ≫ pullback.fst f f) ⁻¹ᵁ X' ⊓ (W.ι ≫ pullback.snd f f) ⁻¹ᵁ X' ⊓ m.1 ⁻¹ᵁ X'
  let U : (pullback f f).Opens := W.ι ''ᵁ UWo
  have hUcoe : (U : Set ↑(pullback f f)) = W.ι.base '' (UWo : Set ↑W) := rfl
  have hUWo : ∀ w : ↑W, w ∈ UWo ↔ (pullback.fst f f).base (W.ι.base w) ∈ X' ∧
      (pullback.snd f f).base (W.ι.base w) ∈ X' ∧ m.1.base w ∈ X' := by
    intro w
    simp only [UWo, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have hUWocoe : (UWo : Set ↑W) = {w | (pullback.fst f f).base (W.ι.base w) ∈ (X' : Set X) ∧
      (pullback.snd f f).base (W.ι.base w) ∈ (X' : Set X) ∧ m.1.base w ∈ (X' : Set X)} := by
    ext w; exact hUWo w
  have hUW : U ≤ W := by
    rintro _ ⟨w, -, rfl⟩; exact w.2
  have hmemU : ∀ q : ↑(pullback f f), q ∈ U ↔ ∃ h : q ∈ W, (⟨q, h⟩ : ↑W) ∈ UWo := by
    intro q; constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, by simp at hw; exact hw⟩
    · rintro ⟨h, hw⟩; exact ⟨⟨q, h⟩, hw, rfl⟩
  have hU₃ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U := by
    intro q hq
    rw [hmemU]
    refine ⟨hW₁ q hq, (hUWo _).mpr ⟨hX'₁ _ ?_, hX'₁ _ ?_, hX'₁ _ ?_⟩⟩
    · rw [← hpf]; exact hq
    · change f.base ((pullback.snd f f).base q) ≠ _
      rw [← hcond, ← hpf]; exact hq
    · rw [hmover, ← hpf]; exact hq
  have hU₄ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X' := by
    intro q hq
    obtain ⟨h, hw⟩ := (hmemU q).mp hq
    exact (hUWo _).mp hw
  have hpreU : {w : ↑W | W.ι.base w ∈ U} = (UWo : Set ↑W) := by
    ext w
    constructor
    · rintro ⟨w', hw', h⟩
      have : w' = w := W.ι.isOpenEmbedding.injective h
      rw [← this]; exact hw'
    · intro hw; exact ⟨w, hw, rfl⟩

  have hsix : ∀ a : X, a ∈ X' →
      DenseIn (U : Set ↑(pullback f f)) (F₁ a) ∧ DenseIn (U : Set ↑(pullback f f)) (F₂ a) ∧
      DenseIn (Φ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₁ a) ∧ DenseIn (Φ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₂ a) ∧
      DenseIn (Ψ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₁ a) ∧ DenseIn (Ψ.base '' {w : ↑W | W.ι.base w ∈ U}) (F₂ a) := by
    intro a ha
    have hG := hX'G a ha
    rw [hpreU, hUcoe, hUWocoe]
    have key := six_denseIn (P := ↑(pullback f f)) (X := ↑X) (W := ↑W)
      (fun q => (pullback.fst f f).base q) (fun q => (pullback.snd f f).base q)
      (pullback.fst f f).continuous (pullback.snd f f).continuous
      (fun w => W.ι.base w) W.ι.isOpenEmbedding (fun w => m.1.base w) m.1.continuous
      (fun w => Φ.base w) (fun w => Ψ.base w) Φ.isOpenEmbedding.isInducing Ψ.isOpenEmbedding.isInducing
      Φfst' Φsnd' Ψfst' Ψsnd' (X' : Set X) X'.2 a ha
      (by rw [← hZcoe]; exact hG.1) (by rw [← hZcoe]; exact hG.2) (hD₃ a ha) (hD₄ a ha)
    exact key

  refine ⟨X', U, hUW, hX'₁, hX'₂, hU₃, hU₄, fun x hx => ?_⟩
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hsix x hx
  exact ⟨(denseIn_setOf_iff _).mp d₁, (denseIn_setOf_iff _).mp d₂, (denseIn_setOf_iff _).mp d₃,
    (denseIn_setOf_iff _).mp d₄, (denseIn_setOf_iff _).mp d₅, (denseIn_setOf_iff _).mp d₆⟩

end Main

end P2mStrictify
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul.P2mStrictify"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
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
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      (∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U) ∧
      (∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
        m.1.base ⟨q, hUW hq⟩ ∈ X') ∧
      (∀ x : X, x ∈ X' →
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
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :=
  P2mStrictify.main K LXK f e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂

end
end S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul (solution)

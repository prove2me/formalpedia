-- Prove2me | solution 1 for NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9b3f5bfa-374f-5c94-9413-c369fbbd3b64

import Mathlib
import Theorems.Thm_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd
import Theorems.Thm_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le
import Theorems.Thm_Algebra_TensorProduct_trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TensorProduct

universe u

namespace P2mDenseSliceLocus

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

end MaxGen

section Chart

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (A A' : Type u) [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
variable (u : Spec (CommRingCat.of A) ⟶ X) (u' : Spec (CommRingCat.of A') ⟶ X)
variable [IsOpenImmersion u] [IsOpenImmersion u']
variable (hu : u ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
variable (hu' : u' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A')))

def chart : Spec (CommRingCat.of (A ⊗[R] A')) ⟶ pullback f f :=
  (pullbackSpecIso R A A').inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      f f u u' (𝟙 _) (by rw [Category.comp_id, hu]) (by rw [Category.comp_id, hu'])

include hu hu' in
theorem isOpenImmersion_chart : IsOpenImmersion (chart f A A' u u' hu hu') := by
  unfold chart
  have := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (f := Spec.map (CommRingCat.ofHom (algebraMap R A))) (g := Spec.map (CommRingCat.ofHom (algebraMap R A')))
    (f' := f) (g' := f) (i₁ := u) (i₂ := u') inferInstance inferInstance hu.symm hu'.symm
  infer_instance

theorem chart_fst : chart f A A' u u' hu hu' ≫ pullback.fst f f =
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] A'))) ≫ u := by
  simp only [chart, Category.assoc, pullback.lift_fst]
  rw [pullbackSpecIso_inv_fst'_assoc]

theorem chart_snd : chart f A A' u u' hu hu' ≫ pullback.snd f f =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom) ≫ u' := by
  simp only [chart, Category.assoc, pullback.lift_snd]
  rw [pullbackSpecIso_inv_snd_assoc]
  rfl

theorem chart_fst_apply (𝔓 : ↑(Spec (CommRingCat.of (A ⊗[R] A')))) :
    (pullback.fst f f).base ((chart f A A' u u' hu hu').base 𝔓) = u.base ⟨𝔓.asIdeal.under A, inferInstance⟩ := by
  rw [← Scheme.Hom.comp_apply, chart_fst, Scheme.Hom.comp_apply]
  rfl

theorem chart_snd_apply (𝔓 : ↑(Spec (CommRingCat.of (A ⊗[R] A')))) :
    (pullback.snd f f).base ((chart f A A' u u' hu hu').base 𝔓) =
      u'.base ⟨𝔓.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom,
        inferInstance⟩ := by
  rw [← Scheme.Hom.comp_apply, chart_snd, Scheme.Hom.comp_apply]
  rfl

theorem range_chart : Set.range (chart f A A' u u' hu hu').base =
    {q | (pullback.fst f f).base q ∈ Set.range u.base ∧ (pullback.snd f f).base q ∈ Set.range u'.base} := by
  have h := Scheme.Pullback.range_map (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A'))) f f u u' (𝟙 _)
    (by rw [Category.comp_id, hu]) (by rw [Category.comp_id, hu'])
  unfold chart
  have : ∀ {P Q S : Scheme.{u}} (α : P ⟶ Q) (β : Q ⟶ S),
      Set.range (α ≫ β).base = β.base '' Set.range α.base := by
    intro P Q S α β; rw [← Set.range_comp]; rfl
  rw [this, (show Function.Surjective (pullbackSpecIso R A A').inv.base from
      (Scheme.homeoOfIso (pullbackSpecIso R A A').symm).surjective).range_eq, Set.image_univ, h]
  ext q
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]

include hu in
theorem f_u_apply (p : ↑(Spec (CommRingCat.of A))) :
    f.base (u.base p) = ⟨p.asIdeal.under R, inferInstance⟩ := by
  rw [← Scheme.Hom.comp_apply, hu]
  rfl

include hu' in
theorem f_u'_apply (p : ↑(Spec (CommRingCat.of A'))) :
    f.base (u'.base p) = ⟨p.asIdeal.under R, inferInstance⟩ := by
  rw [← Scheme.Hom.comp_apply, hu']
  rfl

theorem chart_specializes_iff (𝔓 𝔔 : ↑(Spec (CommRingCat.of (A ⊗[R] A')))) :
    (chart f A A' u u' hu hu').base 𝔓 ⤳ (chart f A A' u u' hu hu').base 𝔔 ↔ 𝔓.asIdeal ≤ 𝔔.asIdeal := by
  haveI := isOpenImmersion_chart f A A' u u' hu hu'
  rw [(chart f A A' u u' hu hu').isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes 𝔓 𝔔).symm

theorem mem_range_chart_of_specializes {y : ↑(pullback f f)} {𝔓 : ↑(Spec (CommRingCat.of (A ⊗[R] A')))}
    (h : y ⤳ (chart f A A' u u' hu hu').base 𝔓) : y ∈ Set.range (chart f A A' u u' hu hu').base := by
  haveI := isOpenImmersion_chart f A A' u u' hu hu'
  exact h.mem_open (chart f A A' u u' hu hu').isOpenEmbedding.isOpen_range ⟨𝔓, rfl⟩

theorem fibreMax_iff (𝔓 : ↑(Spec (CommRingCat.of (A ⊗[R] A')))) :
    (∀ y : ↑(pullback f f), (pullback.fst f f).base y = (pullback.fst f f).base ((chart f A A' u u' hu hu').base 𝔓) →
      y ⤳ (chart f A A' u u' hu hu').base 𝔓 → y = (chart f A A' u u' hu hu').base 𝔓) ↔
    𝔓.asIdeal ∈ ((𝔓.asIdeal.under A).map (algebraMap A (A ⊗[R] A'))).minimalPrimes := by
  haveI := isOpenImmersion_chart f A A' u u' hu hu'
  constructor
  · intro hmax
    refine ⟨⟨𝔓.2, Ideal.map_le_iff_le_comap.mpr le_rfl⟩, ?_⟩
    rintro Q ⟨hQ, hIQ⟩ hQ𝔓
    haveI := hQ
    let 𝔔 : ↑(Spec (CommRingCat.of (A ⊗[R] A'))) := ⟨Q, hQ⟩
    have hspec : (chart f A A' u u' hu hu').base 𝔔 ⤳ (chart f A A' u u' hu hu').base 𝔓 :=
      (chart_specializes_iff f A A' u u' hu hu' 𝔔 𝔓).mpr hQ𝔓
    have hunder : Q.under A = 𝔓.asIdeal.under A :=
      le_antisymm (Ideal.comap_mono hQ𝔓) (Ideal.map_le_iff_le_comap.mp hIQ)
    have hfst : (pullback.fst f f).base ((chart f A A' u u' hu hu').base 𝔔) =
        (pullback.fst f f).base ((chart f A A' u u' hu hu').base 𝔓) := by
      rw [chart_fst_apply, chart_fst_apply]
      exact congrArg u.base (PrimeSpectrum.ext hunder)
    have h := hmax _ hfst hspec
    have h' : 𝔔 = 𝔓 := (chart f A A' u u' hu hu').isOpenEmbedding.injective h
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal h').symm
  · rintro ⟨-, hmin⟩ y hy hyθ
    obtain ⟨𝔔, rfl⟩ := mem_range_chart_of_specializes f A A' u u' hu hu' hyθ
    have hle : 𝔔.asIdeal ≤ 𝔓.asIdeal := (chart_specializes_iff f A A' u u' hu hu' 𝔔 𝔓).mp hyθ
    rw [chart_fst_apply, chart_fst_apply] at hy
    have hunder : 𝔔.asIdeal.under A = 𝔓.asIdeal.under A :=
      congrArg PrimeSpectrum.asIdeal (u.isOpenEmbedding.injective hy)
    have hI : (𝔓.asIdeal.under A).map (algebraMap A (A ⊗[R] A')) ≤ 𝔔.asIdeal :=
      Ideal.map_le_iff_le_comap.mpr (le_of_eq hunder.symm)
    have hge := hmin ⟨𝔔.2, hI⟩ hle
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hle hge)

include hu' in

theorem mem_minimalPrimes_of_spMax (p : ↑(Spec (CommRingCat.of A')))
    (hp : f.base (u'.base p) = IsLocalRing.closedPoint R)
    (hmax : ∀ y : X, y ⤳ u'.base p → f.base y = IsLocalRing.closedPoint R → y = u'.base p) :
    p.asIdeal ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A')).minimalPrimes := by
  have hpR : p.asIdeal.under R = IsLocalRing.maximalIdeal R := by
    rw [f_u'_apply f A' u' hu'] at hp
    exact congrArg PrimeSpectrum.asIdeal hp
  refine ⟨⟨p.2, Ideal.map_le_iff_le_comap.mpr (le_of_eq hpR.symm)⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hQp
  haveI := hQ
  let 𝔔 : ↑(Spec (CommRingCat.of A')) := ⟨Q, hQ⟩
  have hspec : u'.base 𝔔 ⤳ u'.base p :=
    (((PrimeSpectrum.le_iff_specializes 𝔔 p).mp hQp).map u'.continuous)
  have hQR : Q.under R = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    exact Ideal.map_le_iff_le_comap.mp hIQ
  have hfy : f.base (u'.base 𝔔) = IsLocalRing.closedPoint R := by
    rw [f_u'_apply f A' u' hu']
    exact PrimeSpectrum.ext hQR
  have h := hmax _ hspec hfy
  have h' : 𝔔 = p := u'.isOpenEmbedding.injective h
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal h').symm

omit [IsLocalRing R] in

theorem trdeg_congr_ideal {I J : Ideal A'} [I.IsPrime] [J.IsPrime] (h : I = J) :
    Algebra.trdeg (R ⧸ I.under R) (A' ⧸ I) = Algebra.trdeg (R ⧸ J.under R) (A' ⧸ J) := by
  subst h; rfl

theorem chart_lemma [Algebra.FiniteType R A] [Algebra.FiniteType R A']
    (c : ↑(pullback f f)) (hc : c ∈ Set.range (chart f A A' u u' hu hu').base)
    (hcs : f.base ((pullback.fst f f).base c) = IsLocalRing.closedPoint R) :
    ∃ T : X.Opens, (pullback.fst f f).base c ∈ T ∧
      ∀ θ : ↑(pullback f f), θ ∈ Set.range (chart f A A' u u' hu hu').base → c ⤳ θ →
        (pullback.fst f f).base θ ∈ T →
        (∀ y : ↑(pullback f f), (pullback.fst f f).base y = (pullback.fst f f).base θ → y ⤳ θ → y = θ) →
        f.base ((pullback.snd f f).base θ) = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ (pullback.snd f f).base θ → f.base y = IsLocalRing.closedPoint R →
          y = (pullback.snd f f).base θ) →
        ∀ y : ↑(pullback f f), (pullback.fst f f).base y = (pullback.fst f f).base c → y ⤳ c → y = c := by
  classical
  haveI := isOpenImmersion_chart f A A' u u' hu hu'
  obtain ⟨𝔓c, rfl⟩ := hc
  set χ := chart f A A' u u' hu hu' with hχ
  set B := A ⊗[R] A' with hB
  let inR : A' →+* B := (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A')).toRingHom

  obtain ⟨s, hs, hbound⟩ :=
    Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le (A := A) (B := B) 𝔓c.asIdeal
  let T : X.Opens := u ''ᵁ (PrimeSpectrum.basicOpen s)
  refine ⟨T, ?_, ?_⟩
  · rw [chart_fst_apply]
    exact ⟨⟨𝔓c.asIdeal.under A, inferInstance⟩, hs, rfl⟩
  intro θ hθ hcθ hθT hθmax hζs hζmax
  obtain ⟨𝔓θ, rfl⟩ := hθ
  have hle : 𝔓c.asIdeal ≤ 𝔓θ.asIdeal := (chart_specializes_iff f A A' u u' hu hu' _ _).mp hcθ

  have hsθ : s ∉ 𝔓θ.asIdeal.under A := by
    rw [chart_fst_apply] at hθT
    obtain ⟨p, hp, hpeq⟩ := hθT
    have : p = ⟨𝔓θ.asIdeal.under A, inferInstance⟩ := u.isOpenEmbedding.injective hpeq
    subst this
    exact hp

  have hθR : 𝔓θ.asIdeal.under R = IsLocalRing.maximalIdeal R := by
    have h1 : f.base ((pullback.fst f f).base (χ.base 𝔓θ)) = IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]; exact hζs
    rw [chart_fst_apply, f_u_apply f A u hu] at h1
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    change (𝔓θ.asIdeal.under A).under R = _ at h2
    rwa [Ideal.under_under] at h2
  have hcR : 𝔓c.asIdeal.under R = IsLocalRing.maximalIdeal R := by
    rw [chart_fst_apply, f_u_apply f A u hu] at hcs
    have h2 := congrArg PrimeSpectrum.asIdeal hcs
    change (𝔓c.asIdeal.under A).under R = _ at h2
    rwa [Ideal.under_under] at h2

  set 𝔭'θ : Ideal A' := 𝔓θ.asIdeal.comap inR with h𝔭'θ
  set 𝔭'c : Ideal A' := 𝔓c.asIdeal.comap inR with h𝔭'c
  have hζ : (pullback.snd f f).base (χ.base 𝔓θ) = u'.base ⟨𝔭'θ, inferInstance⟩ := chart_snd_apply f A A' u u' hu hu' _
  have hmin' : 𝔭'θ ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A')).minimalPrimes := by
    apply mem_minimalPrimes_of_spMax f A' u' hu' ⟨𝔭'θ, inferInstance⟩
    · rw [← hζ]; exact hζs
    · rw [← hζ]; exact hζmax
  have h𝔭'cR : 𝔭'c.under R = IsLocalRing.maximalIdeal R := by
    rw [h𝔭'c, Ideal.under, Ideal.comap_comap]
    have : inR.comp (algebraMap R A') = algebraMap R B := by
      ext r
      change (1 : A) ⊗ₜ[R] (algebraMap R A' r) = algebraMap R B r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [this]; exact hcR
  have heq' : 𝔭'c = 𝔭'θ := by
    have hle' : 𝔭'c ≤ 𝔭'θ := Ideal.comap_mono hle
    refine le_antisymm hle' (hmin'.2 ⟨inferInstance, ?_⟩ hle')
    exact Ideal.map_le_iff_le_comap.mpr (le_of_eq h𝔭'cR.symm)

  have hθunderR : (𝔓θ.asIdeal.under R).map (algebraMap R A') = (IsLocalRing.maximalIdeal R).map (algebraMap R A') := by
    rw [hθR]
  have hcunderR : (𝔓c.asIdeal.under R).map (algebraMap R A') = (IsLocalRing.maximalIdeal R).map (algebraMap R A') := by
    rw [hcR]
  have Aθ := Algebra.TensorProduct.trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    (R := R) (A := A) (A' := A') 𝔓θ.asIdeal (by rw [hθunderR]; exact hmin')
  have Ac := Algebra.TensorProduct.trdeg_quotient_le_and_mem_minimalPrimes_iff_of_mem_minimalPrimes
    (R := R) (A := A) (A' := A') 𝔓c.asIdeal (by rw [hcunderR]; change 𝔭'c ∈ _; rw [heq']; exact hmin')

  have hθmin : 𝔓θ.asIdeal ∈ ((𝔓θ.asIdeal.under A).map (algebraMap A B)).minimalPrimes :=
    (fibreMax_iff f A A' u u' hu hu' 𝔓θ).mp hθmax
  have e1 : Algebra.trdeg (A ⧸ 𝔓θ.asIdeal.under A) (B ⧸ 𝔓θ.asIdeal) =
      Algebra.trdeg (R ⧸ 𝔭'θ.under R) (A' ⧸ 𝔭'θ) := Aθ.2.mp hθmin
  have e2 : Algebra.trdeg (A ⧸ 𝔓c.asIdeal.under A) (B ⧸ 𝔓c.asIdeal) ≤
      Algebra.trdeg (R ⧸ 𝔭'c.under R) (A' ⧸ 𝔭'c) := Ac.1
  have e3 : Algebra.trdeg (A ⧸ 𝔓θ.asIdeal.under A) (B ⧸ 𝔓θ.asIdeal) ≤
      Algebra.trdeg (A ⧸ 𝔓c.asIdeal.under A) (B ⧸ 𝔓c.asIdeal) := hbound 𝔓θ.asIdeal hle hsθ
  have e4 : Algebra.trdeg (R ⧸ 𝔭'c.under R) (A' ⧸ 𝔭'c) = Algebra.trdeg (R ⧸ 𝔭'θ.under R) (A' ⧸ 𝔭'θ) :=
    trdeg_congr_ideal (R := R) A' heq'
  have hceq : Algebra.trdeg (A ⧸ 𝔓c.asIdeal.under A) (B ⧸ 𝔓c.asIdeal) =
      Algebra.trdeg (R ⧸ 𝔭'c.under R) (A' ⧸ 𝔭'c) := by
    apply le_antisymm e2
    rw [e4, ← e1]
    exact e3
  have hcmin : 𝔓c.asIdeal ∈ ((𝔓c.asIdeal.under A).map (algebraMap A B)).minimalPrimes := Ac.2.mpr hceq
  exact (fibreMax_iff f A A' u u' hu hu' 𝔓c).mpr hcmin

end Chart

section Main

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def SpMax {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) (x : P) : Prop :=
  p.base x = IsLocalRing.closedPoint R ∧ ∀ y : P, y ⤳ x → p.base y = IsLocalRing.closedPoint R → y = x

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : (pullback f f).Opens)
    (hZ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z)
    (ξ : X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ) :
    ∃ N : X.Opens, ξ ∈ N ∧ ∀ a : X, a ∈ N → f.base a = IsLocalRing.closedPoint R →
      Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = a} → ↑(pullback f f)) ⁻¹'
        (Z : Set ↑(pullback f f))) := by
  classical
  have _hξs := hξ
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsLocallyNoetherian (pullback f f) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  haveI : CompactSpace ↑(pullback f f) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f ≫ f)
  haveI : IsNoetherian (pullback f f) := {}
  set g := pullback.fst f f with hg
  set g' := pullback.snd f f with hg'
  have hpf : ∀ q : ↑(pullback f f), (g ≫ f).base q = f.base (g.base q) := fun q => Scheme.Hom.comp_apply _ _ q
  have hcond : ∀ q : ↑(pullback f f), f.base (g.base q) = f.base (g'.base q) :=
    fun q => by rw [← Scheme.Hom.comp_apply, hg, pullback.condition, Scheme.Hom.comp_apply]

  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, (Set.univ : Set X) ⊆ ⋃ V ∈ t, ((V : X.Opens) : Set X) := by
    refine isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
      (fun V => (V : X.Opens).2) fun x _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  have hcov : ∀ x : X, ∃ V ∈ t, x ∈ (V : X.Opens) := by
    intro x
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨V, hV, hxV⟩

  let φ : ∀ V : X.affineOpens, CommRingCat.of R ⟶ Γ(X, V) := fun V => Spec.preimage (V.2.fromSpec ≫ f)
  have HVW : ∀ V W : X.affineOpens, ∀ c : ↑(pullback f f), g.base c ∈ (V : X.Opens) → g'.base c ∈ (W : X.Opens) →
      f.base (g.base c) = IsLocalRing.closedPoint R →
      ∃ T : X.Opens, g.base c ∈ T ∧ ∀ θ : ↑(pullback f f), g.base θ ∈ (V : X.Opens) → g'.base θ ∈ (W : X.Opens) →
        c ⤳ θ → g.base θ ∈ T →
        (∀ y : ↑(pullback f f), g.base y = g.base θ → y ⤳ θ → y = θ) →
        f.base (g'.base θ) = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ g'.base θ → f.base y = IsLocalRing.closedPoint R → y = g'.base θ) →
        ∀ y : ↑(pullback f f), g.base y = g.base c → y ⤳ c → y = c := by
    intro V W c hcV hcW hcs
    letI algV : Algebra R Γ(X, V) := (φ V).hom.toAlgebra
    letI algW : Algebra R Γ(X, W) := (φ W).hom.toAlgebra
    have huV : V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) := by
      rw [show CommRingCat.ofHom (algebraMap R Γ(X, V)) = φ V from rfl, Spec.map_preimage]
    have huW : W.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, W))) := by
      rw [show CommRingCat.ofHom (algebraMap R Γ(X, W)) = φ W from rfl, Spec.map_preimage]
    haveI : Algebra.FiniteType R Γ(X, V) := by
      have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V)))) := by
        rw [← huV]; infer_instance
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
      exact RingHom.finiteType_algebraMap.mp h
    haveI : Algebra.FiniteType R Γ(X, W) := by
      have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, W)))) := by
        rw [← huW]; infer_instance
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
      exact RingHom.finiteType_algebraMap.mp h
    have hrange : ∀ q : ↑(pullback f f), g.base q ∈ (V : X.Opens) → g'.base q ∈ (W : X.Opens) →
        q ∈ Set.range (chart f Γ(X, V) Γ(X, W) V.2.fromSpec W.2.fromSpec huV huW).base := by
      intro q h1 h2
      rw [range_chart]
      exact ⟨by rw [IsAffineOpen.range_fromSpec]; exact h1, by rw [IsAffineOpen.range_fromSpec]; exact h2⟩
    obtain ⟨T, hcT, hT⟩ := chart_lemma f Γ(X, V) Γ(X, W) V.2.fromSpec W.2.fromSpec huV huW c (hrange c hcV hcW) hcs
    exact ⟨T, hcT, fun θ hθV hθW => hT θ (hrange θ hθV hθW)⟩
  choose Tof hTof₁ hTof₂ using HVW

  let C : Set ↑(pullback f f) := {q | (g ≫ f).base q = IsLocalRing.closedPoint R} \ (Z : Set ↑(pullback f f))
  have hCclosed : IsClosed C :=
    ((IsLocalRing.isClosed_singleton_closedPoint R).preimage (g ≫ f).continuous).sdiff Z.2
  haveI : TopologicalSpace.NoetherianSpace ↥C := TopologicalSpace.NoetherianSpace.set C
  let comps : Set (Set ↥C) := irreducibleComponents ↥C
  have hcomps : comps.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

  have hgen : ∀ K ∈ comps, ∃ c : ↑(pullback f f), c ∈ C ∧ IsGenericPoint c (closure (Subtype.val '' K)) := by
    intro K hK
    have hirr : IsIrreducible (Subtype.val '' K) := hK.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨c, hc⟩ := QuasiSober.sober hirr.closure isClosed_closure
    refine ⟨c, ?_, hc⟩
    have : closure (Subtype.val '' K) ⊆ C := closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hCclosed
    exact this hc.mem
  choose cgen hcgenC hcgen using hgen
  have hcgen_spec : ∀ θ ∈ C, ∃ (K : Set ↥C) (hK : K ∈ comps), cgen K hK ⤳ θ := by
    intro θ hθ
    refine ⟨irreducibleComponent (⟨θ, hθ⟩ : ↥C), irreducibleComponent_mem_irreducibleComponents _, ?_⟩
    exact (hcgen _ _).specializes (subset_closure ⟨⟨θ, hθ⟩, mem_irreducibleComponent, rfl⟩)

  let Bad : ∀ (K : Set ↥C), K ∈ comps → Set X := fun K hK =>
    if g.base (cgen K hK) = ξ then
      ⋃ V ∈ t, ⋃ W ∈ t, if h : g.base (cgen K hK) ∈ (V : X.Opens) ∧ g'.base (cgen K hK) ∈ (W : X.Opens) then
        ((Tof V W (cgen K hK) h.1 h.2 (by rw [← hpf]; exact (hcgenC K hK).1) : X.Opens) : Set X)ᶜ else ∅
    else closure {g.base (cgen K hK)}
  have hBadclosed : ∀ K hK, IsClosed (Bad K hK) := by
    intro K hK
    simp only [Bad]
    split_ifs with h
    · refine Set.Finite.isClosed_biUnion t.finite_toSet fun V _ => ?_
      refine Set.Finite.isClosed_biUnion t.finite_toSet fun W _ => ?_
      split_ifs
      · exact (TopologicalSpace.Opens.isOpen _).isClosed_compl
      · exact isClosed_empty
    · exact isClosed_closure
  have hξBad : ∀ K hK, ξ ∉ Bad K hK := by
    intro K hK hξK
    simp only [Bad] at hξK
    split_ifs at hξK with h
    · simp only [Set.mem_iUnion] at hξK
      obtain ⟨V, hV, W, hW, hξVW⟩ := hξK
      split_ifs at hξVW with h'
      · apply hξVW
        rw [← h]
        exact hTof₁ V W (cgen K hK) h'.1 h'.2 _
      · exact hξVW
    ·
      have hspec : g.base (cgen K hK) ⤳ ξ := by
        rw [specializes_iff_mem_closure]; exact hξK
      exact h (hξmax _ hspec (by rw [← hpf]; exact (hcgenC K hK).1))
  let Nset : Set X := (⋃ K ∈ comps, if hK : K ∈ comps then Bad K hK else ∅)ᶜ
  have hNopen : IsOpen Nset := by
    refine (Set.Finite.isClosed_biUnion hcomps fun K hK => ?_).isOpen_compl
    rw [dif_pos hK]; exact hBadclosed K hK
  have hξN : ξ ∈ Nset := by
    simp only [Nset, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro K hK
    rw [dif_pos hK]; exact hξBad K hK
  have hNBad : ∀ a ∈ Nset, ∀ K hK, a ∉ Bad K hK := by
    intro a ha K hK haK
    apply ha
    simp only [Set.mem_iUnion]
    exact ⟨K, hK, by rw [dif_pos hK]; exact haK⟩
  refine ⟨⟨Nset, hNopen⟩, hξN, ?_⟩

  intro a ha has
  change a ∈ Nset at ha

  suffices key : ∀ θ : ↑(pullback f f), g.base θ = a →
      (∀ y : ↑(pullback f f), g.base y = a → y ⤳ θ → y = θ) → θ ∈ Z by
    have key' : Dense ((Subtype.val : ↥({q : ↑(pullback f f) | g.base q = a} : Set ↑(pullback f f)) →
        ↑(pullback f f)) ⁻¹' (Z : Set ↑(pullback f f))) := by
      rw [Subtype.dense_iff]
      rintro q (hq : g.base q = a)
      obtain ⟨θ, hθa, hθq, hθmax⟩ := exists_fibre_maximal g q
      rw [hq] at hθa hθmax
      have hθZ := key θ hθa hθmax
      have : q ∈ closure {θ} := hθq.mem_closure
      refine closure_mono ?_ this
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact ⟨⟨θ, hθa⟩, hθZ, rfl⟩
    exact key'
  intro θ hθa hθmax
  by_contra hθZ

  have hθs : (g ≫ f).base θ = IsLocalRing.closedPoint R := by rw [hpf, hθa]; exact has
  have hθC : θ ∈ C := ⟨hθs, hθZ⟩
  obtain ⟨K, hK, hcθ⟩ := hcgen_spec θ hθC
  set c := cgen K hK with hc

  have hζs : f.base (g'.base θ) = IsLocalRing.closedPoint R := by rw [← hcond, hθa]; exact has
  have hζmax : ∀ y : X, y ⤳ g'.base θ → f.base y = IsLocalRing.closedPoint R → y = g'.base θ := by
    intro y hy hys
    obtain ⟨θ', hθ'θ, hθ'a, hθ'y⟩ :=
      NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd f θ (by rw [← hg, hθa]; exact has) y hy hys
    rw [← hθ'y, hθmax θ' (hθ'a.trans hθa) hθ'θ]

  obtain ⟨V, hV, hθV⟩ := hcov (g.base θ)
  obtain ⟨W, hW, hθW⟩ := hcov (g'.base θ)
  have hcV : g.base c ∈ (V : X.Opens) := (hcθ.map g.continuous).mem_open (V : X.Opens).2 hθV
  have hcW : g'.base c ∈ (W : X.Opens) := (hcθ.map g'.continuous).mem_open (W : X.Opens).2 hθW
  have hcs : f.base (g.base c) = IsLocalRing.closedPoint R := by rw [← hpf]; exact (hcgenC K hK).1
  have haBad : a ∉ Bad K hK := hNBad a ha K hK
  by_cases hcξ : g.base c = ξ
  ·
    have haT : g.base θ ∈ Tof V W c hcV hcW hcs := by
      by_contra hnot
      apply haBad
      simp only [Bad, ← hc, if_pos hcξ, Set.mem_iUnion]
      refine ⟨V, hV, W, hW, ?_⟩
      rw [dif_pos ⟨hcV, hcW⟩]
      rw [← hθa]; exact hnot
    have hcmax := hTof₂ V W c hcV hcW hcs θ hθV hθW hcθ haT
      (by rw [hθa]; exact hθmax) hζs hζmax

    have hcZ : c ∈ Z := by
      refine hZ c (hcgenC K hK).1 fun y hy hys => hcmax y ?_ hy
      have h1 : g.base y ⤳ g.base c := hy.map g.continuous
      rw [hcξ] at h1 ⊢
      exact hξmax _ h1 (by rw [← hpf]; exact hys)
    exact (hcgenC K hK).2 hcZ
  ·
    apply haBad
    simp only [Bad, ← hc, if_neg hcξ]
    rw [← hθa]
    exact (hcθ.map g.continuous).mem_closure

end Main

end P2mDenseSliceLocus

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : (pullback f f).Opens)
    (hZ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z)
    (ξ : X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ) :
    ∃ N : X.Opens, ξ ∈ N ∧ ∀ a : X, a ∈ N → f.base a = IsLocalRing.closedPoint R →
      Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = a} → ↑(pullback f f)) ⁻¹'
        (Z : Set ↑(pullback f f))) :=
  P2mDenseSliceLocus.main f Z hZ ξ hξ hξmax

end
end S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
end P2MW
export P2MW.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem (solution)

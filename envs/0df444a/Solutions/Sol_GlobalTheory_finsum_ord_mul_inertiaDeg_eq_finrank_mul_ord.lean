-- Prove2me | solution 1 for GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:39.36529+00:00
-- url     : https://prove2.me/submissions/9d5a6edd-9258-4a95-9a8e-3e70489b8de4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrd
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite
import Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing
namespace GlobalTheory
open IsLocalRing in
open scoped Pointwise in
private lemma exists_linearIndependent_smul_mem_span {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    ∃ v : Fin (Module.finrank A M) → M, LinearIndependent A v ∧
      ∃ c ∈ nonZeroDivisors A, ∀ m : M, c • m ∈ Submodule.span A (Set.range v) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := A) (M := M) le_rfl
  refine ⟨v, hv, ?_⟩
  set N := Submodule.span A (Set.range v)
  have hN : Module.finrank A N = Module.finrank A M := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hC : Module.finrank A (M ⧸ N) = 0 := by
    have := Submodule.finrank_quotient_add_finrank N; omega
  have htors : Module.IsTorsion A (M ⧸ N) := by
    intro x
    obtain ⟨c, hc, hcx⟩ := Module.finrank_eq_zero_iff.1 hC x
    exact ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hcx⟩
  obtain ⟨c, hcann, hcnz⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htors
  refine ⟨c, hcnz, fun m ↦ ?_⟩
  have : c • (N.mkQ m) = 0 :=
    (Submodule.mem_annihilator.1 hcann) _ Submodule.mem_top
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
open IsLocalRing in
open scoped Pointwise in
private lemma isFiniteLength_of_nonZeroDivisor_smul_eq_zero {A X : Type*} [CommRing A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [AddCommGroup X] [Module A X] [Module.Finite A X] {c : A}
    (hc : c ∈ nonZeroDivisors A) (hX : ∀ x : X, c • x = 0) : IsFiniteLength A X := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := X)
  have hle : ∀ i, Ideal.span {c} ≤ LinearMap.ker (LinearMap.toSpanSingleton A X (s i)) := by
    intro i
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hX _
  let φ : (Fin n → A ⧸ Ideal.span {c}) →ₗ[A] X :=
    ∑ i, (Submodule.liftQ _ (LinearMap.toSpanSingleton A X (s i)) (hle i)) ∘ₗ LinearMap.proj i
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      exact (Submodule.liftQ_apply _ _ 1).trans (one_smul A _)
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hQ : IsFiniteLength A (A ⧸ Ideal.span {c}) := isFiniteLength_quotient_span_singleton A hc
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hQ ⊢
  obtain ⟨-, hQa⟩ := hQ
  exact ⟨inferInstance, isArtinian_of_surjective _ φ hφ⟩
open IsLocalRing in
open scoped Pointwise in
private lemma length_quotient_eq_length_add_of_le {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (P Q : Submodule A M) (h : P ≤ Q) :
    Module.length A (M ⧸ P) =
      Module.length A (Q ⧸ LinearMap.ker (P.mkQ ∘ₗ Q.subtype)) + Module.length A (M ⧸ Q) := by
  have e := Module.length_eq_add_of_exact (Submodule.map P.mkQ Q).subtype
    (Submodule.map P.mkQ Q).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  rw [(Submodule.quotientQuotientEquivQuotient P Q h).length_eq] at e
  rw [e, (LinearMap.quotKerEquivRange (P.mkQ ∘ₗ Q.subtype)).length_eq, LinearMap.range_comp,
    Submodule.range_subtype]
open IsLocalRing in
open scoped Pointwise in
private lemma length_quotient_smul_univ_eq_finrank_mul {A M : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : A) (hM : ∀ m : M, a • m = 0 → m = 0) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) =
      Module.finrank A M * Module.length A (A ⧸ Ideal.span {a}) := by
  obtain ⟨v, hv, c, hc, hcN⟩ := exists_linearIndependent_smul_mem_span (A := A) (M := M)
  set N := Submodule.span A (Set.range v) with hNdef
  have hCfin : IsFiniteLength A (M ⧸ N) := by
    refine isFiniteLength_of_nonZeroDivisor_smul_eq_zero hc fun x ↦ ?_
    induction x using Submodule.Quotient.induction_on with
    | H m => rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hcN m
  have hmem : ∀ m : M, a • m ∈ a • N ↔ m ∈ N := by
    intro m
    constructor
    · intro h
      obtain ⟨n, hn, he⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h
      have := hM (n - m) (by rw [smul_sub, he, sub_self])
      rwa [sub_eq_zero.1 this] at hn
    · intro h
      exact Submodule.smul_mem_pointwise_smul _ _ _ h
  have hle1 : a • N ≤ N := by
    rw [← Submodule.ideal_span_singleton_smul]; exact Submodule.smul_le_right
  have hle2 : a • N ≤ a • (⊤ : Submodule A M) := by
    rw [← Submodule.ideal_span_singleton_smul, ← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono le_rfl le_top
  have e1 := length_quotient_eq_length_add_of_le (a • N) N hle1
  have e2 := length_quotient_eq_length_add_of_le (a • N) (a • ⊤) hle2

  let μ : M ≃ₗ[A] (a • ⊤ : Submodule A M) := LinearEquiv.ofBijective
    ((a • LinearMap.id).codRestrict (a • ⊤)
      (fun m ↦ Submodule.smul_mem_pointwise_smul m a ⊤ Submodule.mem_top))
    ⟨fun x y h ↦ by
      have h' : a • x = a • y := congrArg Subtype.val h
      exact sub_eq_zero.1 (hM _ (by rw [smul_sub, h', sub_self])),
     by
      rintro ⟨_, hy⟩
      obtain ⟨m, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hy
      exact ⟨m, rfl⟩⟩
  have hα : Module.length A ((a • ⊤ : Submodule A M) ⧸
      LinearMap.ker ((a • N).mkQ ∘ₗ (a • ⊤ : Submodule A M).subtype)) =
      Module.length A (M ⧸ N) := by
    refine (Submodule.Quotient.equiv N _ μ ?_).length_eq.symm
    ext ⟨x, hx⟩
    obtain ⟨m, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hx
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.subtype_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨n, hn, he⟩
      have : a • n = a • m := congrArg Subtype.val he
      rw [← hM (n - m) (by rw [smul_sub, this, sub_self]) |> sub_eq_zero.1]
      exact hn
    · intro h
      exact ⟨m, h, rfl⟩
  have hβ : Module.length A (N ⧸ LinearMap.ker ((a • N).mkQ ∘ₗ N.subtype)) =
      Module.finrank A M * Module.length A (A ⧸ Ideal.span {a}) := by
    have hker : LinearMap.ker ((a • N).mkQ ∘ₗ N.subtype) = a • (⊤ : Submodule A N) := by
      ext ⟨x, hx⟩
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro h
        obtain ⟨n, hn, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h
        exact Submodule.smul_mem_pointwise_smul (⟨n, hn⟩ : N) a ⊤ Submodule.mem_top
      · intro h
        obtain ⟨n, -, he⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h
        have hx' : x = a • (n : M) := (congrArg Subtype.val he).symm
        rw [hx']
        exact Submodule.smul_mem_pointwise_smul _ a N n.2
    let e : N ≃ₗ[A] (Fin (Module.finrank A M) → A) :=
      hv.linearCombinationEquiv.symm ≪≫ₗ Finsupp.linearEquivFunOnFinite A A _
    have hpi : (a • ⊤ : Submodule A (Fin (Module.finrank A M) → A)) =
        Submodule.pi Set.univ (fun _ ↦ Ideal.span {a}) := by
      ext f
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton']
      constructor
      · intro h i
        obtain ⟨g, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h
        exact ⟨g i, by simp [mul_comm]⟩
      · intro h
        choose g hg using h
        refine Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.2 ⟨g, Submodule.mem_top, ?_⟩
        ext i
        simp [← hg i, mul_comm]
    rw [hker, (Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range])).length_eq, hpi,
      (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
    simp
  rw [hα] at e2
  rw [hβ] at e1
  have hfin : Module.length A (M ⧸ N) ≠ ⊤ := Module.length_ne_top_iff.2 hCfin
  rw [e1, add_comm] at e2
  exact (WithTop.add_left_cancel hfin e2).symm
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
open scoped Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A B : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 1)
    (a : A) (ha : a ≠ 0) :
    ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A},
      ((Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) =
      (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  classical
  haveI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 hdim.le
  haveI : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  haveI := _root_.GlobalTheory.finite_maximalSpectrum_of_finite A B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  set b := algebraMap A B a with hb
  have hb0 : b ≠ 0 := by
    rw [hb, ne_eq, ← map_zero (algebraMap A B)]
    exact hinj.ne ha
  have hM : ∀ m : B, a • m = 0 → m = 0 := fun m h ↦ by
    rw [Algebra.smul_def] at h
    exact (mul_eq_zero.1 h).resolve_left hb0
  have hI : (Ideal.span {b}).restrictScalars A = (a • ⊤ : Submodule A B) := by
    ext x
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
  have hordA : Ring.ord A a ≠ ⊤ := Module.length_ne_top_iff.2
    (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  have h1 : Module.length A (B ⧸ Ideal.span {b}) = Module.finrank A B * Ring.ord A a := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq, hI,
      length_quotient_smul_univ_eq_finrank_mul a hM]
    rfl
  have hne : (Module.finrank A B : ℕ∞) * Ring.ord A a ≠ ⊤ :=
    WithTop.mul_ne_top (ENat.coe_ne_top _) hordA
  have hfinA : IsFiniteLength A (B ⧸ Ideal.span {b}) := by
    rw [← Module.length_ne_top_iff, h1]
    exact hne
  have hfinB : IsFiniteLength B (B ⧸ Ideal.span {b}) := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfinA ⊢
    exact ⟨inferInstance, isArtinian_of_tower A hfinA.2⟩
  have h2 := _root_.GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule A B hfinB
    (fun n : MaximalSpectrum B ↦ Localization.AtPrime n.asIdeal)
    (fun n ↦ Localization.AtPrime n.asIdeal ⧸ (Ideal.span {b}).localized'
      (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))
    (fun n ↦ (Ideal.span {b}).toLocalizedQuotient' (Localization.AtPrime n.asIdeal)
      n.asIdeal.primeCompl (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))
  have hloc : ∀ n : MaximalSpectrum B, Module.length (Localization.AtPrime n.asIdeal)
      (Localization.AtPrime n.asIdeal ⧸ (Ideal.span {b}).localized'
        (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl (Algebra.linearMap B (Localization.AtPrime n.asIdeal))) =
      Ring.ord (Localization.AtPrime n.asIdeal) (algebraMap B _ b) := by
    intro n
    rw [Submodule.localized'_span, Set.image_singleton]
    rfl
  simp only [hloc, h1] at h2
  have hterm : ∀ n ∈ (Finset.univ : Finset (MaximalSpectrum B)),
      Ring.ord (Localization.AtPrime n.asIdeal) (algebraMap B _ b) *
        ((n.asIdeal.inertiaDeg A : ℕ) : ℕ∞) ≠ ⊤ := fun n hn ↦
    ne_top_of_le_ne_top (h2 ▸ hne) (Finset.single_le_sum (f := fun n : MaximalSpectrum B ↦
      Ring.ord (Localization.AtPrime n.asIdeal) (algebraMap B _ b) *
        ((n.asIdeal.inertiaDeg A : ℕ) : ℕ∞)) (fun _ _ ↦ bot_le) hn)
  have h3 := congrArg ENat.toNat h2
  rw [ENat.toNat_sum hterm] at h3
  simp only [ENat.toNat_mul, ENat.toNat_coe] at h3
  have hS : {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = maximalIdeal A} =
      Set.range MaximalSpectrum.toPrimeSpectrum := by
    ext Q
    constructor
    · intro hQ
      have : (Q.asIdeal.comap (algebraMap A B)).IsMaximal := by
        rw [show Q.asIdeal.comap (algebraMap A B) = maximalIdeal A from hQ]; infer_instance
      exact ⟨⟨Q.asIdeal, Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ this⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n.asIdeal)
  rw [hS, finsum_mem_range MaximalSpectrum.toPrimeSpectrum_injective, finsum_eq_sum_of_fintype]
  exact_mod_cast h3.symm
end _root_.GlobalTheory
end GlobalTheory

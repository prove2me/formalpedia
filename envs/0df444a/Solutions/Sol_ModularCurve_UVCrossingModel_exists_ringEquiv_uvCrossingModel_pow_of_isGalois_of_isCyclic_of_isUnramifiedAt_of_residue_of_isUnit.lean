-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d54aec07-e49d-5acf-8fc6-12d282699cee

import Mathlib
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two

import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free
import Theorems.Thm_IsAdicComplete_exists_isPrimitiveRoot_of_residueField
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul
import Theorems.Thm_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq
import Theorems.Thm_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem
import Theorems.Thm_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
import Theorems.Thm_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
import Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
import Theorems.Thm_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
import Theorems.Thm_ModularCurve_UVCrossingModel_two_le_ringKrullDim
import Theorems.Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective
import Theorems.Thm_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~crossingSwap_U"
open scoped TensorProduct

namespace KDMbis44
namespace BP

open PowerSeries in
theorem powerSeries_eq_zero_of_mul_eq_zero_of_notMem_span_C {A : Type*} [CommRing A] (a : A) (ha : IsNilpotent a)
    (hloc : ∀ b : A, b ∈ Ideal.span {a} ∨ IsUnit b)
    (t : A⟦X⟧) (ht : t ∉ Ideal.span {(C a : A⟦X⟧)}) (z : A⟦X⟧) (hz : t * z = 0) : z = 0 := by
  classical

  have hspan : ∀ g : A⟦X⟧, (∀ n, coeff n g ∈ Ideal.span {a}) → g ∈ Ideal.span {(C a : A⟦X⟧)} := by
    intro g hg
    have hc : ∀ n, ∃ b, coeff n g = a * b := fun n => by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hg n)
      exact ⟨b, by rw [← hb, mul_comm]⟩
    choose b hb using hc
    refine Ideal.mem_span_singleton'.mpr ⟨mk b, ?_⟩
    ext n
    rw [mul_comm, coeff_C_mul, coeff_mk, hb]

  have hex : ∃ n, IsUnit (coeff n t) := by
    by_contra! h
    exact ht (hspan t fun n => (hloc (coeff n t)).resolve_right (h n))
  have hd : IsUnit (coeff (Nat.find hex) t) := Nat.find_spec hex
  have hlt : ∀ n < Nat.find hex, ¬ IsUnit (coeff n t) := fun n hn => Nat.find_min hex hn
  set d : ℕ := Nat.find hex with hddef

  set v : A⟦X⟧ := mk fun i => coeff (i + d) t with hv
  set r : A⟦X⟧ := (t.trunc d : A⟦X⟧) with hr
  have hsplit : t = X ^ d * v + r := t.eq_X_pow_mul_shift_add_trunc d
  have hvu : IsUnit v := by
    rw [isUnit_iff_constantCoeff, hv, constantCoeff_mk, zero_add]
    exact hd
  have hrmem : r ∈ Ideal.span {(C a : A⟦X⟧)} := by
    refine hspan r fun n => ?_
    by_cases hn : n < d
    · rw [hr, Polynomial.coeff_coe, coeff_trunc, if_pos hn]
      exact (hloc (coeff n t)).resolve_right (hlt n hn)
    · rw [hr, Polynomial.coeff_coe, coeff_trunc, if_neg hn]
      exact Ideal.zero_mem _
  have hrnil : IsNilpotent r := by
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hrmem
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, by rw [← hg, mul_pow, ← map_pow, hk, map_zero, mul_zero]⟩
  obtain ⟨k, hk⟩ := hrnil
  have h1 : (X ^ d * v) * z = -r * z := by
    have h0 := hz
    rw [hsplit, add_mul] at h0
    linear_combination h0
  have key : ∀ j : ℕ, (X ^ d * v) ^ j * z = (-r) ^ j * z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (X ^ d * v) ^ (j + 1) * z = (X ^ d * v) ^ j * ((X ^ d * v) * z) := by ring
        _ = (X ^ d * v) ^ j * (-r * z) := by rw [h1]
        _ = -r * ((X ^ d * v) ^ j * z) := by ring
        _ = -r * ((-r) ^ j * z) := by rw [ih]
        _ = (-r) ^ (j + 1) * z := by ring
  have hXz : (X : A⟦X⟧) ^ (d * k) * (v ^ k * z) = 0 := by
    have h2 := key k
    rw [neg_pow, hk, mul_zero, zero_mul, mul_pow, ← pow_mul] at h2
    rw [← mul_assoc]
    exact h2
  have hvz : v ^ k * z = 0 := by
    ext n
    have h3 := congrArg (coeff (n + d * k)) hXz
    rwa [coeff_X_pow_mul, map_zero] at h3
  exact (hvu.pow k).mul_right_eq_zero.mp hvz

theorem mem_minimalPrimes_of_inf_eq {S : Type*} [CommRing S] {I Q₁ Q₂ : Ideal S} [Q₁.IsPrime] [Q₂.IsPrime]
    (hinf : Q₁ ⊓ Q₂ = I) (h₂₁ : ¬ Q₂ ≤ Q₁) : Q₁ ∈ I.minimalPrimes := by
  refine ⟨⟨‹_›, hinf ▸ inf_le_left⟩, fun P hP hPQ => ?_⟩
  have hmul : Q₁ * Q₂ ≤ P := Ideal.mul_le_inf.trans (by rw [hinf]; exact hP.2)
  rcases hP.1.mul_le.mp hmul with h | h
  · exact h
  · exact absurd (h.trans hPQ) h₂₁

theorem eq_or_eq_of_mem_minimalPrimes_of_inf_eq {S : Type*} [CommRing S] {I Q₁ Q₂ P : Ideal S}
    [Q₁.IsPrime] [Q₂.IsPrime] (hinf : Q₁ ⊓ Q₂ = I) (hP : P ∈ I.minimalPrimes) : P = Q₁ ∨ P = Q₂ := by
  have hmul : Q₁ * Q₂ ≤ P := Ideal.mul_le_inf.trans (by rw [hinf]; exact hP.1.2)
  rcases hP.1.1.mul_le.mp hmul with h | h
  · exact Or.inl (le_antisymm (hP.2 ⟨‹_›, hinf ▸ inf_le_left⟩ h) h)
  · exact Or.inr (le_antisymm (hP.2 ⟨‹_›, hinf ▸ inf_le_right⟩ h) h)

theorem map_eq_self_and_map_eq_self_of_pins {S : Type*} [CommRing S] (γ : S ≃+* S) (p : S) (hγp : γ p = p)
    {Q₁ Q₂ : Ideal S} [Q₁.IsPrime] [Q₂.IsPrime] (hinf : Q₁ ⊓ Q₂ = Ideal.span {p})
    (h₁₂ : ¬ Q₁ ≤ Q₂) (h₂₁ : ¬ Q₂ ≤ Q₁)
    (a a' : S) (hγa : γ a = a) (hγa' : γ a' = a') (haa' : a * a' ∈ Ideal.span {p})
    (ha : a ∉ Ideal.span {p}) (ha' : a' ∉ Ideal.span {p}) :
    Q₁.map (γ : S →+* S) = Q₁ ∧ Q₂.map (γ : S →+* S) = Q₂ := by
  have hinf' : Q₂ ⊓ Q₁ = Ideal.span {p} := by rw [inf_comm]; exact hinf
  have hQ₁ := mem_minimalPrimes_of_inf_eq hinf h₂₁
  have hQ₂ := mem_minimalPrimes_of_inf_eq hinf' h₁₂
  have h₁ := eq_or_eq_of_mem_minimalPrimes_of_inf_eq hinf
    (Ideal.map_mem_minimalPrimes_span_singleton_of_apply_eq γ p hγp hQ₁)
  have h₂ := eq_or_eq_of_mem_minimalPrimes_of_inf_eq hinf
    (Ideal.map_mem_minimalPrimes_span_singleton_of_apply_eq γ p hγp hQ₂)
  have hp₁ : Ideal.span {p} ≤ Q₁ := hinf ▸ inf_le_left
  rcases ‹Q₁.IsPrime›.mem_or_mem (hp₁ haa') with h | h
  · have h' : a ∉ Q₂ := fun h2 => ha (by rw [← hinf]; exact Ideal.mem_inf.mpr ⟨h, h2⟩)
    exact Ideal.map_eq_self_of_apply_eq_of_mem_of_not_mem γ h₁ h₂ hγa h h'
  · have h' : a' ∉ Q₂ := fun h2 => ha' (by rw [← hinf]; exact Ideal.mem_inf.mpr ⟨h, h2⟩)
    exact Ideal.map_eq_self_of_apply_eq_of_mem_of_not_mem γ h₁ h₂ hγa' h h'

theorem map_eq_self_of_forall_mem_iff {S : Type*} [CommRing S] (γ : S ≃+* S) (q : S) (hγq : γ q = q)
    (Q : Ideal S) (hQ : Q.map (γ : S →+* S) = Q) (J : Ideal S)
    (hJ : ∀ f, f ∈ J ↔ ∃ s ∉ Q, s * f ∈ Ideal.span {q}) : J.map (γ : S →+* S) = J := by
  have hQ' : ∀ s, γ s ∈ Q ↔ s ∈ Q := fun s => by
    conv_lhs => rw [← hQ, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    rw [RingEquiv.symm_apply_apply]
  have hq' : ∀ x, x ∈ Ideal.span {q} ↔ γ x ∈ Ideal.span {q} := fun x => by
    rw [Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨γ c, by rw [map_mul, hγq]⟩
    · rintro ⟨c, hc⟩
      exact ⟨γ.symm c, γ.injective (by rw [map_mul, RingEquiv.apply_symm_apply, hγq, hc])⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    obtain ⟨s, hs, hsf⟩ := (hJ f).mp hf
    refine (hJ _).mpr ⟨γ s, fun h => hs ((hQ' s).mp h), ?_⟩
    rw [RingHom.coe_coe, ← map_mul]
    exact (hq' _).mp hsf
  · intro f hf
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
    obtain ⟨s, hs, hsf⟩ := (hJ f).mp hf
    refine (hJ _).mpr ⟨γ.symm s, fun h => hs ?_, ?_⟩
    · have h' := (hQ' (γ.symm s)).mpr h
      rwa [RingEquiv.apply_symm_apply] at h'
    · rw [hq', map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hsf

theorem mem_span_singleton_of_algebraMap_mem {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    {r x : R} (h : algebraMap R S r ∈ Ideal.span {algebraMap R S x}) : r ∈ Ideal.span {x} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨s, hs⟩ := h
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, zero_mul] at hs
    exact ⟨0, by rw [zero_mul]; exact hinj (by rw [hs, map_zero])⟩
  obtain ⟨p, hpm, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
  let K := FractionRing R
  have hxK : algebraMap R K x ≠ 0 := fun h0 =>
    hx ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) _ h0)
  let y : K := algebraMap R K r / algebraMap R K x
  have h4 : algebraMap R K r = algebraMap R K x * y := by rw [mul_div_cancel₀ _ hxK]
  have hy : IsIntegral R y := by
    refine ⟨p, hpm, ?_⟩
    have h1 : Polynomial.eval₂ (algebraMap R S) (algebraMap R S r) (p.scaleRoots x) = 0 := by
      rw [hs, Polynomial.scaleRoots_eval₂_mul, hps, mul_zero]
    have h2 : Polynomial.eval r (p.scaleRoots x) = 0 :=
      hinj (by rw [← Polynomial.eval₂_at_apply, h1, map_zero])
    have h3 : Polynomial.eval₂ (algebraMap R K) (algebraMap R K r) (p.scaleRoots x) = 0 := by
      rw [Polynomial.eval₂_at_apply, h2, map_zero]
    rw [h4, Polynomial.scaleRoots_eval₂_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hxK)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hy
  refine ⟨k, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hk, ← h4]

open PowerSeries in
theorem powerSeries_mem_span_C_iff {A : Type*} [CommRing A] (a : A) (g : A⟦X⟧) :
    g ∈ Ideal.span {(C a : A⟦X⟧)} ↔ ∀ n, coeff n g ∈ Ideal.span {a} := by
  constructor
  · intro hg n
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    rw [coeff_mul_C]
    exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
  · intro hg
    have hc : ∀ n, ∃ b, coeff n g = a * b := fun n => by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hg n)
      exact ⟨b, by rw [← hb, mul_comm]⟩
    choose b hb using hc
    refine Ideal.mem_span_singleton'.mpr ⟨mk b, ?_⟩
    ext n
    rw [mul_comm, coeff_C_mul, coeff_mk, hb]

section Model

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  (ϖ : W) (hϖ : Irreducible ϖ) (m : ℕ) (hm : 1 ≤ m)

omit [IsDomain W] [IsDiscreteValuationRing W] in

theorem U_mul_V_eq_const_pow (c ϖ : W) (m : ℕ) (hc : c = ϖ ^ m) : U c * V c = const c ϖ ^ m := by
  change Ideal.Quotient.mk _ (MvPowerSeries.X 0) * Ideal.Quotient.mk _ (MvPowerSeries.X 1) =
    Ideal.Quotient.mk _ (MvPowerSeries.C ϖ) ^ m
  rw [← map_mul, ← map_pow, Ideal.Quotient.eq, ← map_pow, ← hc]
  exact Ideal.subset_span rfl

include hϖ in

theorem quot_dichotomy (b : W ⧸ Ideal.span {ϖ ^ m}) :
    b ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ} ∨ IsUnit b := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  by_cases hw : IsUnit w
  · exact Or.inr (hw.map _)
  · left
    have hw' : w ∈ IsLocalRing.maximalIdeal W := hw
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hw'
    obtain ⟨w₁, rfl⟩ := hw'
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem quot_nilpotent : IsNilpotent (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ) :=
  ⟨m, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _⟩

include hϖ hm in

theorem mem_span_U_of_mul_mem_of_notMem (s f : UVCrossingModel W (ϖ ^ m))
    (hs : s ∉ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)}) (h : s * f ∈ Ideal.span {U (ϖ ^ m)}) :
    f ∈ Ideal.span {U (ϖ ^ m)} := by
  obtain ⟨e, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (ϖ ^ m)
  let ψ : UVCrossingModel W (ϖ ^ m) →+* PowerSeries (W ⧸ Ideal.span {ϖ ^ m}) :=
    e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}))
  have hker : ∀ g, ψ g = 0 ↔ g ∈ Ideal.span {U (ϖ ^ m)} := fun g => by
    change e (Ideal.Quotient.mk _ g) = 0 ↔ _
    rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hψs : ψ s ∉ Ideal.span {(PowerSeries.C (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ) : PowerSeries _)} := by
    intro hmem
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g₀, rfl⟩ : ∃ g₀, ψ g₀ = g := by
      obtain ⟨g₁, rfl⟩ := e.surjective g
      obtain ⟨g₀, rfl⟩ := Ideal.Quotient.mk_surjective g₁
      exact ⟨g₀, rfl⟩
    apply hs
    have h0 : ψ (s - g₀ * const (ϖ ^ m) ϖ) = 0 := by
      rw [map_sub, map_mul, ← hg, sub_eq_zero]
      congr 1
      symm
      change e (Ideal.Quotient.mk _ (const (ϖ ^ m) ϖ)) = _
      rw [heC]
    rw [hker] at h0
    have : s = (s - g₀ * const (ϖ ^ m) ϖ) + g₀ * const (ϖ ^ m) ϖ := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.span_mono (by simp) h0) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hψf : ψ f = 0 :=
    powerSeries_eq_zero_of_mul_eq_zero_of_notMem_span_C _ (quot_nilpotent ϖ m) (quot_dichotomy ϖ hϖ m)
      (ψ s) hψs (ψ f) (by rw [← map_mul, hker]; exact h)
  exact (hker f).mp hψf

include hϖ hm in

theorem isPrime_span_const_U : (Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)}).IsPrime := by
  obtain ⟨e, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (ϖ ^ m)
  let ψ : UVCrossingModel W (ϖ ^ m) →+* PowerSeries (W ⧸ Ideal.span {ϖ ^ m}) :=
    e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}))
  have hker : ∀ g, ψ g = 0 ↔ g ∈ Ideal.span {U (ϖ ^ m)} := fun g => by
    change e (Ideal.Quotient.mk _ g) = 0 ↔ _
    rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hle : Ideal.span {ϖ ^ m} ≤ Ideal.span {ϖ} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self ϖ (by omega))
  haveI : (Ideal.span {ϖ}).IsMaximal := by rw [← hϖ.maximalIdeal_eq]; infer_instance
  let ρ : UVCrossingModel W (ϖ ^ m) →+* PowerSeries (W ⧸ Ideal.span {ϖ}) :=
    (PowerSeries.map (Ideal.Quotient.factor hle)).comp ψ
  suffices hQ : Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)} = RingHom.ker ρ by
    rw [hQ]; exact RingHom.ker_isPrime ρ
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      change PowerSeries.map (Ideal.Quotient.factor hle) (e (Ideal.Quotient.mk _ (const (ϖ ^ m) ϖ))) = 0
      rw [heC, PowerSeries.map_C, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self ϖ), map_zero]
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      change PowerSeries.map (Ideal.Quotient.factor hle) (e (Ideal.Quotient.mk _ (U (ϖ ^ m)))) = 0
      rw [heU, map_zero]
  · intro f hf
    have hcoef : ∀ n, PowerSeries.coeff n (ψ f) ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ} := by
      intro n
      have h1 : Ideal.Quotient.factor hle (PowerSeries.coeff n (ψ f)) = 0 := by
        rw [← PowerSeries.coeff_map]
        change PowerSeries.coeff n (ρ f) = 0
        rw [RingHom.mem_ker.mp hf, map_zero]
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (PowerSeries.coeff n (ψ f))
      rw [← hw, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
      obtain ⟨w₁, rfl⟩ := h1
      rw [← hw, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hmem := (powerSeries_mem_span_C_iff _ _).mpr hcoef
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g₀, rfl⟩ : ∃ g₀, ψ g₀ = g := by
      obtain ⟨g₁, rfl⟩ := e.surjective g
      obtain ⟨g₀, rfl⟩ := Ideal.Quotient.mk_surjective g₁
      exact ⟨g₀, rfl⟩
    have h0 : ψ (f - g₀ * const (ϖ ^ m) ϖ) = 0 := by
      rw [map_sub, map_mul, ← hg, sub_eq_zero]
      congr 1
      symm
      change e (Ideal.Quotient.mk _ (const (ϖ ^ m) ϖ)) = _
      rw [heC]
    rw [hker] at h0
    have : f = (f - g₀ * const (ϖ ^ m) ϖ) + g₀ * const (ϖ ^ m) ϖ := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.span_mono (by simp) h0) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

include hϖ hm in

theorem mem_span_U_iff (f : UVCrossingModel W (ϖ ^ m)) :
    f ∈ Ideal.span {U (ϖ ^ m)} ↔
      ∃ s ∉ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)}, s * f ∈ Ideal.span {U (ϖ ^ m) * V (ϖ ^ m)} := by
  constructor
  · intro hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    refine ⟨V (ϖ ^ m), ?_, ?_⟩
    · have := (ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq ϖ hϖ m hm).2.1 1
      rwa [pow_one] at this
    · rw [show V (ϖ ^ m) * (g * U (ϖ ^ m)) = g * (U (ϖ ^ m) * V (ϖ ^ m)) by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨s, hs, hsf⟩
    refine mem_span_U_of_mul_mem_of_notMem ϖ hϖ m hm s f hs (Ideal.span_singleton_le_span_singleton.mpr ?_ hsf)
    exact dvd_mul_right _ _

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem crossingSwap_U (c : W) : crossingSwap c (U c) = V c := by
  change crossingSwap c (UVCrossingModel.mk c (MvPowerSeries.X 0)) = UVCrossingModel.mk c (MvPowerSeries.X 1)
  rw [crossingSwap_mk, uvSwapEquiv_X_zero]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem crossingSwap_V (c : W) : crossingSwap c (V c) = U c := by
  change crossingSwap c (UVCrossingModel.mk c (MvPowerSeries.X 1)) = UVCrossingModel.mk c (MvPowerSeries.X 0)
  rw [crossingSwap_mk, uvSwapEquiv_X_one]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem crossingSwap_const (c w : W) : crossingSwap c (const c w) = const c w := by
  change crossingSwap c (UVCrossingModel.mk c (MvPowerSeries.C w)) = UVCrossingModel.mk c (MvPowerSeries.C w)
  rw [crossingSwap_mk, uvSwapEquiv_C]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem map_crossingSwap_span_const_U (c w : W) :
    (Ideal.span {const c w, U c}).map (crossingSwap c : UVCrossingModel W c →+* UVCrossingModel W c) =
      Ideal.span {const c w, V c} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {crossingSwap c (const c w), crossingSwap c (U c)} = _
  rw [crossingSwap_const, crossingSwap_U]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem map_crossingSwap_span_U' (c : W) :
    (Ideal.span {U c}).map (crossingSwap c : UVCrossingModel W c →+* UVCrossingModel W c) = Ideal.span {V c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {crossingSwap c (U c)} = _
  rw [crossingSwap_U]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem map_crossingSwap_span_U_mul_V (c : W) :
    (Ideal.span {U c * V c}).map (crossingSwap c : UVCrossingModel W c →+* UVCrossingModel W c) =
      Ideal.span {U c * V c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {crossingSwap c (U c * V c)} = _
  rw [map_mul, crossingSwap_U, crossingSwap_V, mul_comm]

include hϖ hm in
theorem isPrime_span_const_V : (Ideal.span {const (ϖ ^ m) ϖ, V (ϖ ^ m)}).IsPrime := by
  rw [← map_crossingSwap_span_const_U]
  haveI := isPrime_span_const_U ϖ hϖ m hm
  exact Ideal.map_isPrime_of_equiv _

include hϖ hm in
theorem mem_span_V_iff (f : UVCrossingModel W (ϖ ^ m)) :
    f ∈ Ideal.span {V (ϖ ^ m)} ↔
      ∃ s ∉ Ideal.span {const (ϖ ^ m) ϖ, V (ϖ ^ m)}, s * f ∈ Ideal.span {U (ϖ ^ m) * V (ϖ ^ m)} := by
  let τ := crossingSwap (ϖ ^ m)
  have hmem : ∀ (g : UVCrossingModel W (ϖ ^ m)) (I : Ideal (UVCrossingModel W (ϖ ^ m))),
      g ∈ I.map (τ : UVCrossingModel W (ϖ ^ m) →+* UVCrossingModel W (ϖ ^ m)) ↔ τ.symm g ∈ I := fun g I => by
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rw [← map_crossingSwap_span_U', ← map_crossingSwap_span_const_U, ← map_crossingSwap_span_U_mul_V, hmem,
    mem_span_U_iff ϖ hϖ m hm]
  constructor
  · rintro ⟨s, hs, hsf⟩
    refine ⟨τ s, fun h => hs ?_, ?_⟩
    · rw [hmem, RingEquiv.symm_apply_apply] at h
      try exact h
    · rw [hmem, map_mul, RingEquiv.symm_apply_apply]; exact hsf
  · rintro ⟨s, hs, hsf⟩
    refine ⟨τ.symm s, fun h => hs ((hmem _ _).mpr h), ?_⟩
    rw [← map_mul, ← hmem]; exact hsf

include hϖ hm in

theorem map_span_U_eq_and_map_span_V_eq (τ : UVCrossingModel W (ϖ ^ m) ≃+* UVCrossingModel W (ϖ ^ m))
    (hτ : τ (const (ϖ ^ m) ϖ) = const (ϖ ^ m) ϖ)
    (a a' : UVCrossingModel W (ϖ ^ m)) (hτa : τ a = a) (hτa' : τ a' = a')
    (haa' : a * a' ∈ Ideal.span {const (ϖ ^ m) ϖ})
    (ha : a ∉ Ideal.span {const (ϖ ^ m) ϖ}) (ha' : a' ∉ Ideal.span {const (ϖ ^ m) ϖ}) :
    (Ideal.span {U (ϖ ^ m)}).map (τ : UVCrossingModel W (ϖ ^ m) →+* UVCrossingModel W (ϖ ^ m)) =
        Ideal.span {U (ϖ ^ m)} ∧
      (Ideal.span {V (ϖ ^ m)}).map (τ : UVCrossingModel W (ϖ ^ m) →+* UVCrossingModel W (ϖ ^ m)) =
        Ideal.span {V (ϖ ^ m)} := by
  obtain ⟨hinf, hV, hU, -, -⟩ :=
    ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq ϖ hϖ m hm
  haveI := isPrime_span_const_U ϖ hϖ m hm
  haveI := isPrime_span_const_V ϖ hϖ m hm
  have h₁₂ : ¬ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)} ≤ Ideal.span {const (ϖ ^ m) ϖ, V (ϖ ^ m)} := fun h =>
    hU 1 (by rw [pow_one]; exact h (Ideal.subset_span (by simp)))
  have h₂₁ : ¬ Ideal.span {const (ϖ ^ m) ϖ, V (ϖ ^ m)} ≤ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)} := fun h =>
    hV 1 (by rw [pow_one]; exact h (Ideal.subset_span (by simp)))
  obtain ⟨hQU, hQV⟩ := map_eq_self_and_map_eq_self_of_pins τ (const (ϖ ^ m) ϖ) hτ hinf h₁₂ h₂₁ a a' hτa hτa' haa' ha ha'
  have hUV : U (ϖ ^ m) * V (ϖ ^ m) = const (ϖ ^ m) ϖ ^ m := U_mul_V_eq_const_pow (ϖ ^ m) ϖ m rfl
  have hτq : τ (U (ϖ ^ m) * V (ϖ ^ m)) = U (ϖ ^ m) * V (ϖ ^ m) := by rw [hUV, map_pow, hτ]
  exact ⟨map_eq_self_of_forall_mem_iff τ _ hτq _ hQU _ (mem_span_U_iff ϖ hϖ m hm),
    map_eq_self_of_forall_mem_iff τ _ hτq _ hQV _ (mem_span_V_iff ϖ hϖ m hm)⟩

end Model

section ModelExtras

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  (ϖ : W) (hϖ : Irreducible ϖ) (E : ℕ) (hE : 1 ≤ E)

include hϖ hE in
theorem U_notMem_span_const : U (ϖ ^ E) ∉ Ideal.span {const (ϖ ^ E) ϖ} := fun h =>
  (ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq ϖ hϖ E hE).2.2.1 1
    (by rw [pow_one]; exact Ideal.span_mono (by simp) h)

include hϖ hE in
theorem V_notMem_span_const : V (ϖ ^ E) ∉ Ideal.span {const (ϖ ^ E) ϖ} := fun h =>
  (ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq ϖ hϖ E hE).2.1 1
    (by rw [pow_one]; exact Ideal.span_mono (by simp) h)

end ModelExtras

section Transport

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  (ϖ : W) (hϖ : Irreducible ϖ) (m : ℕ) (hm : 1 ≤ m)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem map_span_singleton {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (x : R) : (Ideal.span {x}).map f = Ideal.span {f x} := by
  rw [Ideal.map_span, Set.image_singleton]

include hϖ hm in

theorem map_span_symm_U_eq_and_map_span_symm_V_eq {S : Type*} [CommRing S]
    (e : S ≃+* UVCrossingModel W (ϖ ^ m)) (p : S) (hp : e.symm (const (ϖ ^ m) ϖ) = p)
    (σ : S ≃+* S) (hσp : σ p = p)
    (b b' : S) (hσb : σ b = b) (hσb' : σ b' = b') (hbb' : b * b' ∈ Ideal.span {p})
    (hb : b ∉ Ideal.span {p}) (hb' : b' ∉ Ideal.span {p}) :
    (Ideal.span {e.symm (U (ϖ ^ m))}).map (σ : S →+* S) = Ideal.span {e.symm (U (ϖ ^ m))} ∧
      (Ideal.span {e.symm (V (ϖ ^ m))}).map (σ : S →+* S) = Ideal.span {e.symm (V (ϖ ^ m))} := by
  let τ : UVCrossingModel W (ϖ ^ m) ≃+* UVCrossingModel W (ϖ ^ m) := e.symm.trans (σ.trans e)
  have hτ : ∀ x, τ x = e (σ (e.symm x)) := fun _ => rfl
  have hpe : e p = const (ϖ ^ m) ϖ := by rw [← hp, RingEquiv.apply_symm_apply]
  have hspan : ∀ s : S, s ∈ Ideal.span {p} ↔ e s ∈ Ideal.span {const (ϖ ^ m) ϖ} := fun s => by
    rw [← hpe]
    change _ ↔ e s ∈ Ideal.span {(e : S →+* UVCrossingModel W (ϖ ^ m)) p}
    rw [← map_span_singleton (e : S →+* UVCrossingModel W (ϖ ^ m)), Ideal.map_comap_of_equiv, Ideal.mem_comap]
    change _ ↔ e.symm (e s) ∈ _
    rw [RingEquiv.symm_apply_apply]
  obtain ⟨hU, hV⟩ := map_span_U_eq_and_map_span_V_eq ϖ hϖ m hm τ
    (by rw [hτ, hp, hσp, hpe]) (e b) (e b')
    (by rw [hτ, RingEquiv.symm_apply_apply, hσb]) (by rw [hτ, RingEquiv.symm_apply_apply, hσb'])
    (by rw [← map_mul, ← hspan]; exact hbb') (fun h => hb ((hspan b).mpr h)) (fun h => hb' ((hspan b').mpr h))
  rw [map_span_singleton, RingHom.coe_coe, hτ] at hU hV
  constructor
  · rw [map_span_singleton, RingHom.coe_coe]
    have h := congrArg (Ideal.map (e.symm : UVCrossingModel W (ϖ ^ m) →+* S)) hU
    rw [map_span_singleton, map_span_singleton, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h
    exact h
  · rw [map_span_singleton, RingHom.coe_coe]
    have h := congrArg (Ideal.map (e.symm : UVCrossingModel W (ϖ ^ m) →+* S)) hV
    rw [map_span_singleton, map_span_singleton, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h
    exact h

end Transport

theorem ideal_map_eq_map_of_forall_apply_eq {R S F G : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [FunLike G R S] (f : F) (g : G) (h : ∀ x, f x = g x) (I : Ideal R) :
    I.map f = I.map g := by
  unfold Ideal.map
  congr 2
  exact funext h

theorem branch_pin
    {W W' B : Type*} [CommRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [Algebra W W']
    [CommRing B] [Algebra W B]
    (π : W) (hπ' : Irreducible (algebraMap W W' π)) (m : ℕ) (hm : 0 < m)
    (e' : B ⊗[W] W' ≃+* UVCrossingModel W' (algebraMap W W' π ^ m))
    (hsymmπ : e'.symm (const (algebraMap W W' π ^ m) (algebraMap W W' π)) = algebraMap W (B ⊗[W] W') π)
    (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra R (B ⊗[W] W')]
    [Algebra.IsIntegral R (B ⊗[W] W')] [FaithfulSMul R (B ⊗[W] W')]
    (rπ rU rV : R) (N : ℕ) (hN : 0 < N) (hUV : rU * rV = rπ ^ N)
    (hrU : rU ∉ Ideal.span {rπ}) (hrV : rV ∉ Ideal.span {rπ})
    (hrπ : algebraMap R (B ⊗[W] W') rπ = algebraMap W (B ⊗[W] W') π)
    (βU βV : B) (hβU : algebraMap R (B ⊗[W] W') rU = βU ⊗ₜ[W] 1)
    (hβV : algebraMap R (B ⊗[W] W') rV = βV ⊗ₜ[W] 1) :
    (∀ γ : W' ≃ₐ[W] W', Ideal.map (Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom W W' γ))
        (Ideal.span {e'.symm (U (algebraMap W W' π ^ m))}) = Ideal.span {e'.symm (U (algebraMap W W' π ^ m))}) ∧
    (∀ γ : W' ≃ₐ[W] W', Ideal.map (Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom W W' γ))
        (Ideal.span {e'.symm (V (algebraMap W W' π ^ m))}) = Ideal.span {e'.symm (V (algebraMap W W' π ^ m))}) := by

  set p : B ⊗[W] W' := algebraMap W (B ⊗[W] W') π with hpdef
  have hinj := FaithfulSMul.algebraMap_injective R (B ⊗[W] W')
  have hbb' : (βU ⊗ₜ[W] (1 : W')) * (βV ⊗ₜ[W] (1 : W')) ∈ Ideal.span {p} := by
    rw [← hβU, ← hβV, ← map_mul, hUV, map_pow, hrπ]
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hN
  have hb : βU ⊗ₜ[W] (1 : W') ∉ Ideal.span {p} := fun h =>
    hrU (mem_span_singleton_of_algebraMap_mem hinj (by rw [hβU, hrπ]; exact h))
  have hb' : βV ⊗ₜ[W] (1 : W') ∉ Ideal.span {p} := fun h =>
    hrV (mem_span_singleton_of_algebraMap_mem hinj (by rw [hβV, hrπ]; exact h))

  have key : ∀ γ : W' ≃ₐ[W] W', ∃ σ : B ⊗[W] W' ≃+* B ⊗[W] W',
      (∀ z, Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom W W' γ) z = σ z) ∧
      ∀ β : B, σ (β ⊗ₜ[W] 1) = β ⊗ₜ[W] 1 := by
    intro γ
    refine ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (MulSemiringAction.toAlgEquiv W W' γ)).toRingEquiv, fun z => ?_, fun β => ?_⟩
    · change _ = Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) (MulSemiringAction.toAlgEquiv W W' γ) z
      rw [Algebra.TensorProduct.congr_apply]
      congr 1
      all_goals rfl
    · change Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) (MulSemiringAction.toAlgEquiv W W' γ) _ = _
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
      all_goals rfl
  have hp1 : p = algebraMap W B π ⊗ₜ[W] (1 : W') := Algebra.TensorProduct.algebraMap_apply π
  constructor
  · intro γ
    obtain ⟨σ, hσ, hσβ⟩ := key γ
    rw [ideal_map_eq_map_of_forall_apply_eq _ (σ : B ⊗[W] W' →+* B ⊗[W] W') hσ]
    exact (map_span_symm_U_eq_and_map_span_symm_V_eq (algebraMap W W' π) hπ' m hm e' p hsymmπ σ
      (by rw [hp1, hσβ]) _ _ (hσβ βU) (hσβ βV) hbb' hb hb').1
  · intro γ
    obtain ⟨σ, hσ, hσβ⟩ := key γ
    rw [ideal_map_eq_map_of_forall_apply_eq _ (σ : B ⊗[W] W' →+* B ⊗[W] W') hσ]
    exact (map_span_symm_U_eq_and_map_span_symm_V_eq (algebraMap W W' π) hπ' m hm e' p hsymmπ σ
      (by rw [hp1, hσβ]) _ _ (hσβ βU) (hσβ βV) hbb' hb hb').2

end BP
end KDMbis44

namespace KDMbis44

section Residue

variable {W : Type*} [CommRing W] [IsLocalRing W]

noncomputable def resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) :
    UVCrossingModel W c →+* IsLocalRing.ResidueField W :=
  Ideal.Quotient.lift (uvCrossingIdeal W c)
    ((IsLocalRing.residue W).comp (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)))
    (by
      intro f hf
      change f ∈ Ideal.span _ at hf
      rw [Ideal.mem_span_singleton] at hf
      obtain ⟨g, rfl⟩ := hf
      show (IsLocalRing.residue W) (MvPowerSeries.constantCoeff _) = 0
      rw [IsLocalRing.residue_eq_zero_iff, map_mul, map_sub, map_mul,
        MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul, zero_sub]
      exact Ideal.mul_mem_right _ _ (neg_mem hc))

theorem resHom_mk (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (f : MvPowerSeries (Fin 2) W) :
    resHom c hc (UVCrossingModel.mk c f) = IsLocalRing.residue W (MvPowerSeries.constantCoeff f) :=
  rfl

theorem resHom_const (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (w : W) :
    resHom c hc (const c w) = IsLocalRing.residue W w := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.C w)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_C]

theorem resHom_U (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) : resHom c hc (U c) = 0 := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.X 0)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_X, map_zero]

theorem resHom_V (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) : resHom c hc (V c) = 0 := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.X 1)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_X, map_zero]

theorem resHom_surjective (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) :
    Function.Surjective (resHom c hc) := by
  intro x
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨const c w, resHom_const c hc w⟩

theorem ker_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) [IsLocalRing (UVCrossingModel W c)] :
    RingHom.ker (resHom c hc) = IsLocalRing.maximalIdeal (UVCrossingModel W c) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (resHom_surjective c hc))

theorem mem_maximalIdeal_iff_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (a : UVCrossingModel W c) :
    a ∈ IsLocalRing.maximalIdeal (UVCrossingModel W c) ↔ resHom c hc a = 0 := by
  rw [← ker_resHom c hc, RingHom.mem_ker]

theorem isUnit_iff_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (a : UVCrossingModel W c) :
    IsUnit a ↔ resHom c hc a ≠ 0 := by
  rw [Ne, ← mem_maximalIdeal_iff_resHom c hc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

theorem isUnit_mk_iff (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (f : MvPowerSeries (Fin 2) W) :
    IsUnit (UVCrossingModel.mk c f) ↔ IsUnit (MvPowerSeries.constantCoeff f) := by
  rw [isUnit_iff_resHom c hc, resHom_mk, Ne, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem isUnit_const_iff (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (w : W) :
    IsUnit (const c w) ↔ IsUnit w := by
  change IsUnit (UVCrossingModel.mk c (MvPowerSeries.C w)) ↔ _
  rw [isUnit_mk_iff c hc, MvPowerSeries.constantCoeff_C]

theorem exists_const_mul_sub_one_mem (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (u : (UVCrossingModel W c)ˣ) :
    ∃ u₀ : Wˣ, (u : UVCrossingModel W c) * const c (↑u₀⁻¹ : W) - 1 ∈
      IsLocalRing.maximalIdeal (UVCrossingModel W c) := by
  obtain ⟨f, hf⟩ := UVCrossingModel.mk_surjective c (u : UVCrossingModel W c)
  have hu : IsUnit (MvPowerSeries.constantCoeff f) := by
    rw [← isUnit_mk_iff c hc, hf]; exact u.isUnit
  refine ⟨hu.unit, ?_⟩
  rw [mem_maximalIdeal_iff_resHom c hc, map_sub, map_one, map_mul, ← hf, resHom_mk, resHom_const,
    ← map_mul, IsUnit.mul_val_inv, map_one, sub_self]

end Residue

theorem maximalIdeal_uvCrossingModel_eq_span {W : Type*} [CommRing W] [IsLocalRing W]
    (ϖ : W) (hϖ : IsLocalRing.maximalIdeal W = Ideal.span {ϖ}) (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] :
    IsLocalRing.maximalIdeal (UVCrossingModel W c) = Ideal.span {const c ϖ, U c, V c} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c x
    rw [mem_maximalIdeal_iff_resHom c hc, resHom_mk, IsLocalRing.residue_eq_zero_iff, hϖ,
      Ideal.mem_span_singleton] at hx
    obtain ⟨w, hw⟩ := hx

    have hker : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈
        RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W →+* W) := by
      rw [RingHom.mem_ker, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
    rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff 2, Ideal.mem_span_range_iff_exists_fun] at hker
    obtain ⟨g, hg⟩ := hker
    have hf : f = MvPowerSeries.C ϖ * MvPowerSeries.C w + (g 0 * MvPowerSeries.X 0 + g 1 * MvPowerSeries.X 1) := by
      rw [← map_mul, ← hw, Fin.sum_univ_two] at *
      linear_combination -hg
    rw [hf, map_add, map_add, map_mul, map_mul, map_mul]
    refine Ideal.add_mem _ ?_ (Ideal.add_mem _ ?_ ?_)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · rw [Ideal.span_le]
    rintro x (rfl | rfl | rfl)
    · rw [SetLike.mem_coe, mem_maximalIdeal_iff_resHom c hc, resHom_const, IsLocalRing.residue_eq_zero_iff, hϖ]
      exact Ideal.mem_span_singleton_self ϖ
    · rw [SetLike.mem_coe, mem_maximalIdeal_iff_resHom c hc]; exact resHom_U c hc
    · rw [SetLike.mem_coe, mem_maximalIdeal_iff_resHom c hc]; exact resHom_V c hc

theorem U_mul_V_eq_const {W : Type*} [CommRing W] (c : W) : U c * V c = const c c := by
  change Ideal.Quotient.mk _ (MvPowerSeries.X 0) * Ideal.Quotient.mk _ (MvPowerSeries.X 1) =
    Ideal.Quotient.mk _ (MvPowerSeries.C c)
  rw [← map_mul, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

theorem rel_of_apply_eq {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (θ : A →+* C) (f : B →+* C) (X0 X1 Cπ : A) (x y p : B) (m : ℕ) (u : Bˣ)
    (hX : θ X0 = f x) (hY : θ X1 = f y) (hC : θ Cπ = f p) (hxy : x * y = p ^ m * ↑u) :
    θ X0 * θ X1 = θ Cπ ^ m * ((Units.map f.toMonoidHom u : Cˣ) : C) := by
  rw [hX, hY, hC, ← map_mul, hxy, map_mul, map_pow, Units.coe_map]
  rfl

theorem two_le_ringKrullDim_adicCompletion_of_uvCrossingModel
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
    (B : Type*) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra (UVCrossingModel W (π ^ N)) B] [Module.Finite (UVCrossingModel W (π ^ N)) B]
    [FaithfulSMul (UVCrossingModel W (π ^ N)) B] :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
  IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le B
    ((ModularCurve.UVCrossingModel.two_le_ringKrullDim π hπ N hN).trans
      (Algebra.IsIntegral.ringKrullDim_le_of_injective
        (FaithfulSMul.algebraMap_injective (UVCrossingModel W (π ^ N)) B)))

theorem bijective_algebraMap_adicCompletion_of_moduleFinite
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    Function.Bijective (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) := by
  refine ⟨fun a b h => ?_, fun z => ?_⟩
  · rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply] at h
    exact AdicCompletion.of_injective _ _ h
  obtain ⟨φ, hφ, -, -, e, he₁, he₂⟩ := IsLocalRing.exists_adicCompletion_ringHom_finite_of_moduleFinite R S
  suffices h : ∀ t : TensorProduct R (AdicCompletion (IsLocalRing.maximalIdeal R) R) S,
      ∃ s : S, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s = e t by
    obtain ⟨s, hs⟩ := h (e.symm z)
    exact ⟨s, by rw [hs, RingEquiv.apply_symm_apply]⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r s =>
    refine ⟨algebraMap R S ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal R)).symm r) * s, ?_⟩
    have hr : r = algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal R)).symm r) := by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.of_ofAlgEquiv_symm]
    rw [map_mul, ← hφ, ← he₁, ← he₂, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← hr]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    exact ⟨s + t, by rw [map_add, map_add, hs, ht]⟩

theorem exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_uvCrossingModel
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
    (B : Type*) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra (UVCrossingModel W (π ^ N)) B] [Module.Finite (UVCrossingModel W (π ^ N)) B] :
    ∃ eB : B ≃+* AdicCompletion (IsLocalRing.maximalIdeal B) B,
      ∀ b : B, eB b = algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) b := by
  haveI : IsLocalRing (UVCrossingModel W (π ^ N)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ N hN).2.1
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ N)) := ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ N))) (UVCrossingModel W (π ^ N)) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal (π ^ N)
  exact ⟨RingEquiv.ofBijective _ (bijective_algebraMap_adicCompletion_of_moduleFinite (UVCrossingModel W (π ^ N)) B),
    fun _ => rfl⟩

theorem exists_surjective_mvPowerSeries_adicCompletion
    {W B : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra W B] (π : W) (hπ : Irreducible π) (x y : B)
    (hmax : IsLocalRing.maximalIdeal B = Ideal.span {algebraMap W B π, x, y})
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B) :
    ∃ θ : MvPowerSeries (Fin 2) W →+* AdicCompletion (IsLocalRing.maximalIdeal B) B,
      Function.Surjective θ ∧ θ (MvPowerSeries.X 0) = algebraMap B _ x ∧ θ (MvPowerSeries.X 1) = algebraMap B _ y ∧
      ∀ o : W, θ (MvPowerSeries.C o) = algebraMap B _ (algebraMap W B o) := by
  have hres' : Function.Surjective ((IsLocalRing.residue B).comp (algebraMap W B)) := by
    intro r
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨w, hw⟩ := hres b
    refine ⟨w, ?_⟩
    rw [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hw
  obtain ⟨θW, θ₁, hθWC, -, hsurj, hcomp, hX0, hX1⟩ :=
    IsLocalRing.exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span (O := W) (R := B)
      π hπ x y hmax hres'
  obtain ⟨e, he⟩ := PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C π hπ
  let eW : W ≃+* (PowerSeries W ⧸ Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C π}) :=
    (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal W)).toRingEquiv.trans e
  have heW : ∀ o : W, eW o = Ideal.Quotient.mk _ (PowerSeries.C o) := fun o => by
    show e (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal W) o) = _
    rw [AdicCompletion.ofAlgEquiv_apply, ← he o, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  refine ⟨θ₁.comp (MvPowerSeries.map (σ := Fin 2) eW.toRingHom), ?_, ?_, ?_, fun o => ?_⟩
  · refine hsurj.comp fun g => ⟨MvPowerSeries.map (σ := Fin 2) eW.symm.toRingHom g, ?_⟩
    ext n
    simp
  · rw [RingHom.comp_apply, MvPowerSeries.map_X, hX0]
  · rw [RingHom.comp_apply, MvPowerSeries.map_X, hX1]
  · rw [RingHom.comp_apply, MvPowerSeries.map_C, ← RingHom.comp_apply θ₁ MvPowerSeries.C, hcomp,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, heW, hθWC]

end KDMbis44

namespace KDMbis44
namespace G

theorem algebraMap_uvCrossingModel_injective
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (E : ℕ) (hE : 1 ≤ E) :
    Function.Injective (algebraMap W (UVCrossingModel W (ϖ ^ E))) := by
  haveI : IsDomain (UVCrossingModel W (ϖ ^ E)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ E hE).1
  have hconst : ∀ w : W, algebraMap W (UVCrossingModel W (ϖ ^ E)) w = const (ϖ ^ E) w := fun w => by
    change Ideal.Quotient.mk _ (algebraMap W (MvPowerSeries (Fin 2) W) w) = Ideal.Quotient.mk _ (MvPowerSeries.C w)
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  have hϖ0 : const (ϖ ^ E) ϖ ≠ 0 := by
    intro h0
    obtain ⟨-, hV, hU, -, -⟩ :=
      ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq ϖ hϖ E hE
    have hUV : U (ϖ ^ E) * V (ϖ ^ E) = 0 := by
      have h1 : U (ϖ ^ E) * V (ϖ ^ E) = const (ϖ ^ E) ϖ ^ E := by
        change Ideal.Quotient.mk _ (MvPowerSeries.X 0) * Ideal.Quotient.mk _ (MvPowerSeries.X 1) =
          Ideal.Quotient.mk _ (MvPowerSeries.C ϖ) ^ E
        rw [← map_mul, ← map_pow, Ideal.Quotient.eq, ← map_pow]
        exact Ideal.subset_span rfl
      rw [h1, h0, zero_pow (by omega)]
    rcases mul_eq_zero.mp hUV with h | h
    · exact hU 1 (by rw [pow_one, h]; exact Ideal.zero_mem _)
    · exact hV 1 (by rw [pow_one, h]; exact Ideal.zero_mem _)
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hsub hϖ
  have h0 : algebraMap W (UVCrossingModel W (ϖ ^ E)) (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [hk, map_mul, map_pow, mul_eq_zero] at h0
  rcases h0 with h | h
  · exact (u.isUnit.map _).ne_zero h
  · exact hϖ0 (by rw [← hconst]; exact eq_zero_of_pow_eq_zero h)

theorem algebraMap_tensorProduct_ne_zero {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [CommRing W'] [Algebra W W'] [Module.Flat W W'] (hinj : Function.Injective (algebraMap W B))
    (w : W) (hw : algebraMap W W' w ≠ 0) : algebraMap W (B ⊗[W] W') w ≠ 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply']
  intro h
  apply hw
  apply Algebra.TensorProduct.includeRight_injective (R := W) (A := B) (B := W') hinj
  rw [Algebra.TensorProduct.includeRight_apply, h, map_zero]

theorem isNoetherianRing_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [IsNoetherianRing B] [CommRing W'] [Algebra W W'] [Module.Finite W W'] : IsNoetherianRing (B ⊗[W] W') :=
  isNoetherianRing_iff.mpr (isNoetherian_of_tower B (isNoetherian_of_isNoetherianRing_of_finite B (B ⊗[W] W')))

theorem exists_sub_one_tmul_mem_map {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B] [IsLocalRing B]
    [CommRing W'] [Algebra W W']
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B)
    (z : B ⊗[W] W') : ∃ w' : W', z - (1 : B) ⊗ₜ[W] w' ∈
      (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[W] W')) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [TensorProduct.tmul_zero, sub_zero]; exact Ideal.zero_mem _⟩
  | tmul b w' =>
    obtain ⟨w, hw⟩ := hres b
    refine ⟨algebraMap W W' w * w', ?_⟩
    have h1 : (1 : B) ⊗ₜ[W] (algebraMap W W' w * w') = algebraMap W B w ⊗ₜ[W] w' := by
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have h2 : b ⊗ₜ[W] w' - algebraMap W B w ⊗ₜ[W] w' =
        algebraMap B (B ⊗[W] W') (b - algebraMap W B w) * ((1 : B) ⊗ₜ[W] w') := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.sub_tmul]
    rw [h1, h2]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hw)
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    refine ⟨w₁ + w₂, ?_⟩
    rw [TensorProduct.tmul_add, show x + y - ((1 : B) ⊗ₜ[W] w₁ + (1 : B) ⊗ₜ[W] w₂) =
      (x - (1 : B) ⊗ₜ[W] w₁) + (y - (1 : B) ⊗ₜ[W] w₂) by abel]
    exact Ideal.add_mem _ h₁ h₂

theorem isLocalRing_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B] [IsLocalRing B]
    [CommRing W'] [Algebra W W'] [IsLocalRing W'] [Module.Finite W W'] [Module.Flat W W']
    (hinj : Function.Injective (algebraMap W B))
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B) :
    IsLocalRing (B ⊗[W] W') := by
  haveI : Nontrivial (B ⊗[W] W') :=
    (Algebra.TensorProduct.includeRight_injective (R := W) (A := B) (B := W') hinj).nontrivial
  set J : Ideal (B ⊗[W] W') := (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[W] W')) with hJ

  have hker : RingHom.ker (algebraMap B (B ⊗[W] W')) ≤ IsLocalRing.maximalIdeal B :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨𝔐, h𝔐, h𝔐c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B ⊗[W] W') (IsLocalRing.maximalIdeal B) hker
  have hJle : ∀ 𝔐' : Ideal (B ⊗[W] W'), 𝔐'.IsMaximal → J ≤ 𝔐' := fun 𝔐' h' => by
    rw [hJ, Ideal.map_le_iff_le_comap,
      ← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) 𝔐')]
  have hJtop : J ≠ ⊤ := fun h => h𝔐.ne_top (top_le_iff.mp (h ▸ hJle 𝔐 h𝔐))

  haveI : Nontrivial ((B ⊗[W] W') ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  let ψ : W' →+* (B ⊗[W] W') ⧸ J := (Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.includeRight (R := W) (A := B) (B := W')).toRingHom
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨w', hw'⟩ := exists_sub_one_tmul_mem_map hres z
    refine ⟨w', ?_⟩
    change Ideal.Quotient.mk J ((1 : B) ⊗ₜ[W] w') = Ideal.Quotient.mk J z
    rw [Ideal.Quotient.eq]
    rw [← neg_sub]
    exact Submodule.neg_mem _ hw'
  haveI : IsLocalRing ((B ⊗[W] W') ⧸ J) := IsLocalRing.of_surjective' ψ hψ

  refine IsLocalRing.of_unique_max_ideal ⟨𝔐, h𝔐, fun 𝔐' h𝔐' => ?_⟩
  let mk : (B ⊗[W] W') →+* ((B ⊗[W] W') ⧸ J) := Ideal.Quotient.mk J
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hkermk : RingHom.ker mk = J := Ideal.mk_ker
  let M₀ : Ideal (B ⊗[W] W') := (IsLocalRing.maximalIdeal ((B ⊗[W] W') ⧸ J)).comap mk
  have hM₀ : M₀ ≠ ⊤ := Ideal.comap_ne_top mk (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hback : ∀ 𝔑 : Ideal (B ⊗[W] W'), 𝔑.IsMaximal → 𝔑 = M₀ := by
    intro 𝔑 h𝔑
    refine h𝔑.eq_of_le hM₀ ?_
    have hne : 𝔑.map mk ≠ ⊤ := by
      intro h
      apply h𝔑.ne_top
      have := Ideal.comap_map_of_surjective mk hmk 𝔑
      rw [h, Ideal.comap_top] at this
      rw [eq_top_iff, this, sup_le_iff]
      refine ⟨le_rfl, ?_⟩
      rw [← RingHom.ker_eq_comap_bot, hkermk]
      exact hJle 𝔑 h𝔑
    exact Ideal.map_le_iff_le_comap.mp (IsLocalRing.le_maximalIdeal hne)
  rw [hback 𝔐' h𝔐', hback 𝔐 h𝔐]

theorem exists_sub_mem_maximalIdeal_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [IsLocalRing B] [CommRing W'] [Algebra W W'] [Module.Finite W W'] [IsLocalRing (B ⊗[W] W')]
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B)
    (c : W' → B ⊗[W] W') (hc : ∀ w', c w' = (1 : B) ⊗ₜ[W] w') (z : B ⊗[W] W') :
    ∃ w' : W', z - c w' ∈ IsLocalRing.maximalIdeal (B ⊗[W] W') := by
  obtain ⟨w', hw'⟩ := exists_sub_one_tmul_mem_map hres z
  refine ⟨w', ?_⟩
  rw [hc]
  refine (Ideal.map_le_iff_le_comap.mpr ?_) hw'
  rw [← IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) (IsLocalRing.maximalIdeal (B ⊗[W] W')))]

theorem map_toAlgHom_injective {W R₀ B W' : Type*} [CommRing W] [CommRing R₀] [Algebra W R₀]
    [CommRing B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B]
    [CommRing W'] [Algebra W W'] [Module.Flat W W'] [FaithfulSMul R₀ B] :
    Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')) := by
  have h : ∀ z, Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W') z =
      ((IsScalarTower.toAlgHom W R₀ B).toLinearMap.rTensor W') z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r w => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R₀ B) hab

theorem map_toAlgHom_finite {W R₀ B W' : Type*} [CommRing W] [CommRing R₀] [Algebra W R₀]
    [CommRing B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    [CommRing W'] [Algebra W W'] :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')).toRingHom.Finite := by
  classical
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')
  letI alg : Algebra (R₀ ⊗[W] W') (B ⊗[W] W') := φ.toRingHom.toAlgebra
  have hsmul : ∀ (a : R₀ ⊗[W] W') (z : B ⊗[W] W'), a • z = φ a * z := fun _ _ => rfl
  change Module.Finite (R₀ ⊗[W] W') (B ⊗[W] W')
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite R₀ B›
  refine Module.finite_def.mpr ⟨s.image fun b => b ⊗ₜ[W] (1 : W'), ?_⟩
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul b w =>
    have hb : b ∈ Submodule.span R₀ (s : Set B) := by rw [hs]; exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      have : x ⊗ₜ[W] w = ((1 : R₀) ⊗ₜ[W] w) • (x ⊗ₜ[W] (1 : W')) := by
        rw [hsmul, Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        change _ = x ⊗ₜ[W] (w * 1)
        rw [mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hx))
    | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) ⊗ₜ[W] w = (r ⊗ₜ[W] (1 : W')) • (x ⊗ₜ[W] w) := by
        rw [hsmul, Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          IsScalarTower.coe_toAlgHom', Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end G
end KDMbis44

namespace KDMbis44
namespace Frame

universe u v uK uF

section Action

variable {W : Type u} [CommRing W]
  {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra W R₀]
  {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra W B] [Algebra R₀ B]
  [IsScalarTower W R₀ B] [Module.Finite R₀ B]
  {K₀ : Type uK} {F : Type uF} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
  [Field F] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F]
  [IsFractionRing B F] [FiniteDimensional K₀ F]
  {W' : Type u} [CommRing W'] [Algebra W W']

variable (W R₀ B K₀ F W') in

noncomputable def actHom : (F ≃ₐ[K₀] F) →* ((B ⊗[W] W') ≃ₐ[W] (B ⊗[W] W')) where
  toFun g := Algebra.TensorProduct.congr ((galRestrict R₀ K₀ F B g).restrictScalars W) (AlgEquiv.refl : W' ≃ₐ[W] W')
  map_one' := by
    apply AlgEquiv.ext
    intro z
    rw [Algebra.TensorProduct.congr_apply, map_one]
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; rfl
    | tmul b w => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]; rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    rw [AlgEquiv.mul_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.congr_apply, map_mul]
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b w => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem actHom_tmul (g : F ≃ₐ[K₀] F) (b : B) (w : W') :
    actHom W R₀ B K₀ F W' g (b ⊗ₜ[W] w) = (galRestrict R₀ K₀ F B g b) ⊗ₜ[W] w := by
  change Algebra.TensorProduct.congr _ _ (b ⊗ₜ[W] w) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

variable (W R₀ B K₀ F W') in

noncomputable def act : MulSemiringAction (F ≃ₐ[K₀] F) (B ⊗[W] W') :=
  MulSemiringAction.compHom (B ⊗[W] W') (actHom W R₀ B K₀ F W')

theorem act_smul_tmul (g : F ≃ₐ[K₀] F) (b : B) (w : W') :
    letI := act W R₀ B K₀ F W'
    g • (b ⊗ₜ[W] w) = (galRestrict R₀ K₀ F B g b) ⊗ₜ[W] w :=
  actHom_tmul g b w

noncomputable def actB (R₀ B K₀ F : Type*) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K₀] [Field F]
    [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F]
    [Algebra B F] [IsScalarTower R₀ B F] [IsIntegralClosure B R₀ F] [Algebra.IsAlgebraic K₀ F] :
    MulSemiringAction (F ≃ₐ[K₀] F) B :=
  MulSemiringAction.compHom B (galRestrict R₀ K₀ F B).toMonoidHom

omit [IsDomain R₀] [IsDomain B] [IsScalarTower W R₀ B] in
theorem actB_smul (g : F ≃ₐ[K₀] F) (b : B) :
    letI := actB R₀ B K₀ F
    g • b = galRestrict R₀ K₀ F B g b := rfl

theorem isGaloisGroup_B [IsGalois K₀ F] :
    letI := actB R₀ B K₀ F
    IsGaloisGroup (F ≃ₐ[K₀] F) R₀ B := by
  letI := actB R₀ B K₀ F
  haveI : SMulDistribClass (F ≃ₐ[K₀] F) B F := ⟨fun g b x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', actB_smul, algebraMap_galRestrict_apply]
    rfl⟩
  exact IsGaloisGroup.of_isFractionRing (F ≃ₐ[K₀] F) R₀ B K₀ F

end Action

attribute [local instance] FractionRing.liftAlgebra in

theorem galois_frame
    {W : Type u} [CommRing W]
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra W R₀]
    {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra W B] [Algebra R₀ B]
    [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    {K₀ : Type uK} {F : Type uF} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Field F] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F]
    [IsFractionRing B F] [FiniteDimensional K₀ F] [IsGalois K₀ F]
    (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (n : ℕ) (hdeg : Module.finrank K₀ F = n)
    {W' : Type u} [CommRing W'] [Algebra W W'] [Module.Free W W'] [Module.Finite W W']
    (hBS : Function.Injective (algebraMap B (B ⊗[W] W')))
    (R₀' : Type u) [CommRing R₀'] [IsDomain R₀'] [Algebra R₀' (B ⊗[W] W')] [IsDomain (B ⊗[W] W')]
    [FaithfulSMul R₀' (B ⊗[W] W')]
    (hrange : ∀ s : B ⊗[W] W', s ∈ Set.range (algebraMap R₀' (B ⊗[W] W')) ↔
      s ∈ Set.range (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W'))) :
    ∃ (K₀' : Type u) (_ : Field K₀') (_ : Algebra R₀' K₀') (_ : IsFractionRing R₀' K₀')
      (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R₀' F')
      (_ : IsScalarTower R₀' K₀' F')
      (_ : Algebra (B ⊗[W] W') F') (_ : IsScalarTower R₀' (B ⊗[W] W') F') (_ : IsFractionRing (B ⊗[W] W') F')
      (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
      IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = n := by
  classical
  letI iB := actB R₀ B K₀ F
  letI iS := act W R₀ B K₀ F W'
  have hGB := isGaloisGroup_B (R₀ := R₀) (B := B) (K₀ := K₀) (F := F)

  set toB' := Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W') with htoB'
  have hfix_toB' : ∀ (g : F ≃ₐ[K₀] F) (z : R₀ ⊗[W] W'), g • toB' z = toB' z := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul r w =>
      rw [htoB', Algebra.TensorProduct.map_tmul, act_smul_tmul, IsScalarTower.coe_toAlgHom', AlgEquiv.commutes]
    | add x y hx hy => rw [map_add, smul_add, hx, hy]

  have hGS : IsGaloisGroup (F ≃ₐ[K₀] F) R₀' (B ⊗[W] W') := by
    refine ⟨⟨fun {g₁ g₂} h => ?_⟩, ⟨fun g r s => ?_⟩, ⟨fun s hs => ?_⟩⟩
    ·
      apply hGB.faithful.eq_of_smul_eq_smul
      intro b
      apply hBS
      have := h (b ⊗ₜ[W] (1 : W'))
      rw [act_smul_tmul, act_smul_tmul] at this
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply]
      exact this
    ·
      obtain ⟨z, hz⟩ := (hrange (algebraMap R₀' (B ⊗[W] W') r)).mp ⟨r, rfl⟩
      rw [Algebra.smul_def, Algebra.smul_def, smul_mul', ← hz, hfix_toB']
    ·
      let bW := Module.Free.chooseBasis W W'
      let bS := Algebra.TensorProduct.basis B bW
      have hrepr : ∀ (a : B) (j : Module.Free.ChooseBasisIndex W W'),
          bS.repr (a ⊗ₜ[W] bW j) = Finsupp.single j a := fun a j => by
        rw [Algebra.TensorProduct.basis_repr_tmul, Module.Basis.repr_self, Finsupp.mapRange_single, map_one,
          Finsupp.smul_single_one]
      have hs' : s = ∑ j ∈ (bS.repr s).support, (bS.repr s j) ⊗ₜ[W] bW j := by
        conv_lhs => rw [← bS.linearCombination_repr s, Finsupp.linearCombination_apply, Finsupp.sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.TensorProduct.basis_repr_symm_apply' bW]
      have hcoord : ∀ (g : F ≃ₐ[K₀] F) (i : Module.Free.ChooseBasisIndex W W'),
          bS.repr (g • s) i = g • bS.repr s i := by
        intro g i
        have hgs : g • s = ∑ j ∈ (bS.repr s).support, (g • bS.repr s j) ⊗ₜ[W] bW j := by
          conv_lhs => rw [hs', Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [act_smul_tmul]; rfl
        rw [hgs, map_sum, Finsupp.finsetSum_apply]
        simp only [hrepr, Finsupp.single_apply]
        rw [Finset.sum_ite_eq']
        by_cases h0 : bS.repr s i = 0
        · rw [if_neg (by rw [Finsupp.mem_support_iff, not_not]; exact h0), h0, smul_zero]
        · rw [if_pos (Finsupp.mem_support_iff.mpr h0)]
      have hfixc : ∀ i, ∃ r : R₀, algebraMap R₀ B r = bS.repr s i := fun i =>
        hGB.isInvariant.isInvariant _ fun g => by rw [← hcoord, hs g]
      choose r hr using hfixc
      refine (hrange s).mpr ⟨∑ j ∈ (bS.repr s).support, r j ⊗ₜ[W] bW j, ?_⟩
      rw [map_sum]
      conv_rhs => rw [← bS.linearCombination_repr s, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', hr, Algebra.TensorProduct.basis_repr_symm_apply' bW]
      rfl

  haveI : Finite (F ≃ₐ[K₀] F) := inferInstance
  haveI : Module.IsTorsionFree R₀' (B ⊗[W] W') := Module.IsTorsionFree.of_smul_eq_zero fun r s h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h0 => FaithfulSMul.algebraMap_injective R₀' (B ⊗[W] W') (by rw [h0, map_zero])
  haveI := hGS
  letI actF' := IsFractionRing.mulSemiringAction (F ≃ₐ[K₀] F) (B ⊗[W] W') (FractionRing (B ⊗[W] W'))
  have hGF : IsGaloisGroup (F ≃ₐ[K₀] F) (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.toFractionRing (F ≃ₐ[K₀] F) R₀' (B ⊗[W] W')
  haveI := hGF
  haveI hfd : FiniteDimensional (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.finiteDimensional (F ≃ₐ[K₀] F) _ _
  haveI hgal : IsGalois (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.isGalois (F ≃ₐ[K₀] F) _ _
  have hcyc' : IsCyclic ((FractionRing (B ⊗[W] W')) ≃ₐ[FractionRing R₀'] (FractionRing (B ⊗[W] W'))) :=
    isCyclic_of_surjective _ (IsGaloisGroup.mulEquivAlgEquiv (F ≃ₐ[K₀] F) (FractionRing R₀')
      (FractionRing (B ⊗[W] W'))).surjective
  have hdeg' : Module.finrank (FractionRing R₀') (FractionRing (B ⊗[W] W')) = n := by
    rw [← IsGaloisGroup.card_eq_finrank (F ≃ₐ[K₀] F), IsGalois.card_aut_eq_finrank, hdeg]
  exact ⟨FractionRing R₀', inferInstance, inferInstance, inferInstance, FractionRing (B ⊗[W] W'), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfd, hgal, hcyc', hdeg'⟩

end Frame
end KDMbis44

namespace KDMbis44
namespace U

theorem height_eq_one_of_ne_bot_of_not_isMaximal {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) (𝔭 : Ideal R) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (hm : ¬ 𝔭.IsMaximal) :
    𝔭.height = 1 := by
  have hmax : (IsLocalRing.maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at this
    exact WithBot.coe_injective (by rw [this]; rfl)
  haveI : (IsLocalRing.maximalIdeal R).FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hmax]; decide))
  have hlt : 𝔭 < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') fun h => hm (h ▸ inferInstance)
  have h2 : 𝔭.height < 2 := hmax ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  haveI : (⊥ : Ideal R).FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [Ideal.height_bot]; decide))
  have h1 : (⊥ : Ideal R).height < 𝔭.height := Ideal.height_strict_mono_of_isPrime (bot_lt_iff_ne_bot.mpr h0)
  rw [Ideal.height_bot] at h1
  have hne : 𝔭.height ≠ ⊤ := ne_top_of_lt h2
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at h1 h2 ⊢
  have h1' : 0 < k := by exact_mod_cast h1
  have h2' : k < 2 := by exact_mod_cast h2
  have : k = 1 := by omega
  rw [this]; rfl

theorem isUnramifiedAt_of_not_isMaximal
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hdim : ringKrullDim R₀ = 2)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 → Algebra.IsUnramifiedAt R₀ 𝔭)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hm : ¬ 𝔮.IsMaximal) : Algebra.IsUnramifiedAt R₀ 𝔮 := by
  by_cases h0 : 𝔮 = ⊥
  · subst h0

    haveI : Algebra.FormallyUnramified R₀ K₀ :=
      Algebra.FormallyUnramified.of_isLocalization (Rₘ := K₀) (nonZeroDivisors R₀)
    haveI : Algebra.FormallyUnramified K₀ F := Algebra.FormallyUnramified.of_isSeparable K₀ F
    haveI : Algebra.FormallyUnramified R₀ F := Algebra.FormallyUnramified.comp R₀ K₀ F
    haveI : IsLocalization ((⊥ : Ideal B).primeCompl) F := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] F :=
      IsLocalization.algEquiv ((⊥ : Ideal B).primeCompl) (Localization.AtPrime (⊥ : Ideal B)) F
    exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars R₀).symm
  · have hne : 𝔮.comap (algebraMap R₀ B) ≠ ⊥ := fun h => h0 (Ideal.eq_bot_of_comap_eq_bot h)
    have hnm : ¬ (𝔮.comap (algebraMap R₀ B)).IsMaximal := fun h =>
      hm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R₀) 𝔮 h)
    exact hunr 𝔮 (height_eq_one_of_ne_bot_of_not_isMaximal hdim _ hne hnm)

theorem isUnramifiedAt_baseChange_of_height_eq_one
    {W : Type*} [CommRing W]
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [Algebra W R₀] (hdim : ringKrullDim R₀ = 2)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 → Algebra.IsUnramifiedAt R₀ 𝔭)
    {W' : Type*} [CommRing W'] [Algebra W W'] [Algebra.FormallyUnramified W W'] [Module.Finite W W']
    (R₀' : Type*) [CommRing R₀'] [IsLocalRing R₀'] (hdim' : ringKrullDim R₀' = 2)
    [Algebra R₀' (B ⊗[W] W')] [Module.Finite R₀' (B ⊗[W] W')]
    [Algebra R₀ R₀'] [IsScalarTower R₀ R₀' (B ⊗[W] W')]
    (𝔭 : Ideal (B ⊗[W] W')) [𝔭.IsPrime] (hht : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 1) :
    Algebra.IsUnramifiedAt R₀' 𝔭 := by

  have hnm : ¬ 𝔭.IsMaximal := by
    intro hmax𝔭
    haveI : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭
    have h2 : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 2 := by
      rw [IsLocalRing.eq_maximalIdeal (inferInstance : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal)]
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀')
      rw [hdim'] at this
      exact WithBot.coe_injective (by rw [this]; rfl)
    rw [h2] at hht
    exact absurd hht (by decide)

  have hqnm : ¬ (𝔭.under B).IsMaximal := fun h =>
    hnm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B) 𝔭 h)

  haveI : Algebra.IsUnramifiedAt R₀ (𝔭.under B) := isUnramifiedAt_of_not_isMaximal hdim K₀ F hunr _ hqnm
  haveI : Algebra.IsUnramifiedAt B 𝔭 := inferInstance
  haveI : Algebra.IsUnramifiedAt R₀ 𝔭 := Algebra.IsUnramifiedAt.comp (𝔭.under B) 𝔭
  exact Algebra.IsUnramifiedAt.of_restrictScalars R₀ 𝔭

end U
end KDMbis44

open KDMbis44 in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hmW : IsUnit (m : W))
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra (UVCrossingModel W (π ^ (m * n))) B] [Module.Finite (UVCrossingModel W (π ^ (m * n))) B]
    [FaithfulSMul (UVCrossingModel W (π ^ (m * n))) B]
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀] [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    [Algebra B F] [IsScalarTower (UVCrossingModel W (π ^ (m * n))) B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = n)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (m * n))) B)).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (m * n))) 𝔭)
    (hres : ∀ b : B, ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w) ∈ IsLocalRing.maximalIdeal B) :
    ∃ e : B ≃+* UVCrossingModel W (π ^ m),
      ∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w)) = const (π ^ m) w := by
  classical
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hmnW : IsUnit ((m * n : ℕ) : W) := by rw [Nat.cast_mul]; exact hmW.mul hnW

  letI algWB : Algebra W B :=
    ((algebraMap (UVCrossingModel W (π ^ (m * n))) B).comp (algebraMap W (UVCrossingModel W (π ^ (m * n))))).toAlgebra
  haveI : IsScalarTower W (UVCrossingModel W (π ^ (m * n))) B :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := UVCrossingModel W (π ^ (m * n))) (A := B) fun _ => rfl

  haveI : NeZero ((m * n : ℕ) : IsLocalRing.ResidueField W) := ⟨by
    have := hmnW.map (IsLocalRing.residue W)
    rw [map_natCast] at this
    exact this.ne_zero⟩
  haveI : NeZero (m * n) := ⟨hN.ne'⟩
  haveI : IsCyclotomicExtension {m * n} (IsLocalRing.ResidueField W)
      (CyclotomicField (m * n) (IsLocalRing.ResidueField W)) :=
    CyclotomicField.isCyclotomicExtension (m * n) (IsLocalRing.ResidueField W)
  haveI : FiniteDimensional (IsLocalRing.ResidueField W) (CyclotomicField (m * n) (IsLocalRing.ResidueField W)) :=
    IsCyclotomicExtension.finiteDimensional {m * n} (IsLocalRing.ResidueField W) _
  haveI : IsGalois (IsLocalRing.ResidueField W) (CyclotomicField (m * n) (IsLocalRing.ResidueField W)) :=
    IsCyclotomicExtension.isGalois {m * n} (IsLocalRing.ResidueField W) _
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField W) (CyclotomicField (m * n) (IsLocalRing.ResidueField W)) :=
    IsCyclotomicExtension.isSeparable {m * n} (IsLocalRing.ResidueField W) _
  obtain ⟨W', _, _, _, _, _, _, _, _, _, _, ι, hmax, hιres, hrank, hfin, hgal⟩ :=
    IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete W
      (CyclotomicField (m * n) (IsLocalRing.ResidueField W))
  obtain ⟨hcard, hinv⟩ := hgal inferInstance
  haveI : Fintype (W' ≃ₐ[W] W') := Fintype.ofFinite _

  have hπ' : Irreducible (algebraMap W W' π) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [← hmax, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnW' : IsUnit ((n : ℕ) : W') := by have := hnW.map (algebraMap W W'); rwa [map_natCast] at this
  have hmW' : IsUnit ((m : ℕ) : W') := by have := hmW.map (algebraMap W W'); rwa [map_natCast] at this
  have hmnW' : IsUnit ((m * n : ℕ) : W') := by rw [Nat.cast_mul]; exact hmW'.mul hnW'

  have hμ' : ∃ ζ : W', IsPrimitiveRoot ζ (m * n) := by
    refine IsAdicComplete.exists_isPrimitiveRoot_of_residueField (m * n) hN hmnW' ?_
    exact ⟨ι.symm (IsCyclotomicExtension.zeta (m * n) (IsLocalRing.ResidueField W)
        (CyclotomicField (m * n) (IsLocalRing.ResidueField W))),
      (IsCyclotomicExtension.zeta_spec (m * n) (IsLocalRing.ResidueField W)
        (CyclotomicField (m * n) (IsLocalRing.ResidueField W))).map_of_injective ι.symm.injective⟩

  set π' : W' := algebraMap W W' π with hπ'def

  obtain ⟨eM, heM, heMU, heMV, heMc⟩ :=
    ModularCurve.UVCrossingModel.exists_algEquiv_tensorProduct_map_of_finite_of_free W W' (π ^ (m * n))
  have hcast : algebraMap W W' (π ^ (m * n)) = π' ^ (m * n) := by rw [map_pow]
  let castM : UVCrossingModel W' (algebraMap W W' (π ^ (m * n))) ≃+* UVCrossingModel W' (π' ^ (m * n)) :=
    Ideal.quotEquivOfEq (by rw [hcast])

  let toB' : UVCrossingModel W (π ^ (m * n)) ⊗[W] W' →ₐ[W] B ⊗[W] W' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom W (UVCrossingModel W (π ^ (m * n))) B) (AlgHom.id W W')
  letI algR'B' : Algebra (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') :=
    (toB'.toRingHom.comp (eM.symm.toRingEquiv.toRingHom.comp castM.symm.toRingHom)).toAlgebra

  have hWB : Function.Injective (algebraMap W B) :=
    (FaithfulSMul.algebraMap_injective (UVCrossingModel W (π ^ (m * n))) B).comp
      (KDMbis44.G.algebraMap_uvCrossingModel_injective π hπ (m * n) hN)
  have hres0 : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B := hres

  haveI : IsLocalRing (B ⊗[W] W') := KDMbis44.G.isLocalRing_tensorProduct hWB hres0
  haveI : IsNoetherianRing (B ⊗[W] W') := KDMbis44.G.isNoetherianRing_tensorProduct
  obtain ⟨hdomB', hicB'⟩ :=
    Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing (W := W) B W'
  haveI := hdomB'
  haveI := hicB'
  haveI : Module.Finite (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') := by
    change (toB'.toRingHom.comp (eM.symm.toRingEquiv.toRingHom.comp castM.symm.toRingHom)).Finite
    exact KDMbis44.G.map_toAlgHom_finite.comp
      (RingHom.Finite.of_surjective _ (eM.symm.surjective.comp castM.symm.surjective))
  haveI : FaithfulSMul (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      change Function.Injective (toB'.toRingHom.comp (eM.symm.toRingEquiv.toRingHom.comp castM.symm.toRingHom))
      exact KDMbis44.G.map_toAlgHom_injective.comp (eM.symm.injective.comp castM.symm.injective))

  obtain ⟨K₀', _, _, _, F', _, _, _, _, _, _, _, _, _, hcyc', hdeg'⟩ :
      ∃ (K₀' : Type u_1) (_ : Field K₀') (_ : Algebra (UVCrossingModel W' (π' ^ (m * n))) K₀')
        (_ : IsFractionRing (UVCrossingModel W' (π' ^ (m * n))) K₀')
        (F' : Type (max u_1 u_2)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra (UVCrossingModel W' (π' ^ (m * n))) F')
        (_ : IsScalarTower (UVCrossingModel W' (π' ^ (m * n))) K₀' F')
        (_ : Algebra (B ⊗[W] W') F') (_ : IsScalarTower (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') F')
        (_ : IsFractionRing (B ⊗[W] W') F')
        (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
        IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = n := by
    haveI : IsDomain (UVCrossingModel W (π ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (m * n) hN).1
    haveI : IsIntegrallyClosed (UVCrossingModel W (π ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (m * n) hN).2.2
    haveI : IsDomain (UVCrossingModel W' (π' ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π' hπ' (m * n) hN).1
    haveI : Module.IsTorsionFree W B := Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h0 => hWB (by rw [h0, map_zero])
    have hBS : Function.Injective (algebraMap B (B ⊗[W] W')) := by
      intro a b h
      apply Algebra.TensorProduct.includeLeft_injective (R := W) (S := W) (A := B) (B := W')
        (FaithfulSMul.algebraMap_injective W W')
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply] at h
      exact h
    have hrange : ∀ s : B ⊗[W] W', s ∈ Set.range (algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W')) ↔
        s ∈ Set.range toB' := fun s => by
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨eM.symm (castM.symm r), rfl⟩
      · rintro ⟨z, rfl⟩
        refine ⟨castM (eM z), ?_⟩
        change toB' (eM.symm (castM.symm (castM (eM z)))) = toB' z
        rw [RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    exact KDMbis44.Frame.galois_frame hcyc n hdeg hBS (UVCrossingModel W' (π' ^ (m * n))) hrange
  have hunr' : ∀ (𝔭 : Ideal (B ⊗[W] W')) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W'))).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W' (π' ^ (m * n))) 𝔭 := by
    intro 𝔭 _ hht
    haveI : IsLocalRing (UVCrossingModel W (π ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (m * n) hN).2.1
    haveI : IsDomain (UVCrossingModel W (π ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (m * n) hN).1
    haveI : IsLocalRing (UVCrossingModel W' (π' ^ (m * n))) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π' hπ' (m * n) hN).2.1
    have hdimR : ringKrullDim (UVCrossingModel W (π ^ (m * n))) = 2 :=
      le_antisymm (ModularCurve.UVCrossingModel.ringKrullDim_le_two π hπ (m * n) hN)
        (ModularCurve.UVCrossingModel.two_le_ringKrullDim π hπ (m * n) hN)
    have hdimR' : ringKrullDim (UVCrossingModel W' (π' ^ (m * n))) = 2 :=
      le_antisymm (ModularCurve.UVCrossingModel.ringKrullDim_le_two π' hπ' (m * n) hN)
        (ModularCurve.UVCrossingModel.two_le_ringKrullDim π' hπ' (m * n) hN)

    letI algRR' : Algebra (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W' (π' ^ (m * n))) :=
      ((castM.toRingHom.comp eM.toRingEquiv.toRingHom).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := W) (A := UVCrossingModel W (π ^ (m * n))) (B := W'))).toAlgebra
    haveI : IsScalarTower (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') :=
      IsScalarTower.of_algebraMap_eq fun r => by
        show algebraMap (UVCrossingModel W (π ^ (m * n))) (B ⊗[W] W') r =
          toB' (eM.symm (castM.symm (castM (eM (r ⊗ₜ[W] (1 : W'))))))
        rw [RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one,
          IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.algebraMap_apply]
    exact KDMbis44.U.isUnramifiedAt_baseChange_of_height_eq_one hdimR K₀ F hunr
      (UVCrossingModel W' (π' ^ (m * n))) hdimR' 𝔭 hht
  have hres' : ∀ b : B ⊗[W] W', ∃ w : W',
      b - algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') (const (π' ^ (m * n)) w) ∈
        IsLocalRing.maximalIdeal (B ⊗[W] W') := by
    have hc : ∀ w' : W', algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') (const (π' ^ (m * n)) w') =
        (1 : B) ⊗ₜ[W] w' := by
      intro w'
      show toB' (eM.symm (castM.symm (const (π' ^ (m * n)) w'))) = _
      have h1 : castM.symm (const (π' ^ (m * n)) w') = const (algebraMap W W' (π ^ (m * n))) w' := by
        show (Ideal.quotEquivOfEq _).symm (Ideal.Quotient.mk _ (MvPowerSeries.C w')) =
          Ideal.Quotient.mk _ (MvPowerSeries.C w')
        rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
      have h2 : eM.symm (const (algebraMap W W' (π ^ (m * n))) w') = (1 : UVCrossingModel W (π ^ (m * n))) ⊗ₜ[W] w' := by
        have := heM 1 w'
        rw [map_one, map_one, map_one, mul_one] at this
        rw [← this, AlgEquiv.symm_apply_apply]
      rw [h1, h2, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    intro b
    exact KDMbis44.G.exists_sub_mem_maximalIdeal_tensorProduct hres0 _ hc b

  obtain ⟨e', he'⟩ :=
    ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul π' hπ' m n hm hn hnW' hmW' hμ' (B ⊗[W] W') K₀' F' hcyc' hdeg' hunr' hres'

  let x' : B ⊗[W] W' := e'.symm (U (π' ^ m))
  let y' : B ⊗[W] W' := e'.symm (V (π' ^ m))
  have hπB' : algebraMap W (B ⊗[W] W') π ≠ 0 := by
    exact KDMbis44.G.algebraMap_tensorProduct_ne_zero hWB π hπ'.ne_zero
  have hreg : IsSMulRegular (B ⊗[W] W') (algebraMap W (B ⊗[W] W') π) :=
    fun a b h => mul_left_cancel₀ hπB' h

  have halgc : ∀ w : W, algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W')
      (const (π' ^ (m * n)) (algebraMap W W' w)) = algebraMap W (B ⊗[W] W') w := by
    intro w
    show toB' (eM.symm (castM.symm (const (π' ^ (m * n)) (algebraMap W W' w)))) = _
    have h1 : castM.symm (const (π' ^ (m * n)) (algebraMap W W' w)) =
        const (algebraMap W W' (π ^ (m * n))) (algebraMap W W' w) := by
      show (Ideal.quotEquivOfEq _).symm (Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap W W' w))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap W W' w))
      rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    have h2 : eM.symm (const (algebraMap W W' (π ^ (m * n))) (algebraMap W W' w)) =
        const (π ^ (m * n)) w ⊗ₜ[W] (1 : W') := by
      rw [← heMc w, AlgEquiv.symm_apply_apply]
    have h3 : toB' (const (π ^ (m * n)) w ⊗ₜ[W] (1 : W')) = algebraMap W (B ⊗[W] W') w := by
      have hcw : const (π ^ (m * n)) w = algebraMap W (UVCrossingModel W (π ^ (m * n))) w := by
        show Ideal.Quotient.mk _ (MvPowerSeries.C w) = Ideal.Quotient.mk _ (algebraMap W (MvPowerSeries (Fin 2) W) w)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom', hcw,
        ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [h1, h2, h3]
  have hsymm : ∀ w' : W', e'.symm (const (π' ^ m) w') =
      algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') (const (π' ^ (m * n)) w') := fun w' => by
    rw [← he' w', RingEquiv.symm_apply_apply]
  have hsymmπ : e'.symm (const (π' ^ m) π') = algebraMap W (B ⊗[W] W') π := by
    rw [hsymm]
    exact halgc π
  have hxy : x' * y' = algebraMap W (B ⊗[W] W') π ^ m * ↑(1 : (B ⊗[W] W')ˣ) := by
    have hUV : U (π' ^ m) * V (π' ^ m) = const (π' ^ m) (π' ^ m) := U_mul_V_eq_const _
    show e'.symm (U (π' ^ m)) * e'.symm (V (π' ^ m)) = _
    rw [← map_mul, hUV, hsymm, Units.val_one, mul_one,
      show π' ^ m = algebraMap W W' (π ^ m) from (map_pow (algebraMap W W') π m).symm, halgc, map_pow]
  have hmaxB' : IsLocalRing.maximalIdeal (B ⊗[W] W') =
      Ideal.span {algebraMap W (B ⊗[W] W') π, x', y'} := by
    haveI : IsLocalRing (UVCrossingModel W' (π' ^ m)) :=
      (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π' hπ' m hm).2.1
    have hπ'm : π' ^ m ∈ IsLocalRing.maximalIdeal W' :=
      Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ'.not_isUnit) _ hm
    have hM := maximalIdeal_uvCrossingModel_eq_span π' hπ'.maximalIdeal_eq (π' ^ m) hπ'm
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e'.symm, hM, Ideal.map_span, Set.image_insert_eq,
      Set.image_insert_eq, Set.image_singleton]
    show Ideal.span {e'.symm (const (π' ^ m) π'), e'.symm (U (π' ^ m)), e'.symm (V (π' ^ m))} = _
    rw [hsymmπ]

  haveI : IsDomain (UVCrossingModel W' (π' ^ (m * n))) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π' hπ' (m * n) hN).1
  haveI : IsIntegrallyClosed (UVCrossingModel W' (π' ^ (m * n))) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π' hπ' (m * n) hN).2.2
  have hβ : ∀ (X : MvPowerSeries (Fin 2) W) (X' : MvPowerSeries (Fin 2) W'),
      MvPowerSeries.map (algebraMap W W') X = X' →
      eM (UVCrossingModel.mk (π ^ (m * n)) X ⊗ₜ[W] 1) = UVCrossingModel.mk (algebraMap W W' (π ^ (m * n))) X' →
      algebraMap (UVCrossingModel W' (π' ^ (m * n))) (B ⊗[W] W') (UVCrossingModel.mk (π' ^ (m * n)) X') =
        algebraMap (UVCrossingModel W (π ^ (m * n))) B (UVCrossingModel.mk (π ^ (m * n)) X) ⊗ₜ[W] (1 : W') := by
    intro X X' hX hE
    show toB' (eM.symm (castM.symm (UVCrossingModel.mk (π' ^ (m * n)) X'))) = _
    have h1 : castM.symm (UVCrossingModel.mk (π' ^ (m * n)) X') =
        UVCrossingModel.mk (algebraMap W W' (π ^ (m * n))) X' := by
      show (Ideal.quotEquivOfEq _).symm (Ideal.Quotient.mk _ X') = Ideal.Quotient.mk _ X'
      rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    have h2 : eM.symm (UVCrossingModel.mk (algebraMap W W' (π ^ (m * n))) X') =
        UVCrossingModel.mk (π ^ (m * n)) X ⊗ₜ[W] (1 : W') := by
      rw [← hE, AlgEquiv.symm_apply_apply]
    rw [h1, h2, Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom']
  obtain ⟨hstabx, hstaby⟩ := KDMbis44.BP.branch_pin π hπ' m hm e' hsymmπ
      (UVCrossingModel W' (π' ^ (m * n))) (const (π' ^ (m * n)) π') (U (π' ^ (m * n))) (V (π' ^ (m * n)))
      (m * n) hN (KDMbis44.BP.U_mul_V_eq_const_pow _ _ _ rfl)
      (KDMbis44.BP.U_notMem_span_const π' hπ' (m * n) hN) (KDMbis44.BP.V_notMem_span_const π' hπ' (m * n) hN)
      (halgc π) (algebraMap (UVCrossingModel W (π ^ (m * n))) B (U (π ^ (m * n))))
      (algebraMap (UVCrossingModel W (π ^ (m * n))) B (V (π ^ (m * n))))
      (hβ (MvPowerSeries.X 0) (MvPowerSeries.X 0) (MvPowerSeries.map_X _ 0) heMU)
      (hβ (MvPowerSeries.X 1) (MvPowerSeries.X 1) (MvPowerSeries.map_X _ 1) heMV)
  obtain ⟨x, y, u, hxyB, hmaxB, -, -⟩ :=
    IsLocalRing.exists_crossingPresentation_of_baseChange_of_forall_map_span_eq (W := W) (W' := W') (S := B)
      (Γ := W' ≃ₐ[W] W') hinv (by rw [← hcard]; exact (Nat.card_eq_fintype_card).symm) π m hreg x' y' 1 hxy hmaxB' hstabx hstaby

  have hθ : ∃ θ : MvPowerSeries (Fin 2) W →+* AdicCompletion (IsLocalRing.maximalIdeal B) B,
      Function.Surjective θ ∧ θ (MvPowerSeries.X 0) = algebraMap B _ x ∧ θ (MvPowerSeries.X 1) = algebraMap B _ y ∧
      ∀ o : W, θ (MvPowerSeries.C o) = algebraMap B _ (algebraMap W B o) :=
    KDMbis44.exists_surjective_mvPowerSeries_adicCompletion π hπ x y hmaxB (fun b => hres b)
  obtain ⟨θ, hθsurj, hθX, hθY, hθC⟩ := hθ
  have hdim : 2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    KDMbis44.two_le_ringKrullDim_adicCompletion_of_uvCrossingModel π hπ (m * n) hN B
  have hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) =
      θ (MvPowerSeries.C π) ^ m * ((Units.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).toMonoidHom u :
        (AdicCompletion (IsLocalRing.maximalIdeal B) B)ˣ) : AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    KDMbis44.rel_of_apply_eq θ (algebraMap B _) (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.C π)
      x y (algebraMap W B π) m u hθX hθY (hθC π) hxyB
  obtain ⟨ιB, hιBc, -, -⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit π hπ m hm θ hθsurj _ hrel hdim
  obtain ⟨eB, heB⟩ :=
    KDMbis44.exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_uvCrossingModel π hπ (m * n) hN B
  refine ⟨eB.trans ιB, fun w => ?_⟩
  rw [RingEquiv.trans_apply, heB, show algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w) =
      algebraMap W B w from rfl, ← hθC, hιBc]

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit (solution)

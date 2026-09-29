-- Prove2me | solution 1 for MvPowerSeries.isAdicComplete_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fe933123-6c85-5b8b-8164-cd9ee1342aaa

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_isAdicComplete_maximalIdeal

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing Finsupp

variable {σ : Type u} {R : Type v} [CommRing R]

theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem maximalIdeal_eq_comap [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap (constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

theorem coeff_dropVar (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

theorem mem_pow_span_X_of_coeff_eq_zero [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  classical
  haveI := Fintype.ofFinite σ
  set J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) with hJ
  induction k generalizing φ with
  | zero => simp
  | succ k ihk =>
    suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), (∀ m : σ →₀ ℕ, m.degree < k + 1 → coeff m ψ = 0) →
        (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) → ψ ∈ J ^ (k + 1) by
      exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ψ h0 hs
      have : ψ = 0 := by
        ext m
        by_cases hm : m = 0
        · subst hm; rw [map_zero]; exact h0 0 (by simp)
        · rw [map_zero]
          refine hs m fun hsub => hm ?_
          ext j
          have : j ∉ m.support := fun hj => by simpa using hsub hj
          simpa [Finsupp.mem_support_iff] using this
      rw [this]; exact Ideal.zero_mem _
    | insert i s hi ih =>
      intro ψ h0 hs
      have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
        rw [X_dvd_iff]
        intro m hm
        rw [map_sub, coeff_dropVar, if_pos hm, sub_self]
      obtain ⟨q, hq⟩ := hdiv
      have hqk : ∀ m : σ →₀ ℕ, m.degree < k → coeff m q = 0 := by
        intro m hm
        have h1 : coeff (Finsupp.single i 1 + m) (X i * q) = coeff m q := by
          rw [X, coeff_add_monomial_mul, one_mul]
        have h2 : coeff (Finsupp.single i 1 + m) (ψ - dropVar i ψ) = 0 := by
          rw [map_sub, coeff_dropVar, if_neg (by simp), sub_zero]
          exact h0 _ (by rw [map_add, Finsupp.degree_single]; omega)
        rw [← h1, ← hq, h2]
      have hrest : dropVar i ψ ∈ J ^ (k + 1) := by
        refine ih _ ?_ ?_
        · intro m hm
          rw [coeff_dropVar]
          split_ifs
          · exact h0 m hm
          · rfl
        · intro m hm
          rw [coeff_dropVar]
          split_ifs with hmi
          · refine hs m fun hsub => hm fun j hj => ?_
            rcases Finset.mem_insert.mp (hsub hj) with rfl | h
            · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
            · exact h
          · rfl
      have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
      rw [this, pow_succ']
      exact Ideal.add_mem _ (pow_succ' J k ▸ hrest)
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ihk q hqk))

theorem sub_truncTotal_mem_pow_span_X [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncTotal k φ : MvPolynomial σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  refine mem_pow_span_X_of_coeff_eq_zero k _ fun m hm => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]

section LocalCoeff

variable [IsLocalRing R]

local notation "𝔐" => maximalIdeal (MvPowerSeries σ R)
local notation "𝔪" => maximalIdeal R

theorem coeff_mem_pow_of_mem_pow (n : ℕ) (x : MvPowerSeries σ R) (hx : x ∈ 𝔐 ^ n) (m : σ →₀ ℕ) :
    coeff m x ∈ 𝔪 ^ (n - m.degree) := by
  classical
  induction n generalizing x m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add, hp]
      by_cases hp2 : p.2 = 0
      ·
        have hp1 : p.1 = m := by simpa [hp2] using hp
        have hz0 : coeff p.2 z ∈ 𝔪 := by
          rw [hp2, coeff_zero_eq_constantCoeff_apply]
          rw [maximalIdeal_eq_comap, Ideal.mem_comap] at hz
          exact hz
        have hmem := Ideal.mul_mem_mul (ih y hy p.1) hz0
        rw [← pow_succ] at hmem
        rw [hp1] at hmem ⊢
        have hle : n + 1 - m.degree ≤ n - m.degree + 1 := by omega
        exact Ideal.pow_le_pow_right hle hmem
      ·
        have hp2' : 0 < p.2.degree := by
          rw [Nat.pos_iff_ne_zero, Ne, Finsupp.degree_eq_zero_iff]
          exact hp2
        have hmem := Ideal.mul_mem_right (coeff p.2 z) _ (ih y hy p.1)
        have hle : n + 1 - m.degree ≤ n - p.1.degree := by omega
        exact Ideal.pow_le_pow_right hle hmem
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz

theorem C_mem_pow (k : ℕ) (c : R) (hc : c ∈ 𝔪 ^ k) : (C c : MvPowerSeries σ R) ∈ 𝔐 ^ k := by
  have h : (𝔪).map (C (σ := σ) (R := R)) ≤ 𝔐 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_C]
    exact ha
  have := Ideal.pow_right_mono h k
  rw [← Ideal.map_pow] at this
  exact this (Ideal.mem_map_of_mem _ hc)

theorem span_X_le : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ 𝔐 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_X]
  exact Ideal.zero_mem _

variable [Finite σ]

theorem monomial_one_mem_pow (m : σ →₀ ℕ) : (monomial m (1 : R) : MvPowerSeries σ R) ∈ 𝔐 ^ m.degree := by
  classical
  refine Ideal.pow_right_mono span_X_le m.degree (mem_pow_span_X_of_coeff_eq_zero _ _ fun m' hm' => ?_)
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact lt_irrefl _ hm'

theorem monomial_mem_pow (n : ℕ) (m : σ →₀ ℕ) (c : R) (hc : c ∈ 𝔪 ^ (n - m.degree)) :
    (monomial m c : MvPowerSeries σ R) ∈ 𝔐 ^ n := by
  have : (monomial m c : MvPowerSeries σ R) = C c * monomial m 1 := by
    rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  rw [this]
  have hmem := Ideal.mul_mem_mul (C_mem_pow _ c hc) (monomial_one_mem_pow (R := R) m)
  rw [← pow_add] at hmem
  have hle : n ≤ n - m.degree + m.degree := by omega
  exact Ideal.pow_le_pow_right hle hmem

theorem mem_pow_of_coeff_mem_pow (n : ℕ) (x : MvPowerSeries σ R)
    (hx : ∀ m : σ →₀ ℕ, m.degree < n → coeff m x ∈ 𝔪 ^ (n - m.degree)) : x ∈ 𝔐 ^ n := by
  classical
  have hsplit : x = (truncTotal n x : MvPolynomial σ R) + (x - (truncTotal n x : MvPolynomial σ R)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ (Ideal.pow_right_mono span_X_le n (sub_truncTotal_mem_pow_span_X n x))
  have hcoe : ((truncTotal n x : MvPolynomial σ R) : MvPowerSeries σ R) =
      ∑ m ∈ (finite_of_degree_lt (σ := σ) n).toFinset, monomial m (coeff m x) := by
    rw [truncTotal, truncFinset_apply, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
  rw [hcoe]
  refine Ideal.sum_mem _ fun m hm => monomial_mem_pow n m _ (hx m ?_)
  simpa using hm

theorem isAdicComplete_maximalIdeal [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete 𝔐 (MvPowerSeries σ R) := by
  haveI : IsHausdorff 𝔐 (MvPowerSeries σ R) := ⟨fun x hx => by
    ext m
    rw [map_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff 𝔪 R) (coeff m x) fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hk := hx (k + m.degree)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at hk
    have := coeff_mem_pow_of_mem_pow (k + m.degree) x hk m
    rwa [show k + m.degree - m.degree = k by omega] at this⟩
  have hP : IsPrecomplete 𝔐 (MvPowerSeries σ R) := ⟨fun g hg => by
    have hgd : ∀ {k l : ℕ}, k ≤ l → g l - g k ∈ 𝔐 ^ k := fun h => by
      have := (smodEq_pow_smul_top_iff _ _ _ _).mp (hg h)
      rwa [← neg_sub, Ideal.neg_mem_iff] at this

    have hc : ∀ m : σ →₀ ℕ, ∃ c : R, ∀ k, coeff m (g (k + m.degree)) - c ∈ 𝔪 ^ k := by
      intro m
      obtain ⟨c, hc⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete 𝔪 R)
        (f := fun k => coeff m (g (k + m.degree))) (fun {k l} hkl => by
          rw [smodEq_pow_smul_top_iff, ← map_sub]
          have := coeff_mem_pow_of_mem_pow (k + m.degree) _
            (hgd (show k + m.degree ≤ l + m.degree by omega)) m
          rw [show k + m.degree - m.degree = k by omega] at this
          rwa [← neg_sub, map_neg, Ideal.neg_mem_iff])
      exact ⟨c, fun k => (smodEq_pow_smul_top_iff _ _ _ _).mp (hc k)⟩
    choose c hc using hc
    refine ⟨fun m => c m, fun n => ?_⟩
    rw [smodEq_pow_smul_top_iff]
    refine mem_pow_of_coeff_mem_pow n _ fun m hm => ?_
    rw [map_sub]
    have h := hc m (n - m.degree)
    rw [show n - m.degree + m.degree = n by omega] at h
    exact h⟩
  exact ⟨⟩

end LocalCoeff

end M4cP4PS

theorem solution {σ : Type u} {R : Type v} [Finite σ] [CommRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) :=
  M4cP4PS.isAdicComplete_maximalIdeal

end S_MvPowerSeries_isAdicComplete_maximalIdeal
end P2MW
export P2MW.S_MvPowerSeries_isAdicComplete_maximalIdeal (solution)

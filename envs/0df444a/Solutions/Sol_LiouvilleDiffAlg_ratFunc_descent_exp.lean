-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_descent_exp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:11.50358+00:00
-- url     : https://prove2.me/submissions/ef59728c-cc4a-4e9e-84fa-d1bf7acdb836

import Mathlib
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_liouville_key
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_deriv_poly

open scoped Differential
open Polynomial

private lemma coeff_implicitDeriv_aux {K : Type*} [Field K] [Differential K] (a : K) (p : K[X]) (k : ℕ) :
    (Differential.implicitDeriv (C a * X) p).coeff k = (p.coeff k)′ + a * ((k : K) * p.coeff k) := by
  have : Differential.implicitDeriv (C a * X) p
      = Differential.mapCoeffs p + (C a * X) * derivative p := by
    simp [Differential.implicitDeriv]
  rw [this, coeff_add, Differential.coeff_mapCoeffs, mul_assoc, coeff_C_mul]
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

private lemma xpow_deriv_aux {K : Type*} [Field K] [Differential K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′) * RatFunc.X) (m : ℕ) :
    ((RatFunc.X : RatFunc K) ^ m)′ = algebraMap K (RatFunc K) ((m : K) * s′) * RatFunc.X ^ m := by
  have hne : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have h := Differential.logDeriv_pow m (RatFunc.X : RatFunc K)
  unfold Differential.logDeriv at h
  rw [hX, mul_div_assoc, div_self hne, mul_one] at h
  have hp : (RatFunc.X : RatFunc K) ^ m ≠ 0 := pow_ne_zero _ hne
  rw [div_eq_iff hp] at h
  rw [h]; simp

private lemma const_ratio_aux {K : Type*} [Field K] [Differential K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    {y x : RatFunc K} (hx : x ≠ 0) (c : K)
    (hy : y′ = algebraMap K (RatFunc K) c * y) (hx' : x′ = algebraMap K (RatFunc K) c * x) :
    ∃ k : K, y = algebraMap K (RatFunc K) k * x := by
  have hz : (y / x)′ = 0 := by
    have h1 : y = (y / x) * x := by field_simp
    have h2 : y′ = (y / x)′ * x + (y / x) * x′ := by
      conv_lhs => rw [h1]
      simp [Derivation.leibniz, smul_eq_mul]
      ring
    have h3 : (y / x)′ * x = 0 := by
      have : (y / x)′ * x = y′ - (y / x) * x′ := by rw [h2]; ring
      rw [this, hy, hx']
      conv_lhs => rw [h1]
      field_simp
      ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd h hx
  obtain ⟨k, hk⟩ := hcon _ hz
  exact ⟨k, by rw [hk]; field_simp⟩

private lemma hExc_aux {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′) * RatFunc.X)
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    (p q : K[X]) (hm : Monic p) (hi : Irreducible p) (hne : ¬ p = X)
    (hq : (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q) : ¬ p ∣ q := by
  rintro ⟨lam, hlam⟩
  have hw : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) (C (s′) * X) := by
    simp [hX]
  have hq' : q = Differential.implicitDeriv (C (s′) * X) p := by
    apply RatFunc.algebraMap_injective K
    rw [← hq]
    exact LiouvilleDiffAlg.ratFunc_deriv_poly _ hw p
  set d := p.natDegree with hd
  have hdpos : 0 < d := Irreducible.natDegree_pos hi
  have hp0 : p ≠ 0 := hi.ne_zero
  have hcoef : ∀ k, q.coeff k = (p.coeff k)′ + s′ * ((k : K) * p.coeff k) := by
    intro k; rw [hq']; exact coeff_implicitDeriv_aux _ _ _
  have hqd : q.natDegree ≤ d := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hcoef, coeff_eq_zero_of_natDegree_lt hk]; simp
  have hqd' : q.coeff d = (d : K) * s′ := by
    rw [hcoef, hd, hm.coeff_natDegree]; simp [mul_comm]
  have hlam0 : lam.natDegree = 0 := by
    by_cases hl : lam = 0
    · simp [hl]
    · have := natDegree_mul hp0 hl
      rw [← hlam] at this
      omega
  have hlamC : lam = C (lam.coeff 0) := eq_C_of_natDegree_eq_zero hlam0
  have hl : lam.coeff 0 = (d : K) * s′ := by
    rw [← hqd', hlam, hlamC, coeff_mul_C, hm.coeff_natDegree, one_mul]
    simp
  have hy : (algebraMap K[X] (RatFunc K) p)′
      = algebraMap K (RatFunc K) ((d : K) * s′) * algebraMap K[X] (RatFunc K) p := by
    rw [hq, hlam, hlamC, hl]; simp [mul_comm]
  obtain ⟨k, hk⟩ := const_ratio_aux hcon (pow_ne_zero d RatFunc.X_ne_zero) _ hy (xpow_deriv_aux hX d)
  have hpk : p = C k * X ^ d := by
    apply RatFunc.algebraMap_injective K
    rw [hk]; simp
  have hk1 : k = 1 := by
    have := hm.coeff_natDegree
    rw [← hd, hpk] at this
    simpa using this
  rw [hk1] at hpk
  simp only [map_one, one_mul] at hpk
  have : d = 1 := by
    by_contra h
    exact not_irreducible_pow h (hpk ▸ hi)
  rw [this, pow_one] at hpk
  exact hne hpk

private lemma poly_part_aux {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′) * RatFunc.X)
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    (m : ℕ) (V : K[X]) (T : K) (v : RatFunc K)
    (hvT : v′ = algebraMap K (RatFunc K) T)
    (hv : (RatFunc.X : RatFunc K) ^ m * v = algebraMap K[X] (RatFunc K) V) :
    v = algebraMap K (RatFunc K) (V.coeff m) := by
  have hw : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) (C (s′) * X) := by
    simp [hX]
  have hXm : (RatFunc.X : RatFunc K) ^ m ≠ 0 := pow_ne_zero m RatFunc.X_ne_zero
  have h1 : (algebraMap K[X] (RatFunc K) V)′
      = algebraMap K (RatFunc K) ((m : K) * s′) * algebraMap K[X] (RatFunc K) V
        + (RatFunc.X : RatFunc K) ^ m * algebraMap K (RatFunc K) T := by
    rw [← hv, ← hvT]
    simp only [Derivation.leibniz, xpow_deriv_aux hX m, smul_eq_mul]
    ring
  have h2 : Differential.implicitDeriv (C (s′) * X) V = C ((m : K) * s′) * V + C T * X ^ m := by
    apply RatFunc.algebraMap_injective K
    rw [← LiouvilleDiffAlg.ratFunc_deriv_poly _ hw V, h1]
    simp
    ring
  have h3 : ∀ k : ℕ, (V.coeff k)′ + s′ * ((k : K) * V.coeff k)
      = (m : K) * s′ * V.coeff k + (if k = m then T else 0) := by
    intro k
    have := congrArg (fun P => P.coeff k) h2
    simp only [coeff_implicitDeriv_aux, coeff_add, coeff_C_mul, coeff_X_pow] at this
    simpa using this
  have h4 : ∀ k : ℕ, k ≠ m → V.coeff k = 0 := by
    intro k hk
    have e : (V.coeff k)′ + s′ * ((k : K) * V.coeff k) = (m : K) * s′ * V.coeff k := by
      have := h3 k
      rwa [if_neg hk, add_zero] at this
    have hy : (algebraMap K (RatFunc K) (V.coeff k) * (RatFunc.X : RatFunc K) ^ k)′
        = algebraMap K (RatFunc K) ((m : K) * s′) *
          (algebraMap K (RatFunc K) (V.coeff k) * (RatFunc.X : RatFunc K) ^ k) := by
      simp only [Derivation.leibniz, xpow_deriv_aux hX k, smul_eq_mul, DifferentialAlgebra.deriv_algebraMap]
      have e' : algebraMap K (RatFunc K) ((V.coeff k)′ + s′ * ((k : K) * V.coeff k))
          = algebraMap K (RatFunc K) ((m : K) * s′ * V.coeff k) := by rw [e]
      simp only [map_add, map_mul, map_natCast] at e'
      simp only [map_mul, map_natCast]
      linear_combination (RatFunc.X : RatFunc K) ^ k * e'
    obtain ⟨c0, hc0⟩ := const_ratio_aux hcon hXm _ hy (xpow_deriv_aux hX m)
    have : C (V.coeff k) * X ^ k = C c0 * X ^ m := by
      apply RatFunc.algebraMap_injective K
      simpa using hc0
    have := congrArg (fun P => P.coeff k) this
    simpa [coeff_C_mul, coeff_X_pow, hk] using this
  have hV : V = C (V.coeff m) * X ^ m := by
    ext k
    by_cases hk : k = m
    · subst hk; simp
    · rw [h4 k hk]; simp [coeff_X_pow, hk]
  have hv2 : algebraMap K[X] (RatFunc K) V
      = (RatFunc.X : RatFunc K) ^ m * algebraMap K (RatFunc K) (V.coeff m) := by
    have : algebraMap K[X] (RatFunc K) (C (V.coeff m) * X ^ m)
        = (RatFunc.X : RatFunc K) ^ m * algebraMap K (RatFunc K) (V.coeff m) := by
      simp; ring
    rw [← this, ← hV]
  exact mul_left_cancel₀ hXm (hv.trans hv2)

private lemma denom_aux {K : Type*} [Field K] (B : K[X]) (hB : B ≠ 0)
    (hdiv : ∀ p : K[X], Monic p → Irreducible p → p ∣ B → p = X) :
    ∃ (m : ℕ) (b0 : K), b0 ≠ 0 ∧ B = X ^ m * C b0 := by
  have hfin : FiniteMultiplicity (X : K[X]) B :=
    finiteMultiplicity_of_degree_pos_of_monic (by simp) monic_X hB
  obtain ⟨B', hB', hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hunit : IsUnit B' := by
    by_contra hnu
    obtain ⟨g, hgm, hgi, hgd⟩ := exists_monic_irreducible_factor B' hnu
    have : g = X := hdiv g hgm hgi (hB' ▸ Dvd.dvd.mul_left hgd _)
    exact hnd (this ▸ hgd)
  obtain ⟨b0, hb0, hCb⟩ := Polynomial.isUnit_iff.1 hunit
  exact ⟨_, b0, hb0.ne_zero, by rw [hB', ← hCb]⟩

theorem solution {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′) * RatFunc.X)
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0) (h : K)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) (v : RatFunc K)
    (hfe : algebraMap K (RatFunc K) h = ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) + v′) :
    ∃ (m : ℕ) (c' a : Fin m → K) (b : K), (∀ i, (c' i)′ = 0) ∧ (∀ i, a i ≠ 0) ∧
      h = ∑ i, c' i * ((a i)′ / a i) + b′ := by
  classical
  have hw : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) (C (s′) * X) := by
    simp [hX]
  have hpoly : ∀ r : K[X], ∃ q : K[X],
      (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q :=
    fun r => ⟨_, LiouvilleDiffAlg.ratFunc_deriv_poly _ hw r⟩
  obtain ⟨a, E, Cc, A, B, ha, hE, hC, hB, hv, hBdiv, hfe'⟩ :=
    LiouvilleDiffAlg.ratFunc_liouville_key hpoly (fun p => p = X)
      (fun p q hm hi hne hq => hExc_aux hX hcon p q hm hi hne hq) c hc h u hu v hfe
  set γ : K := ∑ p ∈ E, Cc p with hγdef
  have hγ : γ′ = 0 := by
    rw [hγdef, map_sum]; exact Finset.sum_eq_zero (fun p _ => hC p)
  have hEsum : ∑ p ∈ E, algebraMap K (RatFunc K) (Cc p) *
        ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p)
      = algebraMap K (RatFunc K) (γ * s′) := by
    rw [hγdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(hE p hp).2.2]
    rw [RatFunc.algebraMap_X, hX, mul_div_cancel_right₀ _ RatFunc.X_ne_zero, map_mul]
  obtain ⟨m, b0, hb0, hBeq⟩ := denom_aux B hB (fun p hm hi hd => hBdiv p hm hi hd)
  set V : K[X] := C b0⁻¹ * A with hVdef
  have hv2 : (RatFunc.X : RatFunc K) ^ m * v = algebraMap K[X] (RatFunc K) V := by
    have hb0' : algebraMap K (RatFunc K) b0 ≠ 0 := by
      simpa using hb0
    have hXm : (RatFunc.X : RatFunc K) ^ m ≠ 0 := pow_ne_zero m RatFunc.X_ne_zero
    rw [hv, hBeq, hVdef]
    have e1 : algebraMap K[X] (RatFunc K) (C b0) = algebraMap K (RatFunc K) b0 := by simp
    have e2 : algebraMap K[X] (RatFunc K) (C b0⁻¹) = (algebraMap K (RatFunc K) b0)⁻¹ := by simp
    rw [map_mul, map_mul, map_pow, e1, e2, RatFunc.algebraMap_X]
    field_simp
  have hvT : v′ = algebraMap K (RatFunc K)
      (h - ∑ i, c i * ((a i)′ / a i) - γ * s′) := by
    have e : algebraMap K (RatFunc K) (∑ i, c i * ((a i)′ / a i)) = ∑ i, algebraMap K (RatFunc K) (c i) *
        ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, map_div₀, DifferentialAlgebra.deriv_algebraMap]
    rw [map_sub, map_sub, e, ← hEsum]
    linear_combination (-1 : RatFunc K) * hfe'
  have hvk := poly_part_aux hX hcon m V _ v hvT hv2
  have hT : h - ∑ i, c i * ((a i)′ / a i) - γ * s′ = (V.coeff m)′ := by
    apply (algebraMap K (RatFunc K)).injective
    rw [← hvT, hvk, DifferentialAlgebra.deriv_algebraMap]
  refine ⟨n, c, a, γ * s + V.coeff m, hc, ha, ?_⟩
  have : (γ * s + V.coeff m)′ = γ * s′ + (V.coeff m)′ := by
    simp [Derivation.leibniz, hγ]
  rw [this]
  linear_combination hT

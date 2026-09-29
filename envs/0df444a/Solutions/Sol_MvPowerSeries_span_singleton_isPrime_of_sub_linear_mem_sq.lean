-- Prove2me | solution 1 for MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b8e0e235-5b24-524f-ace8-75f0781722c7

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_algEquiv_apply_X_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq

set_option autoImplicit false

universe u

open MvPowerSeries

namespace LinPrimeGC7

variable {κ : Type u} [Field κ]

def killX1 (p : MvPowerSeries (Fin 2) κ) : MvPowerSeries (Fin 2) κ :=
  fun m => if m 1 = 0 then coeff m p else 0

theorem coeff_killX1 (p : MvPowerSeries (Fin 2) κ) (m : Fin 2 →₀ ℕ) :
    coeff m (killX1 p) = if m 1 = 0 then coeff m p else 0 := rfl

theorem X1_dvd_sub_killX1 (p : MvPowerSeries (Fin 2) κ) : (X 1 : MvPowerSeries (Fin 2) κ) ∣ p - killX1 p := by
  rw [X_dvd_iff]
  intro m hm
  rw [map_sub, coeff_killX1, if_pos hm, sub_self]

theorem X1_dvd_iff_killX1_eq_zero (p : MvPowerSeries (Fin 2) κ) :
    (X 1 : MvPowerSeries (Fin 2) κ) ∣ p ↔ killX1 p = 0 := by
  rw [X_dvd_iff]
  constructor
  · intro h; ext m; rw [coeff_killX1]; split_ifs with hm
    · exact h m hm
    · rfl
  · intro h m hm
    have := congrArg (coeff m) h
    rwa [coeff_killX1, if_pos hm, map_zero] at this

theorem killX1_mul (p q : MvPowerSeries (Fin 2) κ) : killX1 (p * q) = killX1 p * killX1 q := by
  classical
  ext m
  rw [coeff_killX1, coeff_mul, coeff_mul]
  split_ifs with hm
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have h0 : ij.1 1 = 0 ∧ ij.2 1 = 0 := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hij
      simp only [Finsupp.add_apply] at this
      omega
    rw [coeff_killX1, coeff_killX1, if_pos h0.1, if_pos h0.2]
  · symm
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have h0 : ij.1 1 ≠ 0 ∨ ij.2 1 ≠ 0 := by
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hij
      simp only [Finsupp.add_apply] at this
      omega
    rcases h0 with h | h
    · rw [coeff_killX1, if_neg h, zero_mul]
    · rw [coeff_killX1 q, if_neg h, mul_zero]

theorem exists_eq_X0_pow_mul_unit {r : MvPowerSeries (Fin 2) κ} (hr : killX1 r = r) (hr0 : r ≠ 0) :
    ∃ (n : ℕ) (w : MvPowerSeries (Fin 2) κ), IsUnit w ∧ r = X 0 ^ n * w := by
  classical

  have hex : ∃ n : ℕ, coeff (Finsupp.single 0 n) r ≠ 0 := by
    by_contra h
    push Not at h
    apply hr0
    ext m
    rw [map_zero]
    by_cases hm : m 1 = 0
    · have : m = Finsupp.single 0 (m 0) := by
        ext i; fin_cases i <;> simp [hm]
      rw [this]; exact h _
    · rw [← hr, coeff_killX1, if_neg hm]
  let n := Nat.find hex
  have hn : coeff (Finsupp.single 0 n) r ≠ 0 := Nat.find_spec hex
  have hlt : ∀ k < n, coeff (Finsupp.single 0 k) r = 0 := fun k hk => by
    have := Nat.find_min hex hk; push Not at this; exact this
  have hdvd : (X 0 : MvPowerSeries (Fin 2) κ) ^ n ∣ r := by
    rw [X_pow_dvd_iff]
    intro m hm
    by_cases hm1 : m 1 = 0
    · have : m = Finsupp.single 0 (m 0) := by
        ext i; fin_cases i <;> simp [hm1]
      rw [this]; exact hlt _ (this ▸ hm)
    · rw [← hr, coeff_killX1, if_neg hm1]
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨n, w, ?_, hw⟩
  rw [isUnit_iff_constantCoeff]
  have : coeff (Finsupp.single 0 n) r = constantCoeff w := by
    rw [hw, X_pow_eq, coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self, coeff_zero_eq_constantCoeff_apply]
  rw [← this]
  exact isUnit_iff_ne_zero.mpr hn

theorem killX1_killX1 (p : MvPowerSeries (Fin 2) κ) : killX1 (killX1 p) = killX1 p := by
  ext m; rw [coeff_killX1, coeff_killX1]; split_ifs <;> rfl

theorem X0_not_dvd_by_X1 : ¬ ((X 1 : MvPowerSeries (Fin 2) κ) ∣ X 0) := by
  classical
  rw [X_dvd_iff]
  intro h
  have := h (Finsupp.single 0 1) (by simp)
  rw [coeff_index_single_X] at this
  simp at this

theorem span_X1_isPrime : (Ideal.span {(X 1 : MvPowerSeries (Fin 2) κ)}).IsPrime := by
  have hX : (X 1 : MvPowerSeries (Fin 2) κ) ≠ 0 := by
    intro h
    have := congrArg (coeff (Finsupp.single (1 : Fin 2) 1)) h
    rw [coeff_index_single_self_X, map_zero] at this
    exact one_ne_zero this
  refine (Ideal.span_singleton_prime hX).mpr ⟨hX, ?_, ?_⟩
  · rw [isUnit_iff_constantCoeff, constantCoeff_X]; exact not_isUnit_zero
  · intro p q h
    rw [X1_dvd_iff_killX1_eq_zero, killX1_mul, mul_eq_zero] at h
    rcases h with h | h
    · left; rwa [X1_dvd_iff_killX1_eq_zero]
    · right; rwa [X1_dvd_iff_killX1_eq_zero]

theorem eq_span_X1 (P : Ideal (MvPowerSeries (Fin 2) κ)) [hP : P.IsPrime]
    (h1 : (X 1 : MvPowerSeries (Fin 2) κ) ∈ P) (h0 : (X 0 : MvPowerSeries (Fin 2) κ) ∉ P) :
    P = Ideal.span {X 1} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr h1)
  intro p hp
  have hk : killX1 p ∈ P := by
    obtain ⟨t, ht⟩ := X1_dvd_sub_killX1 p
    have : p - killX1 p ∈ P := by rw [ht]; exact P.mul_mem_right _ h1
    simpa using P.sub_mem hp this
  by_cases hk0 : killX1 p = 0
  · exact Ideal.mem_span_singleton.mpr ((X1_dvd_iff_killX1_eq_zero p).mpr hk0)
  · exfalso
    obtain ⟨n, w, hw, hnw⟩ := exists_eq_X0_pow_mul_unit (killX1_killX1 p) hk0
    rw [hnw] at hk
    have : (X 0 : MvPowerSeries (Fin 2) κ) ^ n ∈ P := by
      have := P.mul_mem_right (↑hw.unit⁻¹ : MvPowerSeries (Fin 2) κ) hk
      rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
    exact h0 (hP.mem_of_pow_mem n this)

theorem mem_span_X_of_constantCoeff_eq_zero (p : MvPowerSeries (Fin 2) κ) (hp : constantCoeff p = 0) :
    p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
  have h1 : p - killX1 p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
    obtain ⟨t, ht⟩ := X1_dvd_sub_killX1 p
    rw [ht]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have h2 : killX1 p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
    have : (X 0 : MvPowerSeries (Fin 2) κ) ∣ killX1 p := by
      rw [X_dvd_iff]
      intro m hm0
      rw [coeff_killX1]
      split_ifs with hm1
      · have : m = 0 := by ext i; fin_cases i <;> simp [hm0, hm1]
        rw [this, coeff_zero_eq_constantCoeff_apply, hp]
      · rfl
    obtain ⟨t, ht⟩ := this
    rw [ht]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  simpa using Ideal.add_mem _ h1 h2

theorem coeff_eq_zero_of_mem_sq (p : MvPowerSeries (Fin 2) κ)
    (hp : p ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2)
    (d : Fin 2 →₀ ℕ) (hd : d.degree < 2) : coeff d p = 0 := by
  classical
  have hgen : ∀ r ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}, constantCoeff r = 0 := by
    intro r hr
    have : Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ≤ RingHom.ker constantCoeff := by
      rw [Ideal.span_le]
      rintro x hx
      rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, constantCoeff_X]
    exact this hr
  rw [pow_two] at hp
  revert d hd
  refine Submodule.mul_induction_on hp ?_ ?_
  · intro m hm n hn d hd
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hdeg : ij.1.degree + ij.2.degree < 2 := by rw [← map_add, hij]; exact hd
    rcases Nat.eq_zero_or_pos ij.1.degree with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      rw [h, coeff_zero_eq_constantCoeff_apply, hgen m hm, zero_mul]
    · have h2 : ij.2.degree = 0 := by omega
      rw [Finsupp.degree_eq_zero_iff] at h2
      rw [h2, coeff_zero_eq_constantCoeff_apply, hgen n hn, mul_zero]
  · intro x y hx hy d hd
    rw [map_add, hx d hd, hy d hd, add_zero]

theorem coeff_single_one_mul (p q : MvPowerSeries (Fin 2) κ) (hq : constantCoeff q = 0) (j : Fin 2) :
    coeff (Finsupp.single j 1) (p * q) = constantCoeff p * coeff (Finsupp.single j 1) q := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  have : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, hq, mul_zero, add_zero]

end LinPrimeGC7

open LinPrimeGC7 in
theorem solution
    {κ : Type u} [Field κ] (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (ℓ : MvPowerSeries (Fin 2) κ)
    (hℓ : ℓ - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) :
    (Ideal.span {ℓ}).IsPrime ∧
    ((X 0 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ} ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ}) ∧
    (∀ P : Ideal (MvPowerSeries (Fin 2) κ), P.IsPrime → ℓ ∈ P →
      ((X 0 : MvPowerSeries (Fin 2) κ) ∉ P ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ P) → P = Ideal.span {ℓ}) ∧
    (∀ (a' b' : κ) (h' : MvPowerSeries (Fin 2) κ),
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 →
      C a' * X 0 + C b' * X 1 + h' ∈ Ideal.span {ℓ} → a * b' - a' * b = 0) := by
  classical

  have hlin : ∀ (a' b' : κ) (h' : MvPowerSeries (Fin 2) κ),
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 →
      constantCoeff (C a' * X 0 + C b' * X 1 + h') = 0 ∧
      coeff (Finsupp.single 0 1) (C a' * X 0 + C b' * X 1 + h') = a' ∧
      coeff (Finsupp.single 1 1) (C a' * X 0 + C b' * X 1 + h') = b' := by
    intro a' b' h' hh'
    have h0 := coeff_eq_zero_of_mem_sq h' hh'
    refine ⟨?_, ?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, map_add, h0 0 (by simp)]
      simp [coeff_C_mul, coeff_zero_X]
    · rw [map_add, h0 _ (by simp)]
      simp [coeff_C_mul, coeff_index_single_X]
    · rw [map_add, h0 _ (by simp)]
      simp [coeff_C_mul, coeff_index_single_X]
  have hℓeq : ℓ = C a * X 0 + C b * X 1 + (ℓ - (C a * X 0 + C b * X 1)) := by ring
  obtain ⟨hℓ0, hℓa, hℓb⟩ : constantCoeff ℓ = 0 ∧ coeff (Finsupp.single 0 1) ℓ = a ∧
      coeff (Finsupp.single 1 1) ℓ = b := by
    have := hlin a b _ hℓ
    rwa [← hℓeq] at this

  obtain ⟨e, he1⟩ : ∃ e : MvPowerSeries (Fin 2) κ ≃ₐ[κ] MvPowerSeries (Fin 2) κ, e (X 1) = ℓ := by
    by_cases hb : b = 0
    · have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
      obtain ⟨e, he⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq ![X 1, ℓ]
        (by intro i; fin_cases i <;> simp [constantCoeff_X, hℓ0])
        (by
          rw [Matrix.det_fin_two]
          simp [Matrix.of_apply, coeff_index_single_X, hℓa, hℓb, ha])
      exact ⟨e, he 1⟩
    · obtain ⟨e, he⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq ![X 0, ℓ]
        (by intro i; fin_cases i <;> simp [constantCoeff_X, hℓ0])
        (by
          rw [Matrix.det_fin_two]
          simp [Matrix.of_apply, coeff_index_single_X, hℓa, hℓb, hb])
      exact ⟨e, he 1⟩
  have hmap : Ideal.map e (Ideal.span {(X 1 : MvPowerSeries (Fin 2) κ)}) = Ideal.span {ℓ} := by
    rw [Ideal.map_span, Set.image_singleton, he1]

  have hnonunit : ∀ p : MvPowerSeries (Fin 2) κ, constantCoeff p = 0 → constantCoeff (e p) = 0 := by
    intro p hp
    by_contra h
    have hu : IsUnit (e p) := isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
    have : IsUnit p := by simpa using hu.map e.symm
    rw [isUnit_iff_constantCoeff, hp] at this
    exact not_isUnit_zero this

  have key : ∀ I : Ideal (MvPowerSeries (Fin 2) κ),
      (X 0 : MvPowerSeries (Fin 2) κ) ∈ I.map e → (X 1 : MvPowerSeries (Fin 2) κ) ∈ I.map e →
      ∀ p : MvPowerSeries (Fin 2) κ, constantCoeff p = 0 → p ∈ I := by
    intro I h0 h1 p hp
    have hsub : Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ≤ I.map e := by
      rw [Ideal.span_le]; rintro x hx; rcases hx with rfl | rfl <;> assumption
    have : e p ∈ I.map e := hsub (mem_span_X_of_constantCoeff_eq_zero _ (hnonunit p hp))
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_of_equiv e (e p)).mp this
    rwa [← e.injective hxe]
  haveI := (span_X1_isPrime (κ := κ))
  refine ⟨?_, ?_, ?_, ?_⟩

  · rw [← hmap]; exact Ideal.map_isPrime_of_equiv e

  · by_contra h
    push Not at h
    obtain ⟨h0, h1⟩ := h
    rw [← hmap] at h0 h1
    have := key _ h0 h1 (X 0) (constantCoeff_X 0)
    exact X0_not_dvd_by_X1 (Ideal.mem_span_singleton.mp this)

  · intro P hP hℓP hnm
    have hPeq : (P.comap e).map e = P := Ideal.map_comap_of_surjective _ e.surjective _
    haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    have h1 : (X 1 : MvPowerSeries (Fin 2) κ) ∈ P.comap e := by
      rw [Ideal.mem_comap]; simpa [he1] using hℓP
    have h0 : (X 0 : MvPowerSeries (Fin 2) κ) ∉ P.comap e := by
      intro h0
      have hall : ∀ p : MvPowerSeries (Fin 2) κ, constantCoeff p = 0 → p ∈ P.comap e := by
        intro p hp
        have hsub : Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ≤ P.comap e := by
          rw [Ideal.span_le]; rintro x hx; rcases hx with rfl | rfl <;> assumption
        exact hsub (mem_span_X_of_constantCoeff_eq_zero p hp)
      have hX : ∀ k : Fin 2, (X k : MvPowerSeries (Fin 2) κ) ∈ P := by
        intro k
        have hk : constantCoeff (e.symm (X k)) = 0 := by
          have := hnonunit (e.symm (X k))
          by_contra hne
          have hu : IsUnit (e.symm (X k)) := isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hne)
          have : IsUnit (X k : MvPowerSeries (Fin 2) κ) := by simpa using hu.map e
          rw [isUnit_iff_constantCoeff, constantCoeff_X] at this
          exact not_isUnit_zero this
        have := hall _ hk
        rw [Ideal.mem_comap] at this
        simpa using this
      rcases hnm with h | h
      · exact h (hX 0)
      · exact h (hX 1)
    rw [← hPeq, eq_span_X1 (P.comap e) h1 h0, hmap]

  · intro a' b' h' hh' hmem
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨-, ha', hb'⟩ := hlin a' b' h' hh'
    rw [← hm, coeff_single_one_mul m ℓ hℓ0, hℓa] at ha'
    rw [← hm, coeff_single_one_mul m ℓ hℓ0, hℓb] at hb'
    rw [← ha', ← hb']; ring

end S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq
end P2MW
export P2MW.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq (solution)

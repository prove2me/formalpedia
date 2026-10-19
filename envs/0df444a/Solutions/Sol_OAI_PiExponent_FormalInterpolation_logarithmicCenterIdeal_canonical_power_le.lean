-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_canonical_power_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:56:29.831969+00:00
-- url     : https://prove2.me/submissions/c7f7c315-d495-4a3c-ad22-538206ab1a36

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation
noncomputable def h41_mono {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (a : ℕ) (b : Fin m → ℕ) : MvPolynomial (Fin (m + 1)) Complex :=
  (MvPolynomial.X 0 - 1) ^ a * ∏ i, (logarithmicCoordinate c T i.succ) ^ (b i)

noncomputable def h41_F {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (t : ℝ) : Ideal (MvPolynomial (Fin (m + 1)) Complex) :=
  Ideal.span {x | ∃ (a : ℕ) (b : Fin m → ℕ), t ≤ (a : ℝ) / e 0 + ∑ i, (b i : ℝ) / e i.succ ∧ x = h41_mono c T a b}

theorem h41_F_mono_mem {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (t : ℝ) (a : ℕ) (b : Fin m → ℕ)
    (h : t ≤ (a : ℝ) / e 0 + ∑ i, (b i : ℝ) / e i.succ) : h41_mono c T a b ∈ h41_F c T e t :=
  Ideal.subset_span ⟨a, b, h, rfl⟩

theorem h41_F_mul {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (s t : ℝ) :
    h41_F c T e s * h41_F c T e t ≤ h41_F c T e (s + t) := by
  unfold h41_F
  rw [Ideal.span_mul_span']
  apply Ideal.span_mono
  rintro x ⟨y, ⟨a, b, hab, rfl⟩, z, ⟨a', b', hab', rfl⟩, rfl⟩
  refine ⟨a + a', b + b', ?_, ?_⟩
  · have : ((a + a' : ℕ) : ℝ) / e 0 + ∑ i, (((b + b') i : ℕ) : ℝ) / e i.succ =
        ((a : ℝ) / e 0 + ∑ i, (b i : ℝ) / e i.succ) +
        ((a' : ℝ) / e 0 + ∑ i, (b' i : ℝ) / e i.succ) := by
      simp only [Pi.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]
      ring
    rw [this]; linarith
  · simp only [h41_mono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem h41_F_anti {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (s t : ℝ) (hst : s ≤ t) :
    h41_F c T e t ≤ h41_F c T e s := by
  unfold h41_F
  apply Ideal.span_mono
  rintro x ⟨a, b, hab, rfl⟩
  exact ⟨a, b, hst.trans hab, rfl⟩

theorem h41_F_zero {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) : h41_F c T e 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have : h41_mono c T 0 0 = 1 := by simp [h41_mono]
  rw [← this]
  apply h41_F_mono_mem
  simp

theorem h41_F_pow {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hJ : J ≤ h41_F c T e 1) (k : ℕ) : J ^ k ≤ h41_F c T e k := by
  induction k with
  | zero => simp [h41_F_zero]
  | succ k ih =>
    rw [pow_succ]
    calc J ^ k * J ≤ h41_F c T e k * h41_F c T e 1 := Ideal.mul_mono ih hJ
      _ ≤ h41_F c T e (k + 1) := h41_F_mul c T e _ _
      _ = _ := by push_cast; rfl

theorem h41_F_le_pow {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i) (n : ℕ) :
    h41_F c T e ((n + m : ℕ) : ℝ) ≤ (logarithmicCenterIdeal c T e) ^ n := by
  classical
  unfold h41_F
  rw [Ideal.span_le]
  rintro x ⟨a, b, hab, rfl⟩
  set J := logarithmicCenterIdeal c T e
  have hu : (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) Complex) ^ e 0 ∈ J := by
    have : logarithmicCoordinate c T 0 = MvPolynomial.X 0 - 1 := rfl
    rw [← this]
    exact Ideal.subset_span ⟨0, rfl⟩
  have hg : ∀ i : Fin m, logarithmicCoordinate c T i.succ ^ e i.succ ∈ J :=
    fun i => Ideal.subset_span ⟨i.succ, rfl⟩
  let p := a / e 0
  let q : Fin m → ℕ := fun i => b i / e i.succ
  have hmem : ((MvPolynomial.X 0 - 1) ^ e 0) ^ p *
      ∏ i, (logarithmicCoordinate c T i.succ ^ e i.succ) ^ q i ∈ J ^ (p + ∑ i, q i) := by
    rw [pow_add]
    apply Ideal.mul_mem_mul (Ideal.pow_mem_pow hu p)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (hg i) _)
  have hcount : n ≤ p + ∑ i, q i := by
    have h1 : (a : ℝ) / e 0 < p + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast he 0)]
      have : (a : ℝ) < (e 0 : ℝ) * (p + 1) := by exact_mod_cast Nat.lt_mul_div_succ a (he 0)
      linarith
    have h2 : ∀ i, (b i : ℝ) / e i.succ < q i + 1 := by
      intro i
      rw [div_lt_iff₀ (by exact_mod_cast he i.succ)]
      have : (b i : ℝ) < (e i.succ : ℝ) * (q i + 1) := by exact_mod_cast Nat.lt_mul_div_succ (b i) (he i.succ)
      linarith
    have h3 : ∑ i, (b i : ℝ) / e i.succ < ∑ i, ((q i : ℝ) + 1) ∨ m = 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · right; exact h
      · left
        have : Nonempty (Fin m) := ⟨⟨0, h⟩⟩
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h2 i)
    have h4 : (n : ℝ) < p + ∑ i, (q i : ℝ) + 1 := by
      rw [Finset.sum_add_distrib] at h3
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h3
      push_cast at hab
      rcases h3 with h3 | h3
      · linarith
      · subst h3; simp at hab ⊢; linarith
    have : (n : ℝ) < ((p + ∑ i, q i : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have heq : h41_mono c T a b = ((MvPolynomial.X 0 - 1) ^ (a % e 0) *
      ∏ i, logarithmicCoordinate c T i.succ ^ (b i % e i.succ)) *
      (((MvPolynomial.X 0 - 1) ^ e 0) ^ p *
      ∏ i, (logarithmicCoordinate c T i.succ ^ e i.succ) ^ q i) := by
    simp only [h41_mono]
    have hA : (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) Complex) ^ a =
        (MvPolynomial.X 0 - 1) ^ (a % e 0) * ((MvPolynomial.X 0 - 1) ^ e 0) ^ p := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have hB : ∀ i, logarithmicCoordinate c T i.succ ^ b i =
        logarithmicCoordinate c T i.succ ^ (b i % e i.succ) *
          (logarithmicCoordinate c T i.succ ^ e i.succ) ^ q i := by
      intro i
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hA, Finset.prod_congr rfl (fun i _ => hB i), Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hcount hmem)

theorem h41_trunc_dvd (T S : ℕ) :
    (Polynomial.X : Polynomial ℂ) ^ (min T S) ∣
      OAI.PiExponent.InterpolationMatrix.truncatedLog T - OAI.PiExponent.InterpolationMatrix.truncatedLog S := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  simp only [OAI.PiExponent.InterpolationMatrix.truncatedLog, Polynomial.coeff_sub, PowerSeries.coeff_trunc]
  have h1 : d < T := lt_of_lt_of_le hd (min_le_left _ _)
  have h2 : d < S := lt_of_lt_of_le hd (min_le_right _ _)
  simp [h1, h2]

theorem h41_mono_single {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat) (a : ℕ) (i : Fin m) (k : ℕ) :
    h41_mono c T a (Pi.single i k) = (MvPolynomial.X 0 - 1) ^ a * logarithmicCoordinate c T i.succ ^ k := by
  classical
  simp only [h41_mono]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji; simp [Pi.single_eq_of_ne hji]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem h41_gen_le {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (hcut : ∀ i, e 0 ≤ T i * e i.succ) :
    logarithmicCenterIdeal c (fun _ => e 0) e ≤ h41_F c T e 1 := by
  classical
  unfold logarithmicCenterIdeal
  rw [Ideal.span_le]
  rintro x ⟨i, rfl⟩
  cases i using Fin.cases with
  | zero =>
    have : logarithmicCoordinate c (fun _ => e 0) 0 ^ e 0 = h41_mono c T (e 0) 0 := by
      simp [h41_mono, logarithmicCoordinate]
    show logarithmicCoordinate c (fun _ => e 0) 0 ^ e 0 ∈ _
    rw [this]
    apply h41_F_mono_mem
    have : ((e 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (he 0).ne'
    simp [this]
  | succ i =>
    obtain ⟨t, ht⟩ : ∃ t, t = min (T i) (e 0) := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ := h41_trunc_dvd (T i) (e 0)
    rw [← ht] at hh
    set u : MvPolynomial (Fin (m + 1)) Complex := MvPolynomial.X 0 - 1
    have hg : logarithmicCoordinate c (fun _ => e 0) i.succ =
        logarithmicCoordinate c T i.succ + u ^ t * Polynomial.aeval u h := by
      have : Polynomial.aeval u (OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) -
          Polynomial.aeval u (OAI.PiExponent.InterpolationMatrix.truncatedLog (e 0)) =
          u ^ t * Polynomial.aeval u h := by
        rw [← map_sub, hh]; simp
      simp only [logarithmicCoordinate, Fin.cases_succ]
      rw [← this]
      ring
    show logarithmicCoordinate c (fun _ => e 0) i.succ ^ e i.succ ∈ _
    rw [hg, add_pow]
    apply Ideal.sum_mem
    intro k hk
    have hk' : k ≤ e i.succ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have heq : logarithmicCoordinate c T i.succ ^ k * (u ^ t * Polynomial.aeval u h) ^ (e i.succ - k) *
        ((e i.succ).choose k : MvPolynomial (Fin (m + 1)) Complex) =
        (Polynomial.aeval u h ^ (e i.succ - k) * ((e i.succ).choose k : MvPolynomial (Fin (m + 1)) Complex)) *
          h41_mono c T (t * (e i.succ - k)) (Pi.single i k) := by
      rw [h41_mono_single, pow_mul]
      ring
    rw [heq]
    apply Ideal.mul_mem_left
    apply h41_F_mono_mem
    have hsum : ∑ j, ((Pi.single i k : Fin m → ℕ) j : ℝ) / e j.succ = (k : ℝ) / e i.succ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Pi.single_eq_of_ne hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsum]
    have hte : e 0 ≤ t * e i.succ := by
      rcases le_total (T i) (e 0) with h1 | h1
      · rw [ht, min_eq_left h1]; exact hcut i
      · rw [ht, min_eq_right h1]; exact Nat.le_mul_of_pos_right _ (he i.succ)
    have hte' : (e 0 : ℝ) ≤ (t : ℝ) * e i.succ := by exact_mod_cast hte
    have he0 : (0 : ℝ) < e 0 := by exact_mod_cast he 0
    have hei : (0 : ℝ) < e i.succ := by exact_mod_cast he i.succ
    have hkR : (k : ℝ) ≤ e i.succ := by exact_mod_cast hk'
    rw [Nat.cast_mul, Nat.cast_sub hk', div_add_div _ _ he0.ne' hei.ne', le_div_iff₀ (by positivity)]
    nlinarith

theorem solution
    {m : Nat} (c : Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (he : ∀ i, 0 < e i)
    (hcut : ∀ i, e 0 ≤ T i * e i.succ) (n : Nat) :
    (logarithmicCenterIdeal c (fun _ => e 0) e) ^ (n + m) ≤
      (logarithmicCenterIdeal c T e) ^ n := by
  have h1 := h41_F_pow c T e _ (h41_gen_le c T e he hcut) (n + m)
  exact h1.trans (h41_F_le_pow c T e he n)


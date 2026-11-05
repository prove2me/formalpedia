-- Prove2me | solution 1 for LL_Decomp1535a.ternaryAbove_of_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:04.976501+00:00
-- url     : https://prove2.me/submissions/d43cb6bf-51b8-4e23-9cbf-4b47cc35665f

import Mathlib
import Definitions.Def_LL_Decomp1535a_IsTernarySum
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F
import Definitions.Def_LL_Decomp1535a_TernaryAbove

open MeasureTheory

noncomputable def GbAAux.thetaA (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

noncomputable def GbAAux.R3A (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else 0

theorem GbAAux.orth_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk']
    have e : ∀ α : ℝ, Complex.exp (2 * Real.pi * Complex.I * α * k) =
        Complex.exp ((2 * Real.pi * Complex.I * k) * α) := fun α => by ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * k) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I * k) * ((1 : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I)
        by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]
    simp

theorem GbAAux.theta_le (N : ℕ) : GbAAux.thetaA N ≤ Real.log 4 * N := by
  have h1 : GbAAux.thetaA N = Real.log (primorial N) := by
    unfold GbAAux.thetaA primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [h1]
  calc Real.log (primorial N) ≤ Real.log ((4 : ℕ) ^ N : ℕ) := by
        apply Real.log_le_log
        · exact_mod_cast (primorial_pos N)
        · exact_mod_cast primorial_le_4_pow N
    _ = Real.log 4 * N := by
        rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

theorem GbAAux.sum_log_sq_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * GbAAux.thetaA N := by
  unfold GbAAux.thetaA
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.1 hp
  have hpN : p ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp'.1)
  have h0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h2 : Real.log p ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hpN)
  nlinarith

theorem GbAAux.continuous_S (N : ℕ) : Continuous (LL_Decomp1535a.S N) := by
  unfold LL_Decomp1535a.S
  apply continuous_finset_sum
  intro p _
  fun_prop

theorem GbAAux.continuous_F (N : ℕ) : Continuous (LL_Decomp1535a.F N) := by
  unfold LL_Decomp1535a.F
  have := GbAAux.continuous_S N
  fun_prop

theorem GbAAux.norm_F (N : ℕ) (α : ℝ) :
    ‖LL_Decomp1535a.F N α‖ = ‖LL_Decomp1535a.S N α‖ ^ 3 := by
  unfold LL_Decomp1535a.F
  rw [norm_mul, norm_pow, Complex.norm_exp]
  simp

theorem GbAAux.split_arcs (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in Set.Ioc (0 : ℝ) 1, LL_Decomp1535a.F N α =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α) +
        ∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α := by
  have hint : IntegrableOn (LL_Decomp1535a.F N) (Set.Ioc (0 : ℝ) 1) :=
    (GbAAux.continuous_F N).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  exact (integral_inter_add_sdiff hM hint).symm

theorem GbAAux.minor_bound (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖LL_Decomp1535a.S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α‖ ≤
      B * ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 := by
  have hcont : Continuous fun α => B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
    have := GbAAux.continuous_S N
    fun_prop
  have hgint : IntegrableOn (fun α => B * ‖LL_Decomp1535a.S N α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) 1 \ M) := measurableSet_Ioc.diff hM
  calc ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α‖
      ≤ ∫ α in Set.Ioc (0 : ℝ) 1 \ M, B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        refine norm_integral_le_of_norm_le (hgint.mono_set Set.diff_subset) ?_
        filter_upwards [ae_restrict_mem hmeas] with α hα
        rw [GbAAux.norm_F, pow_succ, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB α hα) (by positivity)
    _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1, B * ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        refine setIntegral_mono_set hgint ?_ (Filter.Eventually.of_forall Set.diff_subset)
        exact Filter.Eventually.of_forall fun α => by positivity
    _ = B * ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul]

theorem GbAAux.int_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) :
    ∫ α in (0 : ℝ)..1, ∑ i ∈ s, f i α = ∑ i ∈ s, ∫ α in (0 : ℝ)..1, f i α :=
  intervalIntegral.integral_finsetSum fun i _ => (hf i).intervalIntegrable _ _

theorem GbAAux.exp_mul_conj (α : ℝ) (p q : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * α * p) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * α * q)) =
    Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) - q : ℤ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem GbAAux.parseval_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖LL_Decomp1535a.S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have key : ∀ α : ℝ, (((‖LL_Decomp1535a.S N α‖ ^ 2 : ℝ)) : ℂ) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) - q : ℤ) : ℂ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold LL_Decomp1535a.S
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← GbAAux.exp_mul_conj]
    ring
  simp_rw [key]
  rw [GbAAux.int_sum _ _ (fun p => by fun_prop), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [GbAAux.int_sum _ _ (fun q => by fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, horth]
  simp [sub_eq_zero, hp, sq]

theorem GbAAux.circle_identity_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (GbAAux.R3A N : ℂ) = ∫ α in (0 : ℝ)..1, LL_Decomp1535a.F N α := by
  have key : ∀ α : ℝ, LL_Decomp1535a.F N α =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) := by
    intro α
    unfold LL_Decomp1535a.F LL_Decomp1535a.S
    simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    have e : Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * α * p) * Complex.exp (2 * Real.pi * Complex.I * α * q) *
          Complex.exp (2 * Real.pi * Complex.I * α * r) *
          Complex.exp (-(2 * Real.pi * Complex.I * α * N)) := by
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  simp_rw [key]
  rw [GbAAux.int_sum _ _ (fun p => by fun_prop)]
  have step : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      ∫ α in (0 : ℝ)..1, ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * α * (((p : ℤ) + q + r - N : ℤ) : ℂ)) =
      ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ r ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((Real.log p : ℂ) * (Real.log q : ℂ) * (Real.log r : ℂ)) *
          (if ((p : ℤ) + q + r - N) = 0 then 1 else 0) := by
    intro p _
    rw [GbAAux.int_sum _ _ (fun q => by fun_prop)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [GbAAux.int_sum _ _ (fun r => by fun_prop)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [intervalIntegral.integral_const_mul, horth]
  rw [Finset.sum_congr rfl step]
  unfold GbAAux.R3A
  simp only [Finset.sum_filter, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · simp only [hp, if_true]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.Prime
    · simp only [hq, if_true]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r.Prime
      · have : ((p : ℤ) + q + r - N = 0) ↔ p + q + r = N := by omega
        simp only [hr, true_and, if_true, this]
        split_ifs <;> simp
      · simp [hr]
    · simp [hq]
  · simp [hp]

theorem GbAAux.ex_pos {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hc
  exact absurd h (not_lt.2 (Finset.sum_nonpos fun i hi => not_lt.1 fun h' => hc ⟨i, hi, h'⟩))

theorem GbAAux.ternary_of_R3 (N : ℕ) (h : 0 < GbAAux.R3A N) : LL_Decomp1535a.IsTernarySum N := by
  unfold GbAAux.R3A at h
  obtain ⟨p, _, hp⟩ := GbAAux.ex_pos h
  obtain ⟨q, _, hq⟩ := GbAAux.ex_pos hp
  obtain ⟨r, _, hr⟩ := GbAAux.ex_pos hq
  by_cases hc : p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N
  · exact ⟨p, q, r, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · rw [if_neg hc] at hr
    exact absurd hr (lt_irrefl _)

theorem GbAAux.ternaryAbove_of_arcs {C : ℝ}
    (h : ∀ N : ℕ, Odd N → C ≤ N → ∃ M : Set ℝ, MeasurableSet M ∧ ∃ A B : ℝ, 0 ≤ B ∧
      A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α).re ∧
      (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖LL_Decomp1535a.S N α‖ ≤ B) ∧
      B * (Real.log N * (Real.log 4 * N)) < A) :
    LL_Decomp1535a.TernaryAbove C := by
  intro N hN hCN
  obtain ⟨M, hM, A, B, hB0, hA, hBS, hAB⟩ := h N hN hCN
  apply GbAAux.ternary_of_R3
  have hR := GbAAux.circle_identity_of_orth GbAAux.orth_int N
  rw [intervalIntegral.integral_of_le zero_le_one, GbAAux.split_arcs N hM] at hR
  have h1 : GbAAux.R3A N = (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α).re +
      (∫ α in Set.Ioc (0 : ℝ) 1 \ M, LL_Decomp1535a.F N α).re := by
    have := congrArg Complex.re hR
    simpa using this
  have h2 := (abs_le.1 (Complex.abs_re_le_norm (∫ α in Set.Ioc (0 : ℝ) 1 \ M,
    LL_Decomp1535a.F N α))).1
  have h3 := GbAAux.minor_bound N hM hB0 hBS
  rw [GbAAux.parseval_of_orth GbAAux.orth_int N] at h3
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h4 := GbAAux.sum_log_sq_le N
  have h5 := GbAAux.theta_le N
  have h6 : B * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      B * (Real.log N * (Real.log 4 * N)) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    exact h4.trans (mul_le_mul_of_nonneg_left h5 hlog)
  linarith

theorem solution {C : ℝ}
    (h : ∀ N : ℕ, Odd N → C ≤ N → ∃ M : Set ℝ, MeasurableSet M ∧ ∃ A B : ℝ, 0 ≤ B ∧
      A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, LL_Decomp1535a.F N α).re ∧
      (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖LL_Decomp1535a.S N α‖ ≤ B) ∧
      B * (Real.log N * (Real.log 4 * N)) < A) :
    LL_Decomp1535a.TernaryAbove C :=
  GbAAux.ternaryAbove_of_arcs h

-- Prove2me | solution 1 for LL_IwaniecLemma9.iwaniec_lemma9_numeric1122
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T04:00:13.913546+00:00
-- url     : https://prove2.me/submissions/7de70e93-1f9f-4a59-b68e-e3c440b651c4

import Mathlib

open Finset Real

namespace LL_IwaniecLemma9Aux

/-- `log t ≤ t / e` for `t > 0`, in the weaker form `2 * log t ≤ t`. -/
lemma two_log_le (t : ℝ) (ht : 0 < t) : 2 * Real.log t ≤ t := by
  have h1 := Real.add_one_le_exp (Real.log t - 1)
  rw [Real.exp_sub, Real.exp_log ht] at h1
  have he : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : (Real.log t) * Real.exp 1 ≤ t := by
    have := (le_div_iff₀ he0).mp (by linarith : Real.log t - 1 + 1 ≤ t / Real.exp 1)
    linarith
  rcases le_or_gt (Real.log t) 0 with h | h
  · linarith
  · nlinarith

end LL_IwaniecLemma9Aux

open LL_IwaniecLemma9Aux

set_option maxHeartbeats 1000000 in
theorem solution (q : ℕ) (hq : 3 ≤ q) (γ l η M : ℝ)
    (hl : l = Real.log ((q : ℝ) * (|γ| + 3)))
    (hη : η = (Real.sqrt l * Real.log (2 * l) ^ (3 / 4 : ℝ))⁻¹)
    (hM : M = (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ η * Real.exp (l ^ (1 / 4 : ℝ))) ^ 100) :
    η⁻¹ * (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (η - 1))) *
      (((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (100 * η) + Real.exp (60 * l ^ (1 / 4 : ℝ))) ≤
      M := by
  set S := q.primeFactors with hS
  set P : ℕ := ∏ p ∈ S, p with hP
  set L : ℝ := l ^ (1 / 4 : ℝ) with hL
  -- basic facts about q and l
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hg : (3 : ℝ) ≤ |γ| + 3 := by have := abs_nonneg γ; linarith
  have hlogq : Real.log q ≤ l := by
    rw [hl]
    apply Real.log_le_log hq0
    nlinarith
  have hl2 : 2 ≤ l := by
    rw [hl]
    have h9 : (9 : ℝ) ≤ (q : ℝ) * (|γ| + 3) := by nlinarith
    have he : Real.exp 2 ≤ 9 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [this]
      have h0 := Real.exp_pos 1
      nlinarith
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hl0 : 0 < l := by linarith
  -- L = l^{1/4}
  have hL1 : 1 ≤ L := Real.one_le_rpow (by linarith) (by norm_num)
  have hlogL : Real.log l ≤ 4 * (L - 1) := by
    have h1 : Real.log L = (1 / 4) * Real.log l := by
      rw [hL, Real.log_rpow hl0]
    have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
    linarith
  -- log (2l) facts
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog2pos : 0.69 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2l1 : 1 ≤ Real.log (2 * l) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlog2l_le : Real.log (2 * l) ≤ l := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos hl0
    linarith
  -- η facts
  set R : ℝ := Real.log (2 * l) ^ (3 / 4 : ℝ) with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hlog2l1 (by norm_num)
  have hRle : R ≤ Real.log (2 * l) := by
    have := Real.rpow_le_rpow_of_exponent_le hlog2l1 (by norm_num : (3 / 4 : ℝ) ≤ 1)
    simpa using this
  have hsqrt0 : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl0
  have hsqrt_le : Real.sqrt l ≤ l := by
    rw [Real.sqrt_le_iff]; constructor <;> nlinarith
  have hηinv : η⁻¹ = Real.sqrt l * R := by rw [hη, inv_inv]
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηinv_le : η⁻¹ ≤ l ^ 2 := by
    rw [hηinv]
    have : Real.sqrt l * R ≤ l * l := by
      apply mul_le_mul hsqrt_le (hRle.trans hlog2l_le) (by linarith) (by linarith)
    nlinarith
  -- η log l ≤ 1
  have hηlog : η * Real.log l ≤ 1 := by
    have hsq : Real.log l ≤ Real.sqrt l := by
      have h := two_log_le (Real.sqrt l) hsqrt0
      have : Real.log l = 2 * Real.log (Real.sqrt l) := by
        rw [Real.log_sqrt hl0.le]; ring
      linarith
    have hlogl0 : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
    have : η * Real.log l ≤ η * (Real.sqrt l * R) := by
      apply mul_le_mul_of_nonneg_left _ hη0.le
      nlinarith
    rw [← hηinv, mul_inv_cancel₀ hη0.ne'] at this
    exact this
  have hlη : l ^ η ≤ 3 := by
    rw [Real.rpow_def_of_pos hl0]
    have := Real.exp_one_lt_d9
    have h := Real.exp_le_exp.mpr (by linarith : Real.log l * η ≤ 1)
    linarith
  -- card S bound
  have hPdvd : P ∣ q := Nat.prod_primeFactors_dvd q
  have hPle : P ≤ q := Nat.le_of_dvd (by omega) hPdvd
  have hPpos : 1 ≤ P := by
    rw [hP]
    exact Finset.one_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hcard : (S.card : ℝ) ≤ 1.5 * l := by
    have h2 : 2 ^ S.card ≤ P := by
      rw [hP]
      exact Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2' : (2 : ℝ) ^ S.card ≤ q := by exact_mod_cast h2.trans hPle
    have h3 := Real.log_le_log (by positivity) h2'
    rw [Real.log_pow] at h3
    nlinarith
  -- the sum bound
  have hsum : ∑ p ∈ S, (p : ℝ) ^ (η - 1) ≤ 7.5 + 3 * Real.log l := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ l)]
    have hsmall : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1) ≤
        3 + 3 * Real.log l := by
      have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1) ≤
          ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ l), 3 * ((p : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).one_lt.le
        have hp0 : (0 : ℝ) < p := by linarith
        rw [Real.rpow_sub_one hp0.ne', div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Real.rpow_le_rpow hp0.le hp.2 hη0.le).trans hlη
      have h2 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ l), 3 * ((p : ℝ))⁻¹ ≤
          ∑ p ∈ Finset.Icc 1 ⌊l⌋₊, 3 * ((p : ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter] at hp
          rw [Finset.mem_Icc]
          exact ⟨(Nat.prime_of_mem_primeFactors hp.1).one_lt.le, Nat.le_floor hp.2⟩
        · intro i _ _; positivity
      have h3 : ∑ p ∈ Finset.Icc 1 ⌊l⌋₊, ((p : ℝ))⁻¹ ≤ 1 + Real.log l := by
        have hh := harmonic_le_one_add_log ⌊l⌋₊
        have hc : ((harmonic ⌊l⌋₊ : ℚ) : ℝ) = ∑ p ∈ Finset.Icc 1 ⌊l⌋₊, ((p : ℝ))⁻¹ := by
          rw [harmonic_eq_sum_Icc]; push_cast; rfl
        rw [hc] at hh
        have hf : (0 : ℝ) < (⌊l⌋₊ : ℝ) := by
          have : 1 ≤ ⌊l⌋₊ := Nat.le_floor (by norm_num; linarith)
          exact_mod_cast this
        have := Real.log_le_log hf (Nat.floor_le hl0.le)
        linarith
      rw [← Finset.mul_sum] at h1 h2
      rw [← Finset.mul_sum] at h2
      linarith
    have hlarge : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1) ≤ 4.5 := by
      have h1 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l), (p : ℝ) ^ (η - 1) ≤
          ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l), l ^ (η - 1) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        have hηle : η - 1 ≤ 0 := by
          have : η ≤ 1 := by
            have h := hηinv_le
            have : 1 ≤ η⁻¹ := by
              rw [hηinv]; nlinarith [Real.sqrt_le_sqrt (by linarith : (1:ℝ) ≤ l), Real.sqrt_one]
            rw [le_inv_comm₀ (by norm_num) hη0] at this
            simpa using this
          linarith
        exact Real.rpow_le_rpow_of_nonpos hl0 (le_of_lt (not_le.mp hp.2)) hηle
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have hcard' : ((S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l)).card : ℝ) ≤ 1.5 * l :=
        le_trans (by exact_mod_cast Finset.card_filter_le _ _) hcard
      rw [Real.rpow_sub_one hl0.ne'] at h1
      have hx : 0 ≤ l ^ η / l := by positivity
      have : ((S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ l)).card : ℝ) * (l ^ η / l) ≤
          1.5 * l * (l ^ η / l) := mul_le_mul_of_nonneg_right hcard' hx
      have h15 : 1.5 * l * (l ^ η / l) = 1.5 * l ^ η := by field_simp
      linarith
    linarith
  -- product bound
  have hprod : ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)) ≤ Real.exp (7.5 + 3 * Real.log l) := by
    calc ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)) ≤ ∏ p ∈ S, Real.exp ((p : ℝ) ^ (η - 1)) := by
          apply Finset.prod_le_prod
          · intro p _; positivity
          · intro p _
            have := Real.add_one_le_exp ((p : ℝ) ^ (η - 1)); linarith
      _ = Real.exp (∑ p ∈ S, (p : ℝ) ^ (η - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (7.5 + 3 * Real.log l) := Real.exp_le_exp.mpr hsum
  -- key: 2 η⁻¹ Π ≤ exp (40 L)
  have hkey : 2 * (η⁻¹ * ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1))) ≤ Real.exp (40 * L) := by
    have hl2e : l ^ 2 = Real.exp (2 * Real.log l) := by
      rw [show 2 * Real.log l = Real.log l + Real.log l by ring, Real.exp_add, Real.exp_log hl0]
      ring
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hprod0 : 0 ≤ ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)) := by
      apply Finset.prod_nonneg; intro p _; positivity
    calc 2 * (η⁻¹ * ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)))
        ≤ Real.exp 1 * (Real.exp (2 * Real.log l) * Real.exp (7.5 + 3 * Real.log l)) := by
          apply mul_le_mul h2e _ (by positivity) (by positivity)
          rw [← hl2e]
          exact mul_le_mul hηinv_le hprod hprod0 (by positivity)
      _ = Real.exp (1 + 2 * Real.log l + (7.5 + 3 * Real.log l)) := by
          simp only [Real.exp_add]; ring
      _ ≤ Real.exp (40 * L) := by
          apply Real.exp_le_exp.mpr
          linarith
  -- assemble
  have hA : (1 : ℝ) ≤ (P : ℝ) ^ (100 * η) :=
    Real.one_le_rpow (by exact_mod_cast hPpos) (by linarith)
  have hB : (1 : ℝ) ≤ Real.exp (60 * L) := Real.one_le_exp (by linarith)
  have hMeq : M = (P : ℝ) ^ (100 * η) * Real.exp (60 * L) * Real.exp (40 * L) := by
    rw [hM, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg P), ← Real.exp_nat_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [hMeq]
  have hAB : (P : ℝ) ^ (100 * η) + Real.exp (60 * L) ≤
      2 * ((P : ℝ) ^ (100 * η) * Real.exp (60 * L)) := by nlinarith
  have hX0 : 0 ≤ η⁻¹ * ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)) := by
    apply mul_nonneg (inv_nonneg.mpr hη0.le)
    apply Finset.prod_nonneg; intro p _; positivity
  have hAB0 : 0 ≤ (P : ℝ) ^ (100 * η) * Real.exp (60 * L) :=
    mul_nonneg (by linarith) (by linarith)
  calc η⁻¹ * (∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1))) * ((P : ℝ) ^ (100 * η) + Real.exp (60 * L))
      ≤ η⁻¹ * (∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1))) *
          (2 * ((P : ℝ) ^ (100 * η) * Real.exp (60 * L))) :=
        mul_le_mul_of_nonneg_left hAB hX0
    _ = (2 * (η⁻¹ * ∏ p ∈ S, (1 + (p : ℝ) ^ (η - 1)))) *
          ((P : ℝ) ^ (100 * η) * Real.exp (60 * L)) := by ring
    _ ≤ Real.exp (40 * L) * ((P : ℝ) ^ (100 * η) * Real.exp (60 * L)) :=
        mul_le_mul_of_nonneg_right hkey hAB0
    _ = (P : ℝ) ^ (100 * η) * Real.exp (60 * L) * Real.exp (40 * L) := by ring

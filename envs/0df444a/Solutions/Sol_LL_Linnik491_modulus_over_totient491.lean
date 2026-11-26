-- Prove2me | solution 1 for LL_Linnik491.modulus_over_totient491
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T06:23:28.044283+00:00
-- url     : https://prove2.me/submissions/97a4323c-4a8a-4ed5-b9d6-bbef378c1efb

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

private noncomputable def primeWeight (p : ℕ) : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ)

private theorem primeWeight_nonneg (p : ℕ) : 0 ≤ primeWeight p := by
  unfold primeWeight
  positivity

private theorem odd_prime_weight_bound (s : Finset ℕ)
    (hOdd : ∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1) :
    (∏ p ∈ s, primeWeight p) ^ 2 ≤ 2 * (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha := hOdd a (Finset.mem_insert_self a s)
    have hs (p : ℕ) (hp : p ∈ s) := hOdd p (Finset.mem_insert_of_mem hp)
    have ha_not_mem : a ∉ s := fun h => (Nat.lt_irrefl a) (hlt a h)
    have hcard : s.card ≤ a / 2 - 1 := by
      have h := Finset.card_le_card_of_injOn (s := s) (t := Finset.Ico 1 (a / 2))
        (fun p : ℕ => p / 2)
        (by
          intro p hp
          change p / 2 ∈ Finset.Ico 1 (a / 2)
          have hp_pos := (hs p hp).1
          have hp_odd := (hs p hp).2
          have hp_lt := hlt p hp
          simp only [Finset.mem_Ico]
          omega)
        (by
          intro p hp r hr heq
          have hp_odd := (hs p hp).2
          have hr_odd := (hs r hr).2
          change p / 2 = r / 2 at heq
          omega)
      simpa only [Nat.card_Ico] using h
    have hsize : 2 * s.card + 3 ≤ a := by omega
    have hsize_real : 2 * (s.card : ℝ) + 3 ≤ (a : ℝ) := by exact_mod_cast hsize
    have ha_real : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.1
    have hfactor : primeWeight a ^ 2 ≤ (2 * (s.card : ℝ) + 3) / (2 * (s.card : ℝ) + 1) := by
      calc
        primeWeight a ^ 2 ≤ (a : ℝ) / ((a : ℝ) - 2) := by
          rw [primeWeight, Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, div_pow]
          apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (by linarith)).2
          nlinarith only [ha_real]
        _ ≤ (2 * (s.card : ℝ) + 3) / (2 * (s.card : ℝ) + 1) := by
          apply (div_le_div_iff₀ (by linarith) (by positivity)).2
          nlinarith only [hsize_real]
    rw [Finset.prod_insert ha_not_mem, Finset.card_insert_of_notMem ha_not_mem, mul_pow]
    calc
      primeWeight a ^ 2 * (∏ p ∈ s, primeWeight p) ^ 2
          ≤ primeWeight a ^ 2 * (2 * (s.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (ih hs) (sq_nonneg _)
      _ ≤ ((2 * (s.card : ℝ) + 3) / (2 * (s.card : ℝ) + 1)) * (2 * (s.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = 2 * (s.card : ℝ) + 3 := div_mul_cancel₀ _ (by positivity)
      _ = 2 * ((s.card + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

private theorem totient_ratio_eq_product (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) = ∏ p ∈ n.primeFactors, primeWeight p := by
  have hPhi : 0 < (n.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hn)
  have hDen : 0 < ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hp_two := (Nat.prime_of_mem_primeFactors hp).two_le
    exact_mod_cast (show 0 < p - 1 by omega)
  unfold primeWeight
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hPhi.ne' hDen.ne').2
  have h : (n.totient : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using
      congrArg (fun x : ℕ => (x : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  exact h.symm.trans (mul_comm _ _)

theorem solution :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (q : ℝ) ≤ D * (q.totient : ℝ) * Real.sqrt (Real.log N) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hConstant : 0 < (3 : ℝ) / Real.log 2 := div_pos (by norm_num) hlogTwo
  refine ⟨2 * Real.sqrt (3 / Real.log 2), mul_pos (by norm_num) (Real.sqrt_pos.2 hConstant), 1, ?_⟩
  intro N hN q hq hqN
  have hN_two : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hN_pos : 0 < (N : ℝ) := by linarith only [hN_two]
  have hq_pos : 0 < q := hq
  have hq_real : 0 < (q : ℝ) := by exact_mod_cast hq_pos
  have hPhi : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq_pos)
  let s := q.primeFactors.erase 2
  have hs_subset : s ⊆ q.primeFactors := Finset.erase_subset _ _
  have hs_odd (p : ℕ) (hp : p ∈ s) : 3 ≤ p ∧ p % 2 = 1 := by
    have hp_ne := (Finset.mem_erase.mp hp).1
    have hp_prime := Nat.prime_of_mem_primeFactors (hs_subset hp)
    have hp_two := hp_prime.two_le
    exact ⟨by omega, hp_prime.eq_two_or_odd.resolve_left hp_ne⟩
  have hs_nonneg : 0 ≤ ∏ p ∈ s, primeWeight p :=
    Finset.prod_nonneg (fun p _ => primeWeight_nonneg p)
  have hEuler : (q : ℝ) / (q.totient : ℝ) ≤ 2 * ∏ p ∈ s, primeWeight p := by
    rw [totient_ratio_eq_product q hq_pos]
    by_cases ht : 2 ∈ q.primeFactors
    · calc
        (∏ p ∈ q.primeFactors, primeWeight p) = (∏ p ∈ s, primeWeight p) * primeWeight 2 :=
          (Finset.prod_erase_mul _ _ ht).symm
        _ ≤ 2 * ∏ p ∈ s, primeWeight p := by
          have hWeight : primeWeight 2 = 2 := by norm_num [primeWeight]
          rw [hWeight]
          exact le_of_eq (mul_comm _ _)
    · have hs_eq : s = q.primeFactors := Finset.erase_eq_of_notMem ht
      rw [← hs_eq]
      linarith only [hs_nonneg]
  have hPow : (2 : ℕ) ^ s.card ≤ q := by
    calc
      (2 : ℕ) ^ s.card = ∏ _p ∈ s, 2 := by simp
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod' (fun p hp => le_trans (by decide) (hs_odd p hp).1)
      _ ≤ q := Nat.le_of_dvd hq_pos
        ((Finset.prod_dvd_prod_of_subset _ _ id hs_subset).trans (Nat.prod_primeFactors_dvd q))
  have hLogPow : (s.card : ℝ) * Real.log 2 ≤ Real.log q := by
    have h : (2 : ℝ) ^ s.card ≤ (q : ℝ) := by exact_mod_cast hPow
    simpa only [Real.log_pow] using (Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ s.card) h)
  have hLogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN_two
  have hLogN_nonneg := hlogTwo.le.trans hLogN
  have hLogq : Real.log q ≤ Real.log N := by
    have h := Real.log_le_log hq_real hqN
    rw [Real.log_rpow hN_pos] at h
    linarith only [h, hLogN_nonneg]
  have hsBound : 2 * (s.card : ℝ) + 1 ≤ (3 / Real.log 2) * Real.log N := by
    calc
      _ ≤ (3 * Real.log N) / Real.log 2 := by
        apply (le_div_iff₀ hlogTwo).mpr
        nlinarith only [hLogPow.trans hLogq, hLogN]
      _ = _ := by ring
  have hSqrt : (∏ p ∈ s, primeWeight p) ≤ Real.sqrt (2 * (s.card : ℝ) + 1) :=
    Real.le_sqrt_of_sq_le (odd_prime_weight_bound s hs_odd)
  have hRatio : (q : ℝ) / (q.totient : ℝ) ≤ (2 * Real.sqrt (3 / Real.log 2)) * Real.sqrt (Real.log N) := by
    calc
      _ ≤ 2 * ∏ p ∈ s, primeWeight p := hEuler
      _ ≤ 2 * Real.sqrt (2 * (s.card : ℝ) + 1) := mul_le_mul_of_nonneg_left hSqrt (by norm_num)
      _ ≤ 2 * Real.sqrt ((3 / Real.log 2) * Real.log N) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsBound) (by norm_num)
      _ = _ := by rw [Real.sqrt_mul hConstant.le, mul_assoc]
  calc
    _ ≤ (2 * Real.sqrt (3 / Real.log 2) * Real.sqrt (Real.log N)) * (q.totient : ℝ) :=
      (div_le_iff₀ hPhi).mp hRatio
    _ = _ := by ring

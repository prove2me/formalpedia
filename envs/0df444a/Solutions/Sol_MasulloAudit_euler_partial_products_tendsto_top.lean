-- Prove2me | solution 1 for MasulloAudit.euler_partial_products_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:51:33.510025+00:00
-- url     : https://prove2.me/submissions/577772fd-6595-4aae-b40e-dba86f6f65e2

import Mathlib

open Filter Set

lemma euler_aux_sum_le_prod (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ S, a i ≤ ∏ i ∈ S, (1 + a i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hP : 1 ≤ ∏ i ∈ S, (1 + a i) :=
      Finset.one_le_prod (fun i _ => by linarith [ha i])
    nlinarith [ha j]

theorem solution (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun x : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)),
      (1 - (p : ℝ) ^ (-s))⁻¹) atTop atTop := by
  set f : ℕ → ℝ := indicator {p | p.Prime} (fun n : ℕ => (n : ℝ) ^ (-s)) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => indicator_nonneg (fun _ _ => by positivity) _
  have hns : ¬ Summable f := by
    intro h
    apply not_summable_one_div_on_primes
    refine h.of_nonneg_of_le (fun n => indicator_nonneg (fun _ _ => by positivity) _) ?_
    intro n
    by_cases hn : n.Prime
    · simp only [hf, indicator_of_mem (show n ∈ {p | p.Prime} from hn)]
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.one_lt.le) (by linarith)
    · simp [hf, indicator_of_notMem (show n ∉ {p | p.Prime} from hn)]
  have hT := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).1 hns
  have hT' : Tendsto (fun x : ℕ => 1 + ∑ i ∈ Finset.range (x + 1), f i) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (hT.comp (tendsto_add_atTop_nat 1))
  refine tendsto_atTop_mono (fun x => ?_) hT'
  have hsum : ∑ i ∈ Finset.range (x + 1), f i =
      ∑ p ∈ Finset.filter Nat.Prime (Finset.range (x + 1)), (p : ℝ) ^ (-s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : n.Prime
    · simp [hf, hn]
    · simp [hf, hn]
  rw [hsum]
  refine (euler_aux_sum_le_prod _ (fun p => (p : ℝ) ^ (-s)) (fun _ => by positivity)).trans ?_
  refine Finset.prod_le_prod (fun _ _ => by positivity) (fun p hp => ?_)
  have hp : p.Prime := (Finset.mem_filter.1 hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : 0 < (p : ℝ) ^ (-s) := by positivity
  have hlt : (p : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  rw [← one_div, le_div_iff₀ (by linarith)]
  nlinarith

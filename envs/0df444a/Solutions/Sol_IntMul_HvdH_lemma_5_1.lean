-- Prove2me | solution 1 for IntMul.HvdH.lemma_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-08T23:51:00.421982+00:00
-- url     : https://prove2.me/submissions/68403c24-ac15-4f91-9461-0ce32f8f403a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_HvdH_rosser_schoenfeld_thm4

open Real

theorem solution (η : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1 / 4) (x : ℝ) (hx : Real.exp (2 / η) ≤ x) :
    η * x / (2 * Real.log x) ≤
      ({q : ℕ | q.Prime ∧ (1 - 2 * η) * x < q ∧ (q : ℝ) ≤ (1 - η) * x}.ncard : ℝ) := by
  -- size facts: x ≥ e^{2/η} > e^8 > 2978
  have h8 : 8 < 2 / η := by rw [lt_div_iff₀ hη₀]; linarith
  have he8 : (2978 : ℝ) < exp 8 := by
    have h1 := Real.exp_one_gt_d9
    have : exp 8 = exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (8 : ℕ) ≠ 0)
    norm_num at this ⊢; linarith
  have hx8 : (2978 : ℝ) < x := he8.trans_le ((exp_le_exp.2 h8.le).trans hx)
  have hxpos : 0 < x := by linarith
  have hlogx : 2 / η ≤ log x := by
    have := log_le_log (exp_pos _) hx; rwa [log_exp] at this
  have hlogpos : 0 < log x := by linarith [div_pos two_pos hη₀]
  set y0 : ℝ := (1 - 2 * η) * x with hy0_def
  set y1 : ℝ := (1 - η) * x with hy1_def
  have hy0 : (563 : ℝ) ≤ y0 := by rw [hy0_def]; nlinarith
  have hy01 : y0 ≤ y1 := by rw [hy0_def, hy1_def]; nlinarith
  have hy1x : y1 ≤ x := by rw [hy1_def]; nlinarith
  -- y / log y is increasing on [e, ∞), so y/(2 log y) ≤ x/(2 log x) for 563 ≤ y ≤ x
  have hmono : ∀ y : ℝ, 563 ≤ y → y ≤ x → y / (2 * log y) ≤ x / (2 * log x) := by
    intro y hy hyx
    have he1 : exp 1 < 563 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.2 (by linarith : exp 1 ≤ y))
      (Set.mem_Ici.2 (by linarith : exp 1 ≤ x)) hyx
    simp only at hanti
    have hly : 0 < log y := log_pos (by linarith)
    have hyp : 0 < y := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_div_iff₀ hxpos hyp] at hanti
    nlinarith
  -- Rosser–Schoenfeld at y1 (lower bound) and at y0 (upper bound)
  obtain ⟨h1l, -⟩ := IntMul.HvdH.rosser_schoenfeld_thm4 y1 (hy0.trans hy01)
  obtain ⟨-, h0u⟩ := IntMul.HvdH.rosser_schoenfeld_thm4 y0 hy0
  have hgap : η * x / 2 < Chebyshev.theta y1 - Chebyshev.theta y0 := by
    have m1 := hmono y1 (hy0.trans hy01) hy1x
    have m0 := hmono y0 hy0 (hy01.trans hy1x)
    have hxl : x / log x ≤ η * x / 2 := by
      rw [div_le_div_iff₀ hlogpos two_pos]
      have : 2 ≤ η * log x := by rw [div_le_iff₀ hη₀] at hlogx; linarith
      nlinarith
    have : x / (2 * log x) + x / (2 * log x) = x / log x := by field_simp; ring
    have hyd : y1 - y0 = η * x := by rw [hy0_def, hy1_def]; ring
    linarith
  -- θ(y1) - θ(y0) is the sum of log p over the primes in (y0, y1]
  have hy0n : (0 : ℝ) ≤ y0 := by linarith
  have hy1n : (0 : ℝ) ≤ y1 := by linarith
  set S : Finset ℕ := (Finset.Icc 0 ⌊y1⌋₊).filter (fun p => p.Prime ∧ ¬ p ≤ ⌊y0⌋₊) with hS
  have hfloor : ⌊y0⌋₊ ≤ ⌊y1⌋₊ := Nat.floor_le_floor hy01
  have hsplit : Chebyshev.theta y1 - Chebyshev.theta y0 = ∑ p ∈ S, log p := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 0 ⌊y1⌋₊).filter Nat.Prime)
      (fun p => p ≤ ⌊y0⌋₊)]
    have hA0 : ((Finset.Icc 0 ⌊y1⌋₊).filter Nat.Prime).filter (fun p => p ≤ ⌊y0⌋₊) =
        (Finset.Icc 0 ⌊y0⌋₊).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨⟨_, _⟩, hp⟩, h⟩; exact ⟨⟨Nat.zero_le _, h⟩, hp⟩
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨⟨⟨Nat.zero_le _, h.trans hfloor⟩, hp⟩, h⟩
    have hS' : ((Finset.Icc 0 ⌊y1⌋₊).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y0⌋₊) = S := by
      rw [hS, Finset.filter_filter]
    rw [hA0, hS']; ring
  -- each log p ≤ log x
  have hsum_le : ∑ p ∈ S, log (p : ℝ) ≤ S.card * log x := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
    have : (p : ℝ) ≤ x := by
      have := (Nat.le_floor_iff hy1n).1 hp.1.2; linarith
    exact log_le_log (by linarith) this
  -- the target set is S
  have hset : {q : ℕ | q.Prime ∧ (1 - 2 * η) * x < q ∧ (q : ℝ) ≤ (1 - η) * x} = (S : Set ℕ) := by
    ext q
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_Icc, hS]
    rw [← hy0_def, ← hy1_def, Nat.le_floor_iff hy1n, Nat.le_floor_iff hy0n, not_le]
    constructor
    · rintro ⟨hp, h0, h1⟩; exact ⟨⟨Nat.zero_le _, h1⟩, hp, h0⟩
    · rintro ⟨⟨_, h1⟩, hp, h0⟩; exact ⟨hp, h0, h1⟩
  rw [hset, Set.ncard_coe_finset]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

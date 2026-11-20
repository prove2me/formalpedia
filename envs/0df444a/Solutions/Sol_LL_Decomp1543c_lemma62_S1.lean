-- Prove2me | solution 1 for LL_Decomp1543c.lemma62_S1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:39:38.852307+00:00
-- url     : https://prove2.me/submissions/493373ce-3e57-452a-870b-a643ea7d5aa6

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_lam1
import Definitions.Def_LL_Decomp1543c_Uf
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_excess_upper_large

open Real Finset ArithmeticFunction LL_Decomp1543c

private lemma norm_e_eq_one (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : (2 * π * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma log_Uf_ge (N : ℕ) (hL : 3100 ≤ Real.log N) :
    1000 ≤ Real.log (Uf N) := by
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    by_contra h
    have hle : (N : ℝ) ≤ 0 := le_of_not_gt h
    have hN0 : N = 0 := by
      exact_mod_cast le_antisymm hle (Nat.cast_nonneg N)
    rw [hN0] at hLpos
    simp at hLpos
  unfold Uf
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hLpos]
  have hlogL : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) / 50 + 4 := by
    have h1 : Real.log (Real.log (N : ℝ) / 50) ≤ Real.log (N : ℝ) / 50 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hLpos) (by norm_num)] at h1
    have h50 : Real.log 50 ≤ 5 := by
      have h50' : (50 : ℝ) ≤ Real.exp 5 := by
        have h1e : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        have h5e : (2 : ℝ) ^ 5 ≤ Real.exp 5 := by
          calc (2 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := by gcongr
            _ = Real.exp (5 * 1) := by rw [← Real.exp_nat_mul]; norm_num
            _ = Real.exp 5 := by ring_nf
        have h25 : (50 : ℝ) ≤ (2.5 : ℝ) ^ 5 := by norm_num
        have he25 : (2.5 : ℝ) ≤ Real.exp 1 := by
          have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
          simp [Finset.sum_range_succ, Nat.factorial] at this
          linarith
        calc (50 : ℝ) ≤ (2.5 : ℝ) ^ 5 := h25
          _ ≤ (Real.exp 1) ^ 5 := by gcongr
          _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      have := Real.log_le_log (by norm_num) h50'
      rwa [Real.log_exp] at this
    linarith
  linarith

private lemma Uf_ge_10pow8 (N : ℕ) (hL : 3100 ≤ Real.log N) :
    (10 : ℝ) ^ 8 ≤ Uf N := by
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    by_contra h
    have hle : (N : ℝ) ≤ 0 := le_of_not_gt h
    have hN0 : N = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg N)
    rw [hN0] at hLpos; simp at hLpos
  have hUpos : 0 < Uf N := by unfold Uf; positivity
  have hlogU : 1000 ≤ Real.log (Uf N) := log_Uf_ge N hL
  have hexp : Real.exp 1000 ≤ Uf N := by
    have := Real.exp_le_exp.mpr hlogU
    rwa [Real.exp_log hUpos] at this
  have h10 : (10 : ℝ) ^ 8 ≤ Real.exp 1000 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (10 : ℝ) ^ 8 ≤ (2 : ℝ) ^ 30 := by norm_num
      _ ≤ (Real.exp 1) ^ 30 := by gcongr
      _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp 1000 := Real.exp_le_exp.mpr (by norm_num)
  linarith

theorem solution (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N := by
  have hU8 : (10 : ℝ) ^ 8 ≤ Uf N := Uf_ge_10pow8 N hL
  have hUpos : 0 < Uf N := by linarith
  have hlogU : 1000 ≤ Real.log (Uf N) := log_Uf_ge N hL
  have htri : ‖Ssum (lam1 (Uf N)) c N α‖ ≤ ∑ n ∈ rangeN c N, lam1 (Uf N) n := by
    unfold Ssum
    calc ‖∑ n ∈ rangeN c N, (lam1 (Uf N) n : ℂ) * e (α * n)‖
        ≤ ∑ n ∈ rangeN c N, ‖(lam1 (Uf N) n : ℂ) * e (α * n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ rangeN c N, lam1 (Uf N) n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, norm_e_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          unfold lam1
          split_ifs
          · exact ArithmeticFunction.vonMangoldt_nonneg
          · exact le_rfl
  have hsum_le_psi : ∑ n ∈ rangeN c N, lam1 (Uf N) n ≤ Chebyshev.psi (Uf N) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    calc ∑ n ∈ rangeN c N, lam1 (Uf N) n
        = ∑ n ∈ (rangeN c N).filter (fun n : ℕ => (n : ℝ) ≤ Uf N), (vonMangoldt n : ℝ) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun n _ => ?_
            unfold lam1; rfl
      _ ≤ ∑ n ∈ Finset.Icc 0 ⌊Uf N⌋₊, (vonMangoldt n : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
            intro n hn
            simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
            exact ⟨Nat.zero_le n, Nat.le_floor hn.2⟩
  have hschoen := TaoFivePrimes.schoenfeld_psi_excess_upper_large (Uf N) hU8
  have herr : Uf N / (40 * Real.log (Uf N)) ≤ 0.02 * Uf N := by
    have h40 : (50 : ℝ) ≤ 40 * Real.log (Uf N) := by linarith
    have hdiv : Uf N / (40 * Real.log (Uf N)) ≤ Uf N / 50 :=
      div_le_div_of_nonneg_left (le_of_lt hUpos) (by norm_num) h40
    linarith
  linarith

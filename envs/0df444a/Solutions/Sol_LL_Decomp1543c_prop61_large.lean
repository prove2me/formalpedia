-- Prove2me | solution 1 for LL_Decomp1543c.prop61_large
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:01:41.036415+00:00
-- url     : https://prove2.me/submissions/43cd91d9-736e-4bb4-a4f2-947408a0705e

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_Dioph
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_lam1
import Definitions.Def_LL_Decomp1543c_lam2
import Definitions.Def_LL_Decomp1543c_lam3
import Definitions.Def_LL_Decomp1543c_Uf
import Definitions.Def_LL_Decomp1543c_Vf
import Definitions.Def_LL_Decomp1543c_WCLemma3
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_rangeN
import Definitions.Def_LL_Decomp1543a_Ssum
import Definitions.Def_LL_Decomp1543a_Dioph
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_lam1
import Definitions.Def_LL_Decomp1543a_lam2
import Definitions.Def_LL_Decomp1543a_lam3
import Definitions.Def_LL_Decomp1543a_lam4
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_Jn
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_lRange
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner
import Definitions.Def_LL_Decomp1543a_block
import Theorems.Thm_LL_Decomp1543c_lemma62_S1
import Theorems.Thm_LL_Decomp1543c_S1_absorb
import Theorems.Thm_LL_Decomp1543c_S2_le
import Theorems.Thm_LL_Decomp1543c_S3_le
import Theorems.Thm_LL_Decomp1543c_wc_lemma3
import Theorems.Thm_LL_Decomp1543c_n65a
import Theorems.Thm_LL_Decomp1543c_n65b
import Theorems.Thm_LL_Decomp1543c_n65c
import Theorems.Thm_LL_Decomp1543c_n66a
import Theorems.Thm_LL_Decomp1543c_n66b
import Theorems.Thm_LL_Decomp1543c_n66c
import Theorems.Thm_LL_Decomp1543a_S_split
import Theorems.Thm_LL_Decomp1543a_S4_dyadic
import Theorems.Thm_LL_Decomp1543a_block_cauchy
import Theorems.Thm_LL_Decomp1543a_square_expand
import Theorems.Thm_LL_Decomp1543a_geom_dyadic
import Theorems.Thm_LL_Decomp1543a_J_props
import Theorems.Thm_LL_Decomp1543a_dyadic_sqrt_sum
import Theorems.Thm_LL_Decomp1543a_dyadic_invsqrt_sum
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_excess_upper_large
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_deficit_lower_large

open Real Finset ArithmeticFunction LL_Decomp1543c

/-! ### Part 1: Bridge equalities between `LL_Decomp1543a` and `LL_Decomp1543c` definitions -/

private lemma e_eq_a (x : ℝ) : e x = LL_Decomp1543a.e x := rfl
private lemma rangeN_eq_a (c : ℝ) (N : ℕ) : rangeN c N = LL_Decomp1543a.rangeN c N := rfl
private lemma Ssum_eq_a (f : ℕ → ℝ) (c : ℝ) (N : ℕ) (α : ℝ) :
    Ssum f c N α = LL_Decomp1543a.Ssum f c N α := rfl
private lemma lam1_eq_a (U : ℝ) : lam1 U = LL_Decomp1543a.lam1 U := rfl
private lemma lam2_eq_a (V : ℝ) : lam2 V = LL_Decomp1543a.lam2 V := rfl
private lemma lam3_eq_a (U V : ℝ) : lam3 U V = LL_Decomp1543a.lam3 U V := rfl
private lemma nint_eq_a (x : ℝ) : nint x = LL_Decomp1543a.nint x := rfl
private lemma minK_eq_a (X θ : ℝ) : minK X θ = LL_Decomp1543a.minK X θ := rfl

/-! ### Part 2: Elementary log and parameter bounds for `log N ≥ 3100` -/

private lemma exp_one_lt_272 : Real.exp 1 < (2.72 : ℝ) := by
  linarith [Real.exp_one_lt_d9]

private lemma exp_one_gt_271 : (2.71 : ℝ) < Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

private lemma N_pos_of_hL (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) : (0 : ℝ) < (N : ℝ) := by
  by_contra h
  have hle : (N : ℝ) ≤ 0 := le_of_not_gt h
  have hN0 : N = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg N)
  rw [hN0] at hL; simp at hL; linarith

private lemma log_le_003_mul (x : ℝ) (hx : 3100 ≤ x) : Real.log x ≤ 0.003 * x := by
  have hxpos : 0 < x := by linarith
  have h1 : Real.log (x / 1000) ≤ x / 1000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num)] at h1
  have h1000 : Real.log 1000 ≤ 7 := by
    have hle : (1000 : ℝ) ≤ Real.exp 7 := by
      calc (1000 : ℝ) ≤ (2.71 : ℝ) ^ 7 := by norm_num
        _ ≤ (Real.exp 1) ^ 7 := by gcongr; exact le_of_lt exp_one_gt_271
        _ = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.log_le_log (by norm_num) hle
    rwa [Real.log_exp] at this
  linarith

private lemma log_Uf_ge_1000 (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) :
    1000 ≤ Real.log (Uf N) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  unfold Uf
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hLpos]
  have hlogL := log_le_003_mul (Real.log (N : ℝ)) hL
  linarith

private lemma log_Vf_ge_1200 (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) :
    1200 ≤ Real.log (Vf N) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hlogL_nn : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  unfold Vf
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hLpos]
  linarith

private lemma exp_ge_10pow9 (y : ℝ) (hy : 1000 ≤ y) : (10 : ℝ) ^ 9 ≤ Real.exp y := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (10 : ℝ) ^ 9 ≤ (2 : ℝ) ^ 30 := by norm_num
    _ ≤ (Real.exp 1) ^ 30 := by gcongr
    _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)

private lemma Uf_ge_10pow9 (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) : (10 : ℝ) ^ 9 ≤ Uf N := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hUpos : 0 < Uf N := by unfold Uf; positivity
  have h1 := Real.exp_le_exp.mpr (log_Uf_ge_1000 N hL)
  rw [Real.exp_log hUpos] at h1
  exact le_trans (exp_ge_10pow9 1000 le_rfl) h1

private lemma Vf_ge_10pow9 (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) : (10 : ℝ) ^ 9 ≤ Vf N := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hVpos : 0 < Vf N := by unfold Vf; positivity
  have h1 := Real.exp_le_exp.mpr (log_Vf_ge_1200 N hL)
  rw [Real.exp_log hVpos] at h1
  exact le_trans (exp_ge_10pow9 1200 (by norm_num)) h1

private lemma Uf_mul_Vf_le_N (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) :
    Uf N * Vf N ≤ (N : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hUpos : 0 < Uf N := by unfold Uf; positivity
  have hVpos : 0 < Vf N := by unfold Vf; positivity
  have hlogL_nn : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log (Uf N * Vf N) ≤ Real.log (N : ℝ) := by
    rw [Real.log_mul (ne_of_gt hUpos) (ne_of_gt hVpos)]
    unfold Uf Vf
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hNpos, Real.log_rpow hLpos, Real.log_rpow hLpos]
    linarith
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (mul_pos hUpos hVpos), Real.exp_log hNpos] at this

private lemma log_N_div_UV_le (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) :
    Real.log ((N : ℝ) / (Uf N * Vf N)) ≤ 0.2018 * Real.log (N : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hUpos : 0 < Uf N := by unfold Uf; positivity
  have hVpos : 0 < Vf N := by unfold Vf; positivity
  rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt (mul_pos hUpos hVpos)),
      Real.log_mul (ne_of_gt hUpos) (ne_of_gt hVpos)]
  unfold Uf Vf
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hLpos, Real.log_rpow hLpos]
  have hlogL := log_le_003_mul (Real.log (N : ℝ)) hL
  linarith

private lemma log_N_div_Vf_le (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) :
    Real.log ((N : ℝ) / Vf N) ≤ 0.6 * Real.log (N : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hVpos : 0 < Vf N := by unfold Vf; positivity
  have hlogL_nn : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hVpos)]
  unfold Vf
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hNpos, Real.log_rpow hLpos]
  linarith

private lemma q_ge_15_of_hq1 (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log (N : ℝ) ^ 4 < (q : ℝ)) : 15 ≤ q := by
  have hL4 : (3100 : ℝ) ^ 4 ≤ Real.log (N : ℝ) ^ 4 := by gcongr
  have h15 : (15 : ℝ) < (q : ℝ) := by
    calc (15 : ℝ) < (0.28 / 1.0012) ^ 2 * (3100 : ℝ) ^ 4 := by norm_num
      _ ≤ (0.28 / 1.0012) ^ 2 * Real.log (N : ℝ) ^ 4 := by gcongr
      _ < (q : ℝ) := hq1
  have : (15 : ℕ) < q := by exact_mod_cast h15
  omega

private lemma log_q_le_log_N (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) (q : ℕ)
    (hq1 : 1 ≤ q) (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 5) :
    Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hL5 : (1.0012 / 0.09 : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 5 := by
    calc (1.0012 / 0.09 : ℝ) ^ 2 ≤ (3100 : ℝ) ^ 5 := by norm_num
      _ ≤ Real.log (N : ℝ) ^ 5 := by gcongr
  have hqle : (q : ℝ) ≤ (N : ℝ) := by
    have hmul : (1.0012 / 0.09) ^ 2 * (N : ℝ) ≤ Real.log (N : ℝ) ^ 5 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hL5 (le_of_lt hNpos)
    have hdiv : (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 5 ≤ (N : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  exact Real.log_le_log (by positivity) hqle

/-! ### Part 3: Midpoint block bound (`3 * X + q * log q`) and sharp `inner_l_sum` -/

private lemma minK_le_left (X θ : ℝ) : minK X θ ≤ X := by
  unfold minK; split_ifs; exact le_rfl; exact min_le_left _ _

private lemma minK_le_inv (X θ : ℝ) (hpos : 0 < nint θ) :
    minK X θ ≤ 1 / (2 * nint θ) := by
  unfold minK; rw [if_neg (ne_of_gt hpos)]; exact min_le_right _ _

private lemma abs_sub_div_ge_symmMod (q : ℕ) (hq : 1 ≤ q) (M m : ℤ) :
    ((min (M % (q : ℤ)).toNat (q - (M % (q : ℤ)).toNat) : ℕ) : ℝ) / q ≤
      |(M : ℝ) / q - (m : ℝ)| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqz : (0 : ℤ) < (q : ℤ) := by omega
  have hr_nonneg : 0 ≤ M % (q : ℤ) := Int.emod_nonneg M (ne_of_gt hqz)
  have hr_lt : M % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos M hqz
  set v : ℕ := (M % (q : ℤ)).toNat
  have hv_cast : (v : ℤ) = M % (q : ℤ) := Int.toNat_of_nonneg hr_nonneg
  have hv_lt : v < q := by omega
  have hdiv_eq : (M : ℝ) / q - (m : ℝ) = ((M - (q : ℤ) * m : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [hdiv_eq, abs_div, abs_of_pos hqpos]
  apply div_le_div_of_nonneg_right _ (le_of_lt hqpos)
  have hM : M = (q : ℤ) * (M / (q : ℤ)) + (v : ℤ) := by
    have := Int.mul_ediv_add_emod M (q : ℤ); omega
  set t : ℤ := M / (q : ℤ) - m
  have hdiff : M - (q : ℤ) * m = (q : ℤ) * t + (v : ℤ) := by dsimp [t]; linarith
  have habs_int : ((min v (q - v) : ℕ) : ℤ) ≤ |M - (q : ℤ) * m| := by
    rw [hdiff]
    by_cases ht : 0 ≤ t
    · have hge : (v : ℤ) ≤ (q : ℤ) * t + (v : ℤ) := by nlinarith
      rw [abs_of_nonneg (by omega)]
      have hle : ((min v (q - v) : ℕ) : ℤ) ≤ (v : ℤ) :=
        Nat.cast_le.mpr (Nat.min_le_left v (q - v))
      omega
    · have ht' : t ≤ -1 := by omega
      have hle : (q : ℤ) * t + (v : ℤ) ≤ -((q - v : ℕ) : ℤ) := by
        have hqv : ((q - v : ℕ) : ℤ) = (q : ℤ) - (v : ℤ) := by omega
        nlinarith
      rw [abs_of_nonpos (by omega)]
      have hle2 : ((min v (q - v) : ℕ) : ℤ) ≤ ((q - v : ℕ) : ℤ) :=
        Nat.cast_le.mpr (Nat.min_le_right v (q - v))
      omega
  have habs_real : (((min v (q - v) : ℕ) : ℤ) : ℝ) ≤ (|M - (q : ℤ) * m| : ℤ) :=
    Int.cast_le.mpr habs_int
  simpa using habs_real

private lemma nint_ge_of_approx (q : ℕ) (hq : 1 ≤ q) (M : ℤ) (x err : ℝ)
    (herr : |x - (M : ℝ) / q| ≤ err) :
    ((min (M % (q : ℤ)).toNat (q - (M % (q : ℤ)).toNat) : ℕ) : ℝ) / q - err ≤ nint x := by
  unfold nint
  set m : ℤ := round x
  have h1 := abs_sub_div_ge_symmMod q hq M m
  have htri : |(M : ℝ) / q - (m : ℝ)| ≤ |x - (m : ℝ)| + |x - (M : ℝ) / q| := by
    have hsplit : (M : ℝ) / q - (m : ℝ) = (x - (m : ℝ)) - (x - (M : ℝ) / q) := by ring
    rw [hsplit]; exact abs_sub _ _
  linarith

private lemma harmonic_ge6_bound (m : ℕ) (hm : 6 ≤ m) :
    ∑ j ∈ Icc 1 m, (1 : ℝ) / (j : ℝ) ≤ Real.log (2 * (m : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hsum : ∑ j ∈ Icc (1 : ℕ) 6, (1 : ℝ) / (j : ℝ) = 49 / 20 := by
      have : Icc (1 : ℕ) 6 = {1, 2, 3, 4, 5, 6} := by decide
      rw [this]; norm_num
    rw [hsum]
    have hexp : Real.exp (49 / 20 : ℝ) ≤ (12 : ℝ) := by
      have hpow : (Real.exp (49 / 20 : ℝ)) ^ 20 ≤ (12 : ℝ) ^ 20 := by
        rw [← Real.exp_nat_mul]
        have h49 : (20 : ℕ) * (49 / 20 : ℝ) = (49 : ℕ) * (1 : ℝ) := by norm_num
        rw [h49, Real.exp_nat_mul]
        calc (Real.exp 1) ^ 49 ≤ (2.72 : ℝ) ^ 49 := by gcongr; exact le_of_lt exp_one_lt_272
          _ ≤ (12 : ℝ) ^ 20 := by norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
    have := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at this
    rw [show (2 : ℝ) * ((6 : ℕ) : ℝ) = 12 by norm_num]
    exact this
  | succ k hk ih =>
    have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp)]
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
        Real.log (2 * ((k + 1 : ℕ) : ℝ)) - Real.log (2 * (k : ℝ)) := by
      push_cast
      have hk_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
      have hk1_pos : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)] at hlog
      have hcalc : (2 * (k : ℝ)) / (2 * ((k : ℝ) + 1)) - 1 = -(1 / ((k : ℝ) + 1)) := by
        field_simp; ring
      rw [hcalc] at hlog
      linarith
    linarith

private lemma harmonic_half_le_log (q : ℕ) (hq : 15 ≤ q) :
    ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) ≤ Real.log (q : ℝ) := by
  set m := q / 2 - 1
  have hm6 : 6 ≤ m := by omega
  have hq_ge : 2 * m ≤ q := by omega
  have hq_ge_r : (2 : ℝ) * (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_ge
  calc ∑ j ∈ Icc 1 m, (1 : ℝ) / (j : ℝ)
      ≤ Real.log (2 * (m : ℝ)) := harmonic_ge6_bound m hm6
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (by positivity) hq_ge_r

private lemma block_minK_bound (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (hq15 : 15 ≤ q)
    (X : ℝ) (hX : 0 < X) (n₀ : ℤ) (S : Finset ℤ)
    (hS : ∀ n ∈ S, n₀ ≤ n ∧ n < n₀ + (q : ℤ)) :
    ∑ n ∈ S, minK X (α * (n : ℝ)) ≤ 3 * X + (q : ℝ) * Real.log (q : ℝ) := by
  rcases hD with ⟨hq1, hgcd, happrox⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqz : (0 : ℤ) < (q : ℤ) := by omega
  set hqhalf : ℕ := (q - 1) / 2
  set m₀ : ℤ := n₀ + (hqhalf : ℤ)
  set b : ℤ := round ((q : ℝ) * (α * (m₀ : ℝ)))
  let M : ℤ → ℤ := fun n => b + a * (n - m₀)
  let rval : ℤ → ℕ := fun n => (M n % (q : ℤ)).toNat
  have hrval_mem : ∀ n, rval n ∈ Finset.range q := by
    intro n; rw [Finset.mem_range]
    have hlt := Int.emod_lt_of_pos (M n) hqz
    have hnn := Int.emod_nonneg (M n) (ne_of_gt hqz)
    have hcast : ((rval n : ℕ) : ℤ) = M n % (q : ℤ) := Int.toNat_of_nonneg hnn
    omega
  have hrval_inj : Set.InjOn rval S := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hnn₁ := Int.emod_nonneg (M n₁) (ne_of_gt hqz)
    have hnn₂ := Int.emod_nonneg (M n₂) (ne_of_gt hqz)
    have hmod : M n₁ % (q : ℤ) = M n₂ % (q : ℤ) := by
      have : ((rval n₁ : ℕ) : ℤ) = ((rval n₂ : ℕ) : ℤ) := by exact_mod_cast heq
      dsimp [rval] at this
      rwa [Int.toNat_of_nonneg hnn₁, Int.toNat_of_nonneg hnn₂] at this
    have hdvd : (q : ℤ) ∣ (M n₁ - M n₂) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hmod, sub_self, Int.zero_emod]
    have hdiff : M n₁ - M n₂ = a * (n₁ - n₂) := by dsimp [M]; ring
    rw [hdiff] at hdvd
    have hcop : IsCoprime (q : ℤ) a := by
      have : IsCoprime a (q : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.natAbs_natCast] using hgcd
      exact this.symm
    have hdvd' : (q : ℤ) ∣ (n₁ - n₂) := hcop.dvd_of_dvd_mul_left hdvd
    have h1 := hS n₁ hn₁; have h2 := hS n₂ hn₂
    rcases hdvd' with ⟨k, hk⟩
    have hk0 : k = 0 := by nlinarith
    rw [hk0, mul_zero] at hk; omega
  let g : ℕ → ℝ := fun v =>
    if min v (q - v) ≤ 1 then X else (q : ℝ) / (2 * (((min v (q - v) : ℕ) : ℝ) - 1))
  have hg_nonneg : ∀ v, 0 ≤ g v := by
    intro v; dsimp [g]; split_ifs with h
    · exact le_of_lt hX
    · have h2 : (2 : ℝ) ≤ ((min v (q - v) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (show 2 ≤ min v (q - v) by omega)
      apply div_nonneg (le_of_lt hqpos) (by linarith)
  have hterm : ∀ n ∈ S, minK X (α * (n : ℝ)) ≤ g (rval n) := by
    intro n hn; dsimp [g]; split_ifs with hle
    · exact minK_le_left _ _
    · have hge2 : 2 ≤ min (rval n) (q - rval n) := by omega
      have hge2r : (2 : ℝ) ≤ ((min (rval n) (q - rval n) : ℕ) : ℝ) := Nat.cast_le.mpr hge2
      have hnm_bound : |(n : ℝ) - (m₀ : ℝ)| ≤ (q : ℝ) / 2 := by
        have h1 := hS n hn
        have h1' : (n₀ : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (n₀ : ℝ) + (q : ℝ) - 1 := by
          constructor
          · exact_mod_cast h1.1
          · have : n ≤ n₀ + (q : ℤ) - 1 := by omega
            have : (n : ℝ) ≤ ((n₀ + (q : ℤ) - 1 : ℤ) : ℝ) := Int.cast_le.mpr this
            push_cast at this; linarith
        have hhalf : (hqhalf : ℝ) ≤ ((q : ℝ) - 1) / 2 ∧
            ((q : ℝ) - 2) / 2 ≤ (hqhalf : ℝ) := by
          have hq1' : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; simp
          constructor
          · have : 2 * hqhalf ≤ q - 1 := Nat.mul_div_le (q - 1) 2
            have : (2 : ℝ) * (hqhalf : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
            linarith
          · have : q - 1 ≤ 2 * hqhalf + 1 := by omega
            have : ((q - 1 : ℕ) : ℝ) ≤ (2 : ℝ) * (hqhalf : ℝ) + 1 := by exact_mod_cast this
            linarith
        have hm0r : (m₀ : ℝ) = (n₀ : ℝ) + (hqhalf : ℝ) := by
          dsimp [m₀]; rw [Int.cast_add, Int.cast_natCast]
        rw [abs_le]; constructor <;> linarith
      have herr : |α * (n : ℝ) - (M n : ℝ) / q| ≤ 1 / (q : ℝ) := by
        have hsplit : α * (n : ℝ) - (M n : ℝ) / q =
            ((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ) +
              (α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ)) := by
          dsimp [M]; push_cast; field_simp; ring
        rw [hsplit]
        have h1 : |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
          rw [abs_div, abs_of_pos hqpos]
          calc |(q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)| / (q : ℝ)
              ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right (abs_sub_round _) (le_of_lt hqpos)
            _ = 1 / (2 * (q : ℝ)) := by ring
        have h2 : |(α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))| ≤ 1 / (2 * (q : ℝ)) := by
          rw [abs_mul]
          calc |α - (a : ℝ) / (q : ℝ)| * |(n : ℝ) - (m₀ : ℝ)|
              ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
                mul_le_mul happrox hnm_bound (abs_nonneg _) (by positivity)
            _ = 1 / (2 * (q : ℝ)) := by field_simp
        calc |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ) +
                (α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))|
            ≤ |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ)| +
                |(α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))| := abs_add_le _ _
          _ ≤ 1 / (2 * (q : ℝ)) + 1 / (2 * (q : ℝ)) := add_le_add h1 h2
          _ = 1 / (q : ℝ) := by ring
      have hnint := nint_ge_of_approx q hq1 (M n) (α * (n : ℝ)) (1 / (q : ℝ)) herr
      have hpos : 0 < (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) :=
        div_pos (by linarith) hqpos
      have hnint' : (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) ≤ nint (α * (n : ℝ)) := by
        have : ((min (rval n) (q - rval n) : ℕ) : ℝ) / (q : ℝ) - 1 / (q : ℝ) =
            (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) := by ring
        rw [← this]; exact hnint
      have hnint_pos : 0 < nint (α * (n : ℝ)) := lt_of_lt_of_le hpos hnint'
      calc minK X (α * (n : ℝ))
          ≤ 1 / (2 * nint (α * (n : ℝ))) := minK_le_inv _ _ hnint_pos
        _ ≤ 1 / (2 * ((((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ))) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = (q : ℝ) / (2 * (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1)) := by field_simp
  have hsum_img : ∑ n ∈ S, minK X (α * (n : ℝ)) ≤ ∑ v ∈ Finset.range q, g v := by
    calc ∑ n ∈ S, minK X (α * (n : ℝ))
        ≤ ∑ n ∈ S, g (rval n) := Finset.sum_le_sum hterm
      _ = ∑ v ∈ S.image rval, g v := (Finset.sum_image (fun x hx y hy h => hrval_inj hx hy h)).symm
      _ ≤ ∑ v ∈ Finset.range q, g v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => hg_nonneg v)
          intro v hv; rcases Finset.mem_image.mp hv with ⟨n, _, rfl⟩; exact hrval_mem n
  set A := (Finset.range q).filter (fun v => min v (q - v) ≤ 1)
  set B := (Finset.range q).filter (fun v => ¬ min v (q - v) ≤ 1)
  have hsplit : ∑ v ∈ Finset.range q, g v = ∑ v ∈ A, g v + ∑ v ∈ B, g v :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun v => min v (q - v) ≤ 1) g).symm
  have hA_bound : ∑ v ∈ A, g v ≤ 3 * X := by
    have hA_sub : A ⊆ ({0, 1, q - 1} : Finset ℕ) := by
      intro v hv; simp only [A, mem_filter, mem_range, mem_insert, mem_singleton] at hv ⊢; omega
    have hcard : A.card ≤ 3 := by
      calc A.card ≤ ({0, 1, q - 1} : Finset ℕ).card := Finset.card_le_card hA_sub
        _ ≤ 3 := by
          calc ({0, 1, q - 1} : Finset ℕ).card
              ≤ ({1, q - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
            _ ≤ ({q - 1} : Finset ℕ).card + 1 + 1 := by
                have := Finset.card_insert_le (1 : ℕ) ({q - 1} : Finset ℕ); omega
            _ = 3 := by simp
    have hA_eq : ∑ v ∈ A, g v = (A.card : ℝ) * X := by
      calc ∑ v ∈ A, g v = ∑ _v ∈ A, X := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [A, mem_filter] at hv; dsimp [g]; rw [if_pos hv.2]
        _ = (A.card : ℝ) * X := by simp
    rw [hA_eq]; have : (A.card : ℝ) ≤ 3 := by exact_mod_cast hcard
    nlinarith
  have hB_bound : ∑ v ∈ B, g v ≤ (q : ℝ) * Real.log (q : ℝ) := by
    set B₁ := B.filter (fun v => v ≤ q / 2)
    set B₂ := B.filter (fun v => ¬ v ≤ q / 2)
    have hB_split : ∑ v ∈ B, g v = ∑ v ∈ B₁, g v + ∑ v ∈ B₂, g v :=
      (Finset.sum_filter_add_sum_filter_not B (fun v => v ≤ q / 2) g).symm
    have hB₁_le : ∑ v ∈ B₁, g v ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
      calc ∑ v ∈ B₁, g v
          = ∑ r ∈ B₁, (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [B₁, B, mem_filter, mem_range] at hv
            have hmin : min v (q - v) = v := Nat.min_eq_left (by omega)
            dsimp [g]; rw [if_neg hv.1.2, hmin]
        _ ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro v hv; simp only [B₁, B, mem_filter, mem_range, mem_Icc] at hv ⊢; omega
            · intro r hr _; simp only [mem_Icc] at hr
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
              apply div_nonneg (le_of_lt hqpos) (by linarith)
    have hB₂_le : ∑ v ∈ B₂, g v ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
      have hinj : Set.InjOn (fun v => q - v) B₂ := by
        intro v₁ hv₁ v₂ hv₂ heq
        simp only [Finset.mem_coe, B₂, B, mem_filter, mem_range] at hv₁ hv₂
        dsimp at heq; omega
      calc ∑ v ∈ B₂, g v
          = ∑ v ∈ B₂, (q : ℝ) / (2 * (((q - v : ℕ) : ℝ) - 1)) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [B₂, B, mem_filter, mem_range] at hv
            have hmin : min v (q - v) = q - v := Nat.min_eq_right (by omega)
            dsimp [g]; rw [if_neg hv.1.2, hmin]
        _ = ∑ r ∈ B₂.image (fun v => q - v), (q : ℝ) / (2 * ((r : ℝ) - 1)) :=
            (Finset.sum_image (f := fun r : ℕ => (q : ℝ) / (2 * ((r : ℝ) - 1)))
              (fun x hx y hy h => hinj hx hy h)).symm
        _ ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro r hr; rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
              simp only [B₂, B, mem_filter, mem_range, mem_Icc] at hv ⊢; omega
            · intro r hr _; simp only [mem_Icc] at hr
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
              apply div_nonneg (le_of_lt hqpos) (by linarith)
    have hshift : 2 * ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) =
        (q : ℝ) * ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_bij (fun r _ => r - 1) ?_ ?_ ?_ ?_
      · intro r hr; simp only [mem_Icc] at hr ⊢; omega
      · intro r₁ hr₁ r₂ hr₂ h; simp only [mem_Icc] at hr₁ hr₂; omega
      · intro j hj; refine ⟨j + 1, ?_, by omega⟩; simp only [mem_Icc] at hj ⊢; omega
      · intro r hr; simp only [mem_Icc] at hr
        have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        rw [hr1]; field_simp
    have hharm := harmonic_half_le_log q hq15
    calc ∑ v ∈ B, g v
        = ∑ v ∈ B₁, g v + ∑ v ∈ B₂, g v := hB_split
      _ ≤ 2 * ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by linarith
      _ = (q : ℝ) * ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) := hshift
      _ ≤ (q : ℝ) * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hharm (le_of_lt hqpos)
  linarith

private lemma inner_l_sum_sharp (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (hq15 : 15 ≤ q)
    (N : ℕ) (U Y X : ℝ) (hU : 0 ≤ U) (hY : 0 ≤ Y) (hX : 0 < X) (m : ℕ) :
    ∑ l ∈ LL_Decomp1543a.lRange N U Y, LL_Decomp1543a.minK X (α * ((m : ℝ) - (l : ℝ))) ≤
      (Y / (q : ℝ) + 1) * (3 * X + (q : ℝ) * Real.log (q : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  set A := ⌊U⌋₊ + 1
  set B := ⌊Y⌋₊
  have hminK_nn : ∀ θ : ℝ, 0 ≤ LL_Decomp1543a.minK X θ := by
    intro θ; rw [← minK_eq_a]; unfold minK; split_ifs
    · exact le_of_lt hX
    · apply le_min (le_of_lt hX); have : 0 ≤ nint θ := by unfold nint; exact abs_nonneg _
      positivity
  have hsub : LL_Decomp1543a.lRange N U Y ⊆ Icc A B := by
    intro l hl
    simp only [LL_Decomp1543a.lRange, mem_filter, mem_Icc] at hl ⊢
    constructor
    · exact (Nat.floor_lt hU).mpr hl.2.1
    · exact Nat.le_floor hl.2.2
  have hle_Icc : ∑ l ∈ LL_Decomp1543a.lRange N U Y, LL_Decomp1543a.minK X (α * ((m : ℝ) - (l : ℝ))) ≤
      ∑ l ∈ Icc A B, minK X (α * ((m : ℝ) - (l : ℝ))) := by
    calc ∑ l ∈ LL_Decomp1543a.lRange N U Y, LL_Decomp1543a.minK X (α * ((m : ℝ) - (l : ℝ)))
        ≤ ∑ l ∈ Icc A B, LL_Decomp1543a.minK X (α * ((m : ℝ) - (l : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hminK_nn _)
      _ = ∑ l ∈ Icc A B, minK X (α * ((m : ℝ) - (l : ℝ))) := by
          refine Finset.sum_congr rfl fun _ _ => (minK_eq_a _ _).symm
  by_cases hAB : B < A
  · have hemp : Icc A B = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
    rw [hemp, sum_empty] at hle_Icc
    have : 0 ≤ (Y / (q : ℝ) + 1) * (3 * X + (q : ℝ) * Real.log (q : ℝ)) := by positivity
    linarith
  · push Not at hAB
    set K := (B - A) / q
    let Blk : ℕ → Finset ℕ := fun k => Icc (A + k * q) (min B (A + (k + 1) * q - 1))
    have hdisj : Set.PairwiseDisjoint (↑(range (K + 1)) : Set ℕ) Blk := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro l hl₁ hl₂
      simp only [Blk, mem_Icc] at hl₁ hl₂
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (k₁ + 1) * q ≤ k₂ * q := Nat.mul_le_mul_right q (by omega)
        have h1 : 1 ≤ (k₁ + 1) * q := by nlinarith
        omega
      · have : (k₂ + 1) * q ≤ k₁ * q := Nat.mul_le_mul_right q (by omega)
        have h1 : 1 ≤ (k₂ + 1) * q := by nlinarith
        omega
    have hbi : (range (K + 1)).biUnion Blk = Icc A B := by
      ext l; simp only [mem_biUnion, mem_range, Blk, mem_Icc]
      constructor
      · rintro ⟨k, _, h1, h2⟩; omega
      · intro ⟨h1, h2⟩
        refine ⟨(l - A) / q, ?_, ?_, ?_⟩
        · have : (l - A) / q ≤ (B - A) / q := Nat.div_le_div_right (by omega)
          omega
        · have : (l - A) / q * q ≤ l - A := Nat.div_mul_le_self _ _
          omega
        · have : l - A < ((l - A) / q + 1) * q := by
            have := Nat.lt_div_mul_add (a := l - A) (b := q) (by omega); linarith
          omega
    have hblk_bound : ∀ k ∈ range (K + 1),
        ∑ l ∈ Blk k, minK X (α * ((m : ℝ) - (l : ℝ))) ≤ 3 * X + (q : ℝ) * Real.log (q : ℝ) := by
      intro k _
      set S : Finset ℤ := (Blk k).image (fun l : ℕ => (m : ℤ) - (l : ℤ))
      have hinj : Set.InjOn (fun l : ℕ => (m : ℤ) - (l : ℤ)) (Blk k) := by
        intro l₁ _ l₂ _ h; dsimp at h; omega
      have hsum_eq : ∑ l ∈ Blk k, minK X (α * ((m : ℝ) - (l : ℝ))) =
          ∑ z ∈ S, minK X (α * (z : ℝ)) := by
        symm; dsimp [S]
        rw [Finset.sum_image (f := fun z : ℤ => minK X (α * (z : ℝ)))
          (g := fun l : ℕ => (m : ℤ) - (l : ℤ)) (fun x hx y hy h => hinj hx hy h)]
        refine Finset.sum_congr rfl fun l _ => by push_cast; rfl
      set n₀ : ℤ := (m : ℤ) - ((A + (k + 1) * q - 1 : ℕ) : ℤ)
      have hS_range : ∀ z ∈ S, n₀ ≤ z ∧ z < n₀ + (q : ℤ) := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
        simp only [Blk, mem_Icc] at hl
        have hmul : (k + 1) * q = k * q + q := by ring
        have hle2 : l ≤ A + (k + 1) * q - 1 := le_trans hl.2 (Nat.min_le_right _ _)
        have hpos1 : 1 ≤ (k + 1) * q := by nlinarith
        dsimp [n₀]; constructor <;> omega
      rw [hsum_eq]
      exact block_minK_bound α a q hD hq15 X hX n₀ S hS_range
    have hK_le : ((K + 1 : ℕ) : ℝ) ≤ Y / (q : ℝ) + 1 := by
      have hKmul : K * q ≤ B - A := Nat.div_mul_le_self _ _
      have hBY : (B : ℝ) ≤ Y := Nat.floor_le hY
      have hKmul' : (K : ℝ) * (q : ℝ) ≤ (B : ℝ) := by
        have : K * q ≤ B := by omega
        exact_mod_cast this
      have hKq : (K : ℝ) ≤ Y / (q : ℝ) := by
        rw [le_div_iff₀ hqpos]; linarith
      push_cast; linarith
    calc ∑ l ∈ LL_Decomp1543a.lRange N U Y, LL_Decomp1543a.minK X (α * ((m : ℝ) - (l : ℝ)))
        ≤ ∑ l ∈ Icc A B, minK X (α * ((m : ℝ) - (l : ℝ))) := hle_Icc
      _ = ∑ k ∈ range (K + 1), ∑ l ∈ Blk k, minK X (α * ((m : ℝ) - (l : ℝ))) := by
          rw [← hbi, Finset.sum_biUnion hdisj]
      _ ≤ ∑ _k ∈ range (K + 1), (3 * X + (q : ℝ) * Real.log (q : ℝ)) :=
          Finset.sum_le_sum hblk_bound
      _ = ((K + 1 : ℕ) : ℝ) * (3 * X + (q : ℝ) * Real.log (q : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (Y / (q : ℝ) + 1) * (3 * X + (q : ℝ) * Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hK_le (by positivity)

/-! ### Part 4: Mod-36 squarefree count bound on `tBlock N M` (`≤ 0.67 * M`) -/

private lemma abs_moebius_le_ind36 (t : ℕ) :
    |(moebius t : ℝ)| ≤ if ¬ (4 ∣ t) ∧ ¬ (9 ∣ t) then 1 else 0 := by
  split_ifs with h
  · by_cases hsq : Squarefree t
    · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
      simp
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp
  · have hnsq : ¬ Squarefree t := by
      intro hsq
      have hnot4 : ¬ (4 ∣ t) := by
        intro h4
        have h22 : 2 * 2 ∣ t := by simpa using h4
        have hu := hsq 2 h22
        exact (by decide : ¬ IsUnit (2 : ℕ)) hu
      have hnot9 : ¬ (9 ∣ t) := by
        intro h9
        have h33 : 3 * 3 ∣ t := by simpa using h9
        have hu := hsq 3 h33
        exact (by decide : ¬ IsUnit (3 : ℕ)) hu
      exact h ⟨hnot4, hnot9⟩
    have hm0 : moebius t = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    rw [hm0]; simp

private lemma card_mod36_block (a : ℕ) :
    ((Icc a (a + 35)).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card ≤ 24 := by
  set S36 := (Finset.range 36).filter (fun r => ¬ (4 ∣ r) ∧ ¬ (9 ∣ r))
  have hS36_card : S36.card = 24 := by decide
  have hinj : Set.InjOn (fun t : ℕ => t % 36)
      ((Icc a (a + 35)).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))) := by
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_coe, mem_filter, mem_Icc] at ht₁ ht₂
    dsimp at heq
    omega
  have himg : ((Icc a (a + 35)).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).image (fun t => t % 36) ⊆ S36 := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨t, ht, rfl⟩
    simp only [mem_filter, mem_Icc, S36, mem_range] at ht ⊢
    refine ⟨Nat.mod_lt t (by norm_num), ?_, ?_⟩
    · intro h4; exact ht.2.1 (by omega)
    · intro h9; exact ht.2.2 (by omega)
  calc ((Icc a (a + 35)).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card
      = (((Icc a (a + 35)).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).image (fun t => t % 36)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ S36.card := Finset.card_le_card himg
    _ = 24 := hS36_card

private lemma squarefree_tBlock_bound (N : ℕ) (M : ℝ) (hM : 100000 ≤ M) :
    ∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)| ≤ 0.67 * M := by
  set A := ⌊M⌋₊ + 1
  set B := ⌊2 * M⌋₊
  have hsub : LL_Decomp1543a.tBlock N M ⊆ Icc A B := by
    intro t ht
    simp only [LL_Decomp1543a.tBlock, mem_filter, mem_Icc] at ht ⊢
    exact ⟨(Nat.floor_lt (by linarith)).mpr ht.2.1, Nat.le_floor ht.2.2⟩
  have h1 : ∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)| ≤
      (((Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card : ℝ) := by
    calc ∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)|
        ≤ ∑ t ∈ Icc A B, |(moebius t : ℝ)| :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ t ∈ Icc A B, (if ¬ (4 ∣ t) ∧ ¬ (9 ∣ t) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun t _ => abs_moebius_le_ind36 t)
      _ = (((Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card : ℝ) := by
          rw [← Finset.sum_filter]; simp
  set K := (B - A) / 36
  have hcover : (Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t)) ⊆
      (range (K + 1)).biUnion (fun k => (Icc (A + 36 * k) (A + 36 * k + 35)).filter
        (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))) := by
    intro t ht
    simp only [mem_filter, mem_Icc, mem_biUnion, mem_range] at ht ⊢
    refine ⟨(t - A) / 36, ?_, ?_, ht.2⟩
    · have : (t - A) / 36 ≤ (B - A) / 36 := Nat.div_le_div_right (by omega)
      omega
    · omega
  have hcard : ((Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card ≤ (K + 1) * 24 := by
    calc ((Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card
        ≤ ((range (K + 1)).biUnion (fun k => (Icc (A + 36 * k) (A + 36 * k + 35)).filter
            (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t)))).card := Finset.card_le_card hcover
      _ ≤ ∑ k ∈ range (K + 1), ((Icc (A + 36 * k) (A + 36 * k + 35)).filter
            (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ range (K + 1), 24 := Finset.sum_le_sum (fun k _ => card_mod36_block (A + 36 * k))
      _ = (K + 1) * 24 := by simp
  have hcard_r : (((Icc A B).filter (fun t => ¬ (4 ∣ t) ∧ ¬ (9 ∣ t))).card : ℝ) ≤
      ((K + 1 : ℕ) : ℝ) * 24 := by exact_mod_cast hcard
  have hK_le : ((K : ℕ) : ℝ) * 36 ≤ M := by
    have hKmul : K * 36 ≤ B - A := Nat.div_mul_le_self _ _
    have hB_le : (B : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
    have hA_gt : M < (A : ℝ) := by
      dsimp [A]; push_cast; exact Nat.lt_floor_add_one M
    have hBA : (B - A : ℕ) ≤ M := by
      by_cases h : A ≤ B
      · have : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub h
        linarith
      · have : B - A = 0 := by omega
        rw [this]; simp; linarith
    have hKmul_r : (K : ℝ) * 36 ≤ ((B - A : ℕ) : ℝ) := by exact_mod_cast hKmul
    linarith
  have hfinal : ((K + 1 : ℕ) : ℝ) * 24 ≤ 0.67 * M := by
    push_cast; linarith
  linarith

/-! ### Part 5: Abel summation + Schoenfeld bound on `∑ am(U, m)^2` -/

private lemma psi_nat_sub (r : ℕ) (hr : 1 ≤ r) :
    (vonMangoldt r : ℝ) = Chebyshev.psi (r : ℝ) - Chebyshev.psi ((r - 1 : ℕ) : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast]
  have hsplit : Icc 0 r = insert r (Icc 0 (r - 1)) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [hsplit, sum_insert (by simp only [mem_Icc]; omega)]
  ring

private lemma abel_sum_psi (A B : ℕ) (hAB : A + 1 ≤ B) (hA : 1 ≤ A) :
    ∑ r ∈ Icc (A + 1) B, (vonMangoldt r : ℝ) / (r : ℝ) =
      Chebyshev.psi (B : ℝ) / (B : ℝ) - Chebyshev.psi (A : ℝ) / ((A + 1 : ℕ) : ℝ) +
        ∑ r ∈ Icc (A + 1) (B - 1), Chebyshev.psi (r : ℝ) * (1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
    have h1 : Icc (A + 1) (A + 1) = {A + 1} := by ext x; simp only [mem_Icc, mem_singleton]; omega
    have h2 : Icc (A + 1) (A + 1 - 1) = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
    rw [h1, h2, sum_singleton, sum_empty, psi_nat_sub (A + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    ring
  | succ k hk ih =>
    have hsplit1 : Icc (A + 1) (k + 1) = insert (k + 1) (Icc (A + 1) k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hsplit2 : Icc (A + 1) (k + 1 - 1) = insert k (Icc (A + 1) (k - 1)) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit1, sum_insert (by simp only [mem_Icc]; omega), ih,
        hsplit2, sum_insert (by simp only [mem_Icc]; omega),
        psi_nat_sub (k + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

private lemma harmonic_tail_le_log (A B : ℕ) (hA : 1 ≤ A) (hAB : A + 1 ≤ B) :
    ∑ r ∈ Icc (A + 1) (B - 1), (1 : ℝ) / ((r + 1 : ℕ) : ℝ) ≤
      Real.log ((B : ℝ) / ((A + 1 : ℕ) : ℝ)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
    have h1 : Icc (A + 1) (A + 1 - 1) = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
    rw [h1, sum_empty, div_self (by positivity), Real.log_one]
  | succ k hk ih =>
    have hsplit : Icc (A + 1) (k + 1 - 1) = insert k (Icc (A + 1) (k - 1)) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp only [mem_Icc]; omega)]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hA1_pos : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)] at hlog
      have hcalc : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -(1 / ((k + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      rw [hcalc] at hlog; linarith
    rw [Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hA1_pos)]
    rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hA1_pos)] at ih
    linarith

private lemma am_sq_sum_bound (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ))
    (X : ℝ) (hX_pos : 0 < X) (hX_le : X ≤ (N : ℝ) / Vf N) :
    ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m ^ 2 ≤
      0.122 * X * Real.log (N : ℝ) ^ 2 := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hU9 := Uf_ge_10pow9 N hL
  have hUpos : 0 < Uf N := by linarith
  by_cases hXU : X ≤ Uf N
  · have hemp : LL_Decomp1543a.lRange N (Uf N) X = ∅ := by
      ext m; simp only [LL_Decomp1543a.lRange, mem_filter, mem_Icc, notMem_empty, iff_false]
      intro h; linarith [h.2.1, h.2.2]
    rw [hemp, sum_empty]; positivity
  · push Not at hXU
    -- Step 1: am(U, m) <= 0.6 * L for all m in lRange N U X
    have ham_le : ∀ m ∈ LL_Decomp1543a.lRange N (Uf N) X,
        0 ≤ LL_Decomp1543a.am (Uf N) m ∧ LL_Decomp1543a.am (Uf N) m ≤ 0.6 * Real.log (N : ℝ) := by
      intro m hm
      simp only [LL_Decomp1543a.lRange, mem_filter, mem_Icc] at hm
      constructor
      · unfold LL_Decomp1543a.am
        exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      · unfold LL_Decomp1543a.am
        calc ∑ r ∈ m.divisors.filter (fun r : ℕ => Uf N < (r : ℝ)), (vonMangoldt r : ℝ)
            ≤ ∑ r ∈ m.divisors, (vonMangoldt r : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
          _ = Real.log (m : ℝ) := ArithmeticFunction.vonMangoldt_sum
          _ ≤ Real.log X := Real.log_le_log (by exact_mod_cast hm.1.1) hm.2.2
          _ ≤ Real.log ((N : ℝ) / Vf N) := Real.log_le_log hX_pos hX_le
          _ ≤ 0.6 * Real.log (N : ℝ) := log_N_div_Vf_le N hL
    have hsq_le : ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m ^ 2 ≤
        (0.6 * Real.log (N : ℝ)) * ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m hm => ?_
      have ⟨hnn, hle⟩ := ham_le m hm
      nlinarith
    -- Step 2: Swap sum to get <= X * sum_{r in Icc (A+1) B} Lambda(r) / r
    set A := ⌊Uf N⌋₊
    set B := ⌊X⌋₊
    have hswap : ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m ≤
        X * ∑ r ∈ Icc (A + 1) B, (vonMangoldt r : ℝ) / (r : ℝ) := by
      have hsub_m : LL_Decomp1543a.lRange N (Uf N) X ⊆ Icc 1 B := by
        intro m hm; simp only [LL_Decomp1543a.lRange, mem_filter, mem_Icc] at hm ⊢
        exact ⟨hm.1.1, Nat.le_floor hm.2.2⟩
      have h1 : ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m ≤
          ∑ m ∈ Icc 1 B, ∑ r ∈ Icc (A + 1) B, if r ∣ m then (vonMangoldt r : ℝ) else 0 := by
        calc ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m
            ≤ ∑ m ∈ Icc 1 B, LL_Decomp1543a.am (Uf N) m :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_m
                (fun m _ _ => Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))
          _ ≤ ∑ m ∈ Icc 1 B, ∑ r ∈ Icc (A + 1) B, if r ∣ m then (vonMangoldt r : ℝ) else 0 := by
              refine Finset.sum_le_sum fun m hm => ?_
              simp only [mem_Icc] at hm
              unfold LL_Decomp1543a.am
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
              intro r hr
              simp only [mem_filter, Nat.mem_divisors, mem_Icc] at hr ⊢
              refine ⟨⟨(Nat.floor_lt (le_of_lt hUpos)).mpr hr.2,
                le_trans (Nat.le_of_dvd (by omega) hr.1.1) hm.2⟩, hr.1.1⟩
      rw [Finset.sum_comm] at h1
      have h2 : ∑ r ∈ Icc (A + 1) B, ∑ m ∈ Icc 1 B, (if r ∣ m then (vonMangoldt r : ℝ) else 0) ≤
          X * ∑ r ∈ Icc (A + 1) B, (vonMangoldt r : ℝ) / (r : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        simp only [mem_Icc] at hr
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcard_div : ((Icc 1 B).filter (fun m => r ∣ m)).card ≤ B / r := by
          have hinj : Set.InjOn (fun m => m / r) ((Icc 1 B).filter (fun m => r ∣ m)) := by
            intro m₁ hm₁ m₂ hm₂ heq
            simp only [Finset.mem_coe, mem_filter, mem_Icc] at hm₁ hm₂
            dsimp at heq
            have h1' := Nat.div_mul_cancel hm₁.2
            have h2' := Nat.div_mul_cancel hm₂.2
            rw [← h1', ← h2', heq]
          have himg : ((Icc 1 B).filter (fun m => r ∣ m)).image (fun m => m / r) ⊆ Icc 1 (B / r) := by
            intro k hk
            rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
            simp only [mem_filter, mem_Icc] at hm ⊢
            constructor
            · rcases hm.2 with ⟨c, hc⟩
              have hc1 : 1 ≤ c := by nlinarith
              have : m / r = c := by rw [hc]; exact Nat.mul_div_cancel_left c (by omega)
              omega
            · exact Nat.div_le_div_right hm.1.2
          calc ((Icc 1 B).filter (fun m => r ∣ m)).card
              = (((Icc 1 B).filter (fun m => r ∣ m)).image (fun m => m / r)).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ (Icc 1 (B / r)).card := Finset.card_le_card himg
            _ = B / r := by simp
        have hcard_r : (((Icc 1 B).filter (fun m => r ∣ m)).card : ℝ) ≤ X / (r : ℝ) := by
          have h1' : (((Icc 1 B).filter (fun m => r ∣ m)).card : ℝ) ≤ (B / r : ℕ) := by
            exact_mod_cast hcard_div
          have h2' : ((B / r : ℕ) : ℝ) * (r : ℝ) ≤ (B : ℝ) := by
            exact_mod_cast Nat.div_mul_le_self B r
          have h3' : (B : ℝ) ≤ X := Nat.floor_le (le_of_lt hX_pos)
          have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
          have h4' : ((B / r : ℕ) : ℝ) ≤ X / (r : ℝ) := by rw [le_div_iff₀ hrpos]; linarith
          linarith
        calc (((Icc 1 B).filter (fun m => r ∣ m)).card : ℝ) * (vonMangoldt r : ℝ)
            ≤ (X / (r : ℝ)) * (vonMangoldt r : ℝ) :=
              mul_le_mul_of_nonneg_right hcard_r ArithmeticFunction.vonMangoldt_nonneg
          _ = X * ((vonMangoldt r : ℝ) / (r : ℝ)) := by ring
      linarith
    -- Step 3: Bound sum_{r=A+1}^B Lambda(r) / r <= 0.203 * L
    have hsum_r_le : ∑ r ∈ Icc (A + 1) B, (vonMangoldt r : ℝ) / (r : ℝ) ≤ 0.203 * Real.log (N : ℝ) := by
      by_cases hAB : B < A + 1
      · have hemp : Icc (A + 1) B = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
        rw [hemp, sum_empty]; positivity
      · push Not at hAB
        have hA_ge : (10 : ℝ) ^ 8 ≤ (A : ℝ) := by
          have : Uf N - 1 < (A : ℝ) := by linarith [Nat.lt_floor_add_one (Uf N)]
          linarith
        have hA_nat : 1 ≤ A := by
          have : (1 : ℝ) ≤ (A : ℝ) := by linarith
          exact_mod_cast this
        have hlogA : 10 ≤ Real.log (A : ℝ) := by
          have h10e : Real.exp 10 ≤ (10 : ℝ) ^ 8 := by
            have : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
            rw [this]
            calc (Real.exp 1) ^ 10 ≤ (2.72 : ℝ) ^ 10 := by gcongr; exact le_of_lt exp_one_lt_272
              _ ≤ (10 : ℝ) ^ 8 := by norm_num
          have := Real.log_le_log (Real.exp_pos _) (le_trans h10e hA_ge)
          rwa [Real.log_exp] at this
        have hpsi_upper : ∀ r : ℕ, A ≤ r → Chebyshev.psi (r : ℝ) ≤ 1.0025 * (r : ℝ) := by
          intro r hr
          have hr_ge : (10 : ℝ) ^ 8 ≤ (r : ℝ) := le_trans hA_ge (by exact_mod_cast hr)
          have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
          have hlogr : 10 ≤ Real.log (r : ℝ) := le_trans hlogA (Real.log_le_log (by linarith) (by exact_mod_cast hr))
          have hsch := TaoFivePrimes.schoenfeld_psi_excess_upper_large (r : ℝ) hr_ge
          have herr : (r : ℝ) / (40 * Real.log (r : ℝ)) ≤ 0.0025 * (r : ℝ) := by
            have h40 : (400 : ℝ) ≤ 40 * Real.log (r : ℝ) := by linarith
            have := div_le_div_of_nonneg_left (le_of_lt hr_pos) (by norm_num) h40
            linarith
          linarith
        have hpsi_A_lower : 0.997 * ((A + 1 : ℕ) : ℝ) ≤ Chebyshev.psi (A : ℝ) := by
          have hA_pos : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
          have hsch := TaoFivePrimes.schoenfeld_psi_deficit_lower_large (A : ℝ) hA_ge
          have herr : (A : ℝ) / (40 * Real.log (A : ℝ)) ≤ 0.0025 * (A : ℝ) := by
            have h40 : (400 : ℝ) ≤ 40 * Real.log (A : ℝ) := by linarith
            have := div_le_div_of_nonneg_left hA_pos (by norm_num) h40
            linarith
          have hA104 : (10000 : ℝ) ≤ (A : ℝ) := by linarith [show (10000 : ℝ) ≤ (10 : ℝ) ^ 8 by norm_num]
          push_cast; linarith
        rw [abel_sum_psi A B hAB hA_nat]
        have hB_pos : (0 : ℝ) < (B : ℝ) := by
          have : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show A ≤ B by omega)
          linarith
        have htermB : Chebyshev.psi (B : ℝ) / (B : ℝ) ≤ 1.0025 := by
          rw [div_le_iff₀ hB_pos]
          exact hpsi_upper B (by omega)
        have htermA : 0.997 ≤ Chebyshev.psi (A : ℝ) / ((A + 1 : ℕ) : ℝ) := by
          rw [le_div_iff₀ (by positivity)]
          exact hpsi_A_lower
        have hsum_mid : ∑ r ∈ Icc (A + 1) (B - 1),
            Chebyshev.psi (r : ℝ) * (1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ)) ≤
            1.0025 * ∑ r ∈ Icc (A + 1) (B - 1), (1 : ℝ) / ((r + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun r hr => ?_
          simp only [mem_Icc] at hr
          have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
          have hr1_pos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
          have hdiff_eq : (1 : ℝ) / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ) =
              1 / ((r : ℝ) * ((r + 1 : ℕ) : ℝ)) := by
            push_cast; field_simp; ring
          rw [hdiff_eq]
          have hup := hpsi_upper r (by omega)
          calc Chebyshev.psi (r : ℝ) * (1 / ((r : ℝ) * ((r + 1 : ℕ) : ℝ)))
              ≤ (1.0025 * (r : ℝ)) * (1 / ((r : ℝ) * ((r + 1 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_right hup (by positivity)
            _ = 1.0025 * (1 / ((r + 1 : ℕ) : ℝ)) := by field_simp
        have hharm := harmonic_tail_le_log A B hA_nat hAB
        have hBA_le : (B : ℝ) / ((A + 1 : ℕ) : ℝ) ≤ (N : ℝ) / (Uf N * Vf N) := by
          have hB_le : (B : ℝ) ≤ X := Nat.floor_le (le_of_lt hX_pos)
          have hU_lt : Uf N < ((A + 1 : ℕ) : ℝ) := by
            dsimp [A]; push_cast; exact Nat.lt_floor_add_one (Uf N)
          have hVpos : 0 < Vf N := by linarith [Vf_ge_10pow9 N hL]
          calc (B : ℝ) / ((A + 1 : ℕ) : ℝ)
              ≤ X / Uf N := by
                apply div_le_div₀ (le_of_lt hX_pos) hB_le hUpos (le_of_lt hU_lt)
            _ ≤ ((N : ℝ) / Vf N) / Uf N := div_le_div_of_nonneg_right hX_le (le_of_lt hUpos)
            _ = (N : ℝ) / (Uf N * Vf N) := by rw [div_div, mul_comm]
        have hlog_BA : Real.log ((B : ℝ) / ((A + 1 : ℕ) : ℝ)) ≤ 0.2018 * Real.log (N : ℝ) :=
          le_trans (Real.log_le_log (by positivity) hBA_le) (log_N_div_UV_le N hL)
        linarith
    calc ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m ^ 2
        ≤ (0.6 * Real.log (N : ℝ)) * ∑ m ∈ LL_Decomp1543a.lRange N (Uf N) X, LL_Decomp1543a.am (Uf N) m := hsq_le
      _ ≤ (0.6 * Real.log (N : ℝ)) * (X * ∑ r ∈ Icc (A + 1) B, (vonMangoldt r : ℝ) / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hswap (by positivity)
      _ ≤ (0.6 * Real.log (N : ℝ)) * (X * (0.203 * Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_r_le (le_of_lt hX_pos)) (by positivity)
      _ = 0.1218 * X * Real.log (N : ℝ) ^ 2 := by ring
      _ ≤ 0.122 * X * Real.log (N : ℝ) ^ 2 := by
          have : 0 ≤ X * Real.log (N : ℝ) ^ 2 := by positivity
          nlinarith

/-! ### Part 6: `S4` bound via `LL_Decomp1543a` dyadic Cauchy-Schwarz -/

private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

private lemma block_sqrt_split (N q M L : ℝ) (hN : 0 < N) (hq : 0 < q) (hM : 0 < M) (hL : 0 < L) :
    √((0.67 * M) * ((0.122 * (N / M) * L ^ 2) *
      ((N / (M * q) + 1) * (3.001 * M + q * L)))) ≤
      0.496 * (N / √q * L) +
      0.286 * (N * L ^ ((3 : ℝ) / 2) * (1 / √M)) +
      0.496 * (√N * L * √M) +
      0.286 * (√N * √q * L ^ ((3 : ℝ) / 2)) := by
  have hprod_eq : (0.67 * M) * ((0.122 * (N / M) * L ^ 2) *
      ((N / (M * q) + 1) * (3.001 * M + q * L))) =
      (0.67 * 0.122 * 3.001) * (N ^ 2 / q * L ^ 2) +
      (0.67 * 0.122) * (N ^ 2 * L ^ 3 / M) +
      (0.67 * 0.122 * 3.001) * (N * L ^ 2 * M) +
      (0.67 * 0.122) * (N * q * L ^ 3) := by
    field_simp; ring
  rw [hprod_eq]
  have h1 := sqrt_add_le
    ((0.67 * 0.122 * 3.001) * (N ^ 2 / q * L ^ 2) + (0.67 * 0.122) * (N ^ 2 * L ^ 3 / M) +
      (0.67 * 0.122 * 3.001) * (N * L ^ 2 * M))
    ((0.67 * 0.122) * (N * q * L ^ 3)) (by positivity) (by positivity)
  have h2 := sqrt_add_le
    ((0.67 * 0.122 * 3.001) * (N ^ 2 / q * L ^ 2) + (0.67 * 0.122) * (N ^ 2 * L ^ 3 / M))
    ((0.67 * 0.122 * 3.001) * (N * L ^ 2 * M)) (by positivity) (by positivity)
  have h3 := sqrt_add_le
    ((0.67 * 0.122 * 3.001) * (N ^ 2 / q * L ^ 2))
    ((0.67 * 0.122) * (N ^ 2 * L ^ 3 / M)) (by positivity) (by positivity)
  have hL32_sq : (L ^ ((3 : ℝ) / 2)) ^ 2 = L ^ 3 := by
    rw [← Real.rpow_natCast (L ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul (le_of_lt hL)]
    have : ((3 : ℝ) / 2) * (2 : ℕ) = (3 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
  have hA1 : √((0.67 * 0.122 * 3.001) * (N ^ 2 / q * L ^ 2)) ≤ 0.496 * (N / √q * L) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (le_of_lt hq)]
    have : 0 ≤ N ^ 2 / q * L ^ 2 := by positivity
    nlinarith
  have hA2 : √((0.67 * 0.122) * (N ^ 2 * L ^ 3 / M)) ≤
      0.286 * (N * L ^ ((3 : ℝ) / 2) * (1 / √M)) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, mul_pow, div_pow, one_pow, Real.sq_sqrt (le_of_lt hM), hL32_sq]
    have : 0 ≤ N ^ 2 * L ^ 3 / M := by positivity
    have heq : (0.286 : ℝ) ^ 2 * (N ^ 2 * L ^ 3 * (1 / M)) =
        (0.286 : ℝ) ^ 2 * (N ^ 2 * L ^ 3 / M) := by ring
    rw [heq]; nlinarith
  have hA3 : √((0.67 * 0.122 * 3.001) * (N * L ^ 2 * M)) ≤ 0.496 * (√N * L * √M) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hN), Real.sq_sqrt (le_of_lt hM)]
    have : 0 ≤ N * L ^ 2 * M := by positivity
    nlinarith
  have hA4 : √((0.67 * 0.122) * (N * q * L ^ 3)) ≤ 0.286 * (√N * √q * L ^ ((3 : ℝ) / 2)) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hN), Real.sq_sqrt (le_of_lt hq), hL32_sq]
    have : 0 ≤ N * q * L ^ 3 := by positivity
    nlinarith
  linarith

private lemma pow_identity_2a (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * y ^ ((3 : ℝ) / 2) * (1 / √(x ^ ((2 : ℝ) / 5) * y ^ ((1 : ℝ) / 5))) =
      x ^ ((4 : ℝ) / 5) * y ^ (1.4 : ℝ) := by
  have hsqrt : √(x ^ ((2 : ℝ) / 5) * y ^ ((1 : ℝ) / 5)) =
      x ^ ((1 : ℝ) / 5) * y ^ ((1 : ℝ) / 10) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (le_of_lt hx), ← Real.rpow_mul (le_of_lt hy)]
    norm_num
  rw [hsqrt]
  have hx1 : x = x ^ ((4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_add hx]; norm_num
  have hy1 : y ^ ((3 : ℝ) / 2) = y ^ (1.4 : ℝ) * y ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_add hy]; norm_num
  have hx15 : x ^ ((1 : ℝ) / 5) ≠ 0 := ne_of_gt (by positivity)
  have hy110 : y ^ ((1 : ℝ) / 10) ≠ 0 := ne_of_gt (by positivity)
  calc x * y ^ ((3 : ℝ) / 2) * (1 / (x ^ ((1 : ℝ) / 5) * y ^ ((1 : ℝ) / 10)))
      = (x ^ ((4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5)) * (y ^ (1.4 : ℝ) * y ^ ((1 : ℝ) / 10)) *
          (1 / (x ^ ((1 : ℝ) / 5) * y ^ ((1 : ℝ) / 10))) := by rw [← hx1, ← hy1]
    _ = x ^ ((4 : ℝ) / 5) * y ^ (1.4 : ℝ) := by field_simp

private lemma pow_identity_2b (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    √x * y * √(x / (x ^ ((2 : ℝ) / 5) * y ^ (-(4 : ℝ) / 5))) =
      x ^ ((4 : ℝ) / 5) * y ^ (1.4 : ℝ) := by
  have hdiv : x / (x ^ ((2 : ℝ) / 5) * y ^ (-(4 : ℝ) / 5)) =
      x ^ ((3 : ℝ) / 5) * y ^ ((4 : ℝ) / 5) := by
    have hx1 : x = x ^ ((3 : ℝ) / 5) * x ^ ((2 : ℝ) / 5) := by
      rw [← Real.rpow_add hx]; norm_num
    have hy1 : y ^ (-(4 : ℝ) / 5) = (y ^ ((4 : ℝ) / 5))⁻¹ := by
      rw [show -(4 : ℝ) / 5 = -((4 : ℝ) / 5) by ring, Real.rpow_neg (le_of_lt hy)]
    have hx25 : x ^ ((2 : ℝ) / 5) ≠ 0 := ne_of_gt (by positivity)
    have hy45 : y ^ ((4 : ℝ) / 5) ≠ 0 := ne_of_gt (by positivity)
    calc x / (x ^ ((2 : ℝ) / 5) * y ^ (-(4 : ℝ) / 5))
        = (x ^ ((3 : ℝ) / 5) * x ^ ((2 : ℝ) / 5)) / (x ^ ((2 : ℝ) / 5) * (y ^ ((4 : ℝ) / 5))⁻¹) := by
          rw [← hx1, ← hy1]
      _ = x ^ ((3 : ℝ) / 5) * y ^ ((4 : ℝ) / 5) := by field_simp
  rw [hdiv, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx), ← Real.rpow_mul (le_of_lt hy)]
  have hxcomb : x ^ ((1 : ℝ) / 2) * x ^ (((3 : ℝ) / 5) * ((1 : ℝ) / 2)) = x ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_add hx]; norm_num
  have hycomb : y * y ^ (((4 : ℝ) / 5) * ((1 : ℝ) / 2)) = y ^ (1.4 : ℝ) := by
    calc y * y ^ (((4 : ℝ) / 5) * ((1 : ℝ) / 2))
        = y ^ (1 : ℝ) * y ^ (((4 : ℝ) / 5) * ((1 : ℝ) / 2)) := by rw [Real.rpow_one]
      _ = y ^ (1 + ((4 : ℝ) / 5) * ((1 : ℝ) / 2)) := (Real.rpow_add hy _ _).symm
      _ = y ^ (1.4 : ℝ) := by norm_num
  calc x ^ ((1 : ℝ) / 2) * y * (x ^ (((3 : ℝ) / 5) * ((1 : ℝ) / 2)) *
          y ^ (((4 : ℝ) / 5) * ((1 : ℝ) / 2)))
      = (x ^ ((1 : ℝ) / 2) * x ^ (((3 : ℝ) / 5) * ((1 : ℝ) / 2))) *
          (y * y ^ (((4 : ℝ) / 5) * ((1 : ℝ) / 2))) := by ring
    _ = x ^ ((4 : ℝ) / 5) * y ^ (1.4 : ℝ) := by rw [hxcomb, hycomb]

private lemma pow_identity_3 (y : ℝ) (hy : 0 < y) :
    y * y ^ ((3 : ℝ) / 2) = y ^ (2.5 : ℝ) := by
  calc y * y ^ ((3 : ℝ) / 2)
      = y ^ (1 : ℝ) * y ^ ((3 : ℝ) / 2) := by rw [Real.rpow_one]
    _ = y ^ (1 + (3 : ℝ) / 2) := (Real.rpow_add hy _ _).symm
    _ = y ^ (2.5 : ℝ) := by norm_num

private lemma S4_bound (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log (N : ℝ)) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log (N : ℝ) ^ 4 < (q : ℝ))
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ 5) :
    ‖LL_Decomp1543a.Ssum (LL_Decomp1543a.lam4 (Uf N) (Vf N)) c N α‖ ≤
      0.2387 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        2.8199 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
          0.0889 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hU9 := Uf_ge_10pow9 N hL
  have hV9 := Vf_ge_10pow9 N hL
  have hUpos : 0 < Uf N := by linarith
  have hVpos : 0 < Vf N := by linarith
  have hq15 : 15 ≤ q := q_ge_15_of_hq1 N hL q hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := log_q_le_log_N N hL q (by omega) hq2
  have hUV_le_N := Uf_mul_Vf_le_N N hL
  set L := Real.log (N : ℝ)
  set U := Uf N
  set V := Vf N
  set J := LL_Decomp1543a.Jn N U V
  have hJprops := LL_Decomp1543a.J_props N U V hUpos hVpos hUV_le_N
  have hJ_ge1 : 1 ≤ J := by unfold J LL_Decomp1543a.Jn; omega
  have hJ_le : (J : ℝ) ≤ 0.292 * L := by
    have hlog2 : (0.693 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h1 : (J : ℝ) ≤ 1 + Real.log ((N : ℝ) / (U * V)) / Real.log 2 := hJprops.2
    have h2 : Real.log ((N : ℝ) / (U * V)) ≤ 0.2018 * L := log_N_div_UV_le N hL
    have hdiv : Real.log ((N : ℝ) / (U * V)) / Real.log 2 ≤ (0.2018 / 0.693) * L := by
      have hnn : 0 ≤ Real.log ((N : ℝ) / (U * V)) := by
        apply Real.log_nonneg; rw [one_le_div (mul_pos hUpos hVpos)]; exact hUV_le_N
      have := div_le_div₀ (by positivity) h2 (by norm_num) (le_of_lt hlog2)
      rwa [mul_div_right_comm] at this
    linarith
  -- Step 1: S4_dyadic + triangle inequality
  rw [LL_Decomp1543a.S4_dyadic c N U V α hUpos hVpos]
  have htri : ‖∑ j ∈ range J, LL_Decomp1543a.block c N U (2 ^ j * V) α‖ ≤
      ∑ j ∈ range J, ‖LL_Decomp1543a.block c N U (2 ^ j * V) α‖ := norm_sum_le _ _
  -- Step 2: Per-block bound
  have hblock_le : ∀ j ∈ range J,
      ‖LL_Decomp1543a.block c N U (2 ^ j * V) α‖ ≤
        0.496 * ((N : ℝ) / √(q : ℝ) * L) +
        0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2) * (1 / √(2 ^ j * V))) +
        0.496 * (√(N : ℝ) * L * √(2 ^ j * V)) +
        0.286 * (√(N : ℝ) * √(q : ℝ) * L ^ ((3 : ℝ) / 2)) := by
    intro j _
    set M := (2 : ℝ) ^ j * V
    have h2j_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hM_ge_V : V ≤ M := by dsimp [M]; nlinarith
    have hM_ge_109 : (10 : ℝ) ^ 9 ≤ M := le_trans hV9 hM_ge_V
    have hM_pos : 0 < M := by linarith
    have hcauchy : ‖LL_Decomp1543a.block c N U M α‖ ≤
        √(∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)|) *
          √(∑ t ∈ LL_Decomp1543a.tBlock N M, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2) := by
      unfold LL_Decomp1543a.block
      exact LL_Decomp1543a.block_cauchy _ _
    have hsqf : ∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)| ≤ 0.67 * M :=
      squarefree_tBlock_bound N M (by linarith)
    have hexp := LL_Decomp1543a.square_expand c N U M α (le_of_lt hUpos) (by linarith)
      (fun θ A B hA hB => LL_Decomp1543a.geom_dyadic θ M (le_of_lt hM_pos) A B hA hB)
    have hNM_le : (N : ℝ) / M ≤ (N : ℝ) / V :=
      div_le_div_of_nonneg_left (le_of_lt hNpos) hVpos hM_ge_V
    have hinner_m : ∀ m ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M),
        ∑ l ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M),
          LL_Decomp1543a.minK (M + 1 / 2) (α * ((m : ℝ) - (l : ℝ))) ≤
          ((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L) := by
      intro m _
      have h1 := inner_l_sum_sharp α a q hD hq15 N U ((N : ℝ) / M) (M + 1 / 2)
        (le_of_lt hUpos) (by positivity) (by linarith) m
      have h2 : ((N : ℝ) / M) / (q : ℝ) = (N : ℝ) / (M * (q : ℝ)) := by rw [div_div]
      rw [h2] at h1
      have h3 : 3 * (M + 1 / 2) + (q : ℝ) * Real.log (q : ℝ) ≤ 3.001 * M + (q : ℝ) * L := by
        have : (q : ℝ) * Real.log (q : ℝ) ≤ (q : ℝ) * L :=
          mul_le_mul_of_nonneg_left hlogq_le (le_of_lt hqpos)
        linarith
      exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (by positivity))
    have ham_sq := am_sq_sum_bound N hL ((N : ℝ) / M) (by positivity) hNM_le
    have hsec_bound : ∑ t ∈ LL_Decomp1543a.tBlock N M, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2 ≤
        (0.122 * ((N : ℝ) / M) * L ^ 2) *
          (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)) := by
      calc ∑ t ∈ LL_Decomp1543a.tBlock N M, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2
          ≤ ∑ m ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M),
              LL_Decomp1543a.am U m ^ 2 *
                ∑ l ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M),
                  LL_Decomp1543a.minK (M + 1 / 2) (α * ((m : ℝ) - (l : ℝ))) := hexp
        _ ≤ ∑ m ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M),
              LL_Decomp1543a.am U m ^ 2 *
                (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)) := by
            refine Finset.sum_le_sum fun m hm =>
              mul_le_mul_of_nonneg_left (hinner_m m hm) (sq_nonneg _)
        _ = (∑ m ∈ LL_Decomp1543a.lRange N U ((N : ℝ) / M), LL_Decomp1543a.am U m ^ 2) *
              (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)) := by
            rw [← Finset.sum_mul]
        _ ≤ (0.122 * ((N : ℝ) / M) * L ^ 2) *
              (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)) :=
            mul_le_mul_of_nonneg_right ham_sq (by positivity)
    have hprod_le : ‖LL_Decomp1543a.block c N U M α‖ ≤
        √((0.67 * M) * ((0.122 * ((N : ℝ) / M) * L ^ 2) *
          (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)))) := by
      calc ‖LL_Decomp1543a.block c N U M α‖
          ≤ √(∑ t ∈ LL_Decomp1543a.tBlock N M, |(moebius t : ℝ)|) *
              √(∑ t ∈ LL_Decomp1543a.tBlock N M, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2) := hcauchy
        _ ≤ √(0.67 * M) * √((0.122 * ((N : ℝ) / M) * L ^ 2) *
              (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L))) :=
            mul_le_mul (Real.sqrt_le_sqrt hsqf) (Real.sqrt_le_sqrt hsec_bound)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = √((0.67 * M) * ((0.122 * ((N : ℝ) / M) * L ^ 2) *
              (((N : ℝ) / (M * (q : ℝ)) + 1) * (3.001 * M + (q : ℝ) * L)))) :=
            (Real.sqrt_mul (by positivity) _).symm
    exact le_trans hprod_le (block_sqrt_split (N : ℝ) (q : ℝ) M L hNpos hqpos hM_pos hLpos)
  -- Step 3: Sum the 4 terms over j ∈ range J
  have hsum4 : ∑ j ∈ range J, ‖LL_Decomp1543a.block c N U (2 ^ j * V) α‖ ≤
      (J : ℝ) * (0.496 * ((N : ℝ) / √(q : ℝ) * L)) +
      0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * (∑ j ∈ range J, 1 / √(2 ^ j * V)) +
      0.496 * (√(N : ℝ) * L) * (∑ j ∈ range J, √(2 ^ j * V)) +
      (J : ℝ) * (0.286 * (√(N : ℝ) * √(q : ℝ) * L ^ ((3 : ℝ) / 2))) := by
    have hle := Finset.sum_le_sum hblock_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have h2 : ∑ j ∈ range J, 0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2) * (1 / √(2 ^ j * V))) =
        0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * ∑ j ∈ range J, 1 / √(2 ^ j * V) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have h3 : ∑ j ∈ range J, 0.496 * (√(N : ℝ) * L * √(2 ^ j * V)) =
        0.496 * (√(N : ℝ) * L) * ∑ j ∈ range J, √(2 ^ j * V) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    linarith
  -- Step 4: Apply dyadic sum bounds and power identities
  have hinv := LL_Decomp1543a.dyadic_invsqrt_sum V hVpos J
  have hsqrt := LL_Decomp1543a.dyadic_sqrt_sum N U V hUpos hVpos J hJ_ge1 hJprops.1
  have hsqrt2 : (2 : ℝ) + √2 ≤ 3.415 := by
    have : √2 ≤ (1.415 : ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  have hpow2a : (N : ℝ) * L ^ ((3 : ℝ) / 2) * (1 / √V) =
      (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) :=
    pow_identity_2a (N : ℝ) L hNpos hLpos
  have hpow2b : √(N : ℝ) * L * √((N : ℝ) / U) =
      (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) :=
    pow_identity_2b (N : ℝ) L hNpos hLpos
  have hpow3 : L * L ^ ((3 : ℝ) / 2) = L ^ (2.5 : ℝ) :=
    pow_identity_3 L hLpos
  have hT1 : (J : ℝ) * (0.496 * ((N : ℝ) / √(q : ℝ) * L)) ≤
      0.2387 * (N : ℝ) / √(q : ℝ) * L ^ 2 := by
    calc (J : ℝ) * (0.496 * ((N : ℝ) / √(q : ℝ) * L))
        ≤ (0.292 * L) * (0.496 * ((N : ℝ) / √(q : ℝ) * L)) :=
          mul_le_mul_of_nonneg_right hJ_le (by positivity)
      _ = (0.292 * 0.496) * ((N : ℝ) / √(q : ℝ) * L ^ 2) := by ring
      _ ≤ 0.2387 * ((N : ℝ) / √(q : ℝ) * L ^ 2) := by
          have : 0 ≤ (N : ℝ) / √(q : ℝ) * L ^ 2 := by positivity
          nlinarith
      _ = 0.2387 * (N : ℝ) / √(q : ℝ) * L ^ 2 := by ring
  have hT2a : 0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * (∑ j ∈ range J, 1 / √(2 ^ j * V)) ≤
      (0.286 * 3.415) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) := by
    calc 0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * (∑ j ∈ range J, 1 / √(2 ^ j * V))
        ≤ 0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * ((2 + √2) / √V) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (0.286 * (2 + √2)) * ((N : ℝ) * L ^ ((3 : ℝ) / 2) * (1 / √V)) := by ring
      _ = (0.286 * (2 + √2)) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) := by rw [hpow2a]
      _ ≤ (0.286 * 3.415) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hT2b : 0.496 * (√(N : ℝ) * L) * (∑ j ∈ range J, √(2 ^ j * V)) ≤
      (0.496 * 3.415) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) := by
    calc 0.496 * (√(N : ℝ) * L) * (∑ j ∈ range J, √(2 ^ j * V))
        ≤ 0.496 * (√(N : ℝ) * L) * ((2 + √2) * √((N : ℝ) / U)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (0.496 * (2 + √2)) * (√(N : ℝ) * L * √((N : ℝ) / U)) := by ring
      _ = (0.496 * (2 + √2)) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) := by rw [hpow2b]
      _ ≤ (0.496 * 3.415) * ((N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hT2 : 0.286 * ((N : ℝ) * L ^ ((3 : ℝ) / 2)) * (∑ j ∈ range J, 1 / √(2 ^ j * V)) +
      0.496 * (√(N : ℝ) * L) * (∑ j ∈ range J, √(2 ^ j * V)) ≤
      2.8199 * (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) := by
    have : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) := by positivity
    nlinarith
  have hT3 : (J : ℝ) * (0.286 * (√(N : ℝ) * √(q : ℝ) * L ^ ((3 : ℝ) / 2))) ≤
      0.0889 * √(N : ℝ) * √(q : ℝ) * L ^ (2.5 : ℝ) := by
    calc (J : ℝ) * (0.286 * (√(N : ℝ) * √(q : ℝ) * L ^ ((3 : ℝ) / 2)))
        ≤ (0.292 * L) * (0.286 * (√(N : ℝ) * √(q : ℝ) * L ^ ((3 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_right hJ_le (by positivity)
      _ = (0.292 * 0.286) * (√(N : ℝ) * √(q : ℝ) * (L * L ^ ((3 : ℝ) / 2))) := by ring
      _ = (0.292 * 0.286) * (√(N : ℝ) * √(q : ℝ) * L ^ (2.5 : ℝ)) := by rw [hpow3]
      _ ≤ 0.0889 * (√(N : ℝ) * √(q : ℝ) * L ^ (2.5 : ℝ)) := by
          have : 0 ≤ √(N : ℝ) * √(q : ℝ) * L ^ (2.5 : ℝ) := by positivity
          nlinarith
      _ = 0.0889 * √(N : ℝ) * √(q : ℝ) * L ^ (2.5 : ℝ) := by ring
  linarith

/-! ### Part 7: Assembly of `prop61_large` -/

theorem solution (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  have hNpos := N_pos_of_hL N hL
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hU1 : 1 ≤ Uf N := by linarith [Uf_ge_10pow9 N hL]
  have hV1 : 1 ≤ Vf N := by linarith [Vf_ge_10pow9 N hL]
  have hUV1 : 1 ≤ Uf N * Vf N := by nlinarith
  have hq15 : 15 ≤ q := q_ge_15_of_hq1 N hL q hq1
  have hsplit : Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
      Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
        Ssum (lam3 (Uf N) (Vf N)) c N α +
        LL_Decomp1543a.Ssum (LL_Decomp1543a.lam4 (Uf N) (Vf N)) c N α := by
    rw [Ssum_eq_a, Ssum_eq_a, Ssum_eq_a, Ssum_eq_a, lam1_eq_a, lam2_eq_a, lam3_eq_a]
    exact LL_Decomp1543a.S_split c N (Uf N) (Vf N) α hV1
  have htri : ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤
      ‖Ssum (lam1 (Uf N)) c N α‖ + ‖Ssum (lam2 (Vf N)) c N α‖ +
        ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ +
        ‖LL_Decomp1543a.Ssum (LL_Decomp1543a.lam4 (Uf N) (Vf N)) c N α‖ := by
    rw [hsplit]
    have h1 := norm_add_le (Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
        Ssum (lam3 (Uf N) (Vf N)) c N α)
      (LL_Decomp1543a.Ssum (LL_Decomp1543a.lam4 (Uf N) (Vf N)) c N α)
    have h2 := norm_add_le (Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α)
      (Ssum (lam3 (Uf N) (Vf N)) c N α)
    have h3 := norm_add_le (Ssum (lam1 (Uf N)) c N α) (Ssum (lam2 (Vf N)) c N α)
    linarith
  -- Bound S1
  have hS1 : ‖Ssum (lam1 (Uf N)) c N α‖ ≤
      0.38 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) :=
    le_trans (LL_Decomp1543c.lemma62_S1 c N hL α) (LL_Decomp1543c.S1_absorb N hL)
  -- Bound S2
  have hS2 : ‖Ssum (lam2 (Vf N)) c N α‖ ≤
      0.0282 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.0006 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ) := by
    have h1 := LL_Decomp1543c.S2_le c hc N (Vf N) α
    have h2 := LL_Decomp1543c.wc_lemma3 α a q hD hq15 (Vf N) (N : ℝ) hV1 hNpos
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hLpos)
    have h65a := LL_Decomp1543c.n65a N hL q hq1 hq2
    have h65b := LL_Decomp1543c.n65b N hL q hq1 hq2
    have h65c := LL_Decomp1543c.n65c N hL q hq1 hq2
    have hexpand : Real.log (N : ℝ) *
        (5 * (q : ℝ) + 1.5 * (q : ℝ) * Real.log (q : ℝ) +
          Vf N * Real.log (q : ℝ) + 5 * (N : ℝ) / (q : ℝ) * Real.log (Vf N)) =
        (5 * (q : ℝ) + 1.5 * (q : ℝ) * Real.log (q : ℝ)) * Real.log (N : ℝ) +
        Vf N * Real.log (q : ℝ) * Real.log (N : ℝ) +
        5 * (N : ℝ) / (q : ℝ) * Real.log (Vf N) * Real.log (N : ℝ) := by ring
    linarith
  -- Bound S3
  have hS3 : ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ ≤
      0.0131 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.0005 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ) := by
    have h1 := LL_Decomp1543c.S3_le c hc N (Uf N) (Vf N) α hU1 hV1
    have h2 := LL_Decomp1543c.wc_lemma3 α a q hD hq15 (Uf N * Vf N) (N : ℝ) hUV1 hNpos
    have hlogUV_nn : 0 ≤ Real.log (Uf N * Vf N) := Real.log_nonneg hUV1
    have h3 := mul_le_mul_of_nonneg_left h2 hlogUV_nn
    have h66a := LL_Decomp1543c.n66a N hL q hq1 hq2
    have h66b := LL_Decomp1543c.n66b N hL q hq1 hq2
    have h66c := LL_Decomp1543c.n66c N hL q hq1 hq2
    have hexpand : Real.log (Uf N * Vf N) *
        (5 * (q : ℝ) + 1.5 * (q : ℝ) * Real.log (q : ℝ) +
          Uf N * Vf N * Real.log (q : ℝ) + 5 * (N : ℝ) / (q : ℝ) * Real.log (Uf N * Vf N)) =
        (5 * (q : ℝ) + 1.5 * (q : ℝ) * Real.log (q : ℝ)) * Real.log (Uf N * Vf N) +
        Uf N * Vf N * Real.log (q : ℝ) * Real.log (Uf N * Vf N) +
        5 * (N : ℝ) / (q : ℝ) * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) := by ring
    linarith
  -- Bound S4
  have hS4 := S4_bound c N hL α a q hD hq1 hq2
  have hsum_rhs :
      0.38 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
      (0.0282 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.0006 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ)) +
      (0.0131 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.0005 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ)) +
      (0.2387 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        2.8199 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.0889 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ)) =
      0.28 * (N : ℝ) / √(q : ℝ) * Real.log (N : ℝ) ^ 2 +
        4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log (N : ℝ) ^ (1.4 : ℝ) +
        0.09 * √(N : ℝ) * √(q : ℝ) * Real.log (N : ℝ) ^ (2.5 : ℝ) := by ring
  linarith

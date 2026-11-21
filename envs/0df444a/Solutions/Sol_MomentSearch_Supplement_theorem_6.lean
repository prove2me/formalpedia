-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:53:03.290438+00:00
-- url     : https://prove2.me/submissions/175dd65c-3010-4d1d-a138-f7f16cbf96bc

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection

import Theorems.Thm_MomentSearch_Supplement_sparse_sketch_hard_fibre
import Theorems.Thm_MomentSearch_Supplement_sparse_support_opt_upper_bound

open scoped ENNReal
open MomentSearch MomentSearch.Supplement

theorem solution :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ (X : Type) (σ : (Fin n → ℝ) → X) (k : ℕ),
            (k : ℝ) ≤ 1 / 2 * (n : ℝ) ^ ε * Real.logb 2 n →
            (σ '' stdSimplex ℝ (Fin n)).Finite →
            (σ '' stdSimplex ℝ (Fin n)).ncard ≤ 2 ^ k →
            ENNReal.ofReal (γ / ε) ≤ approxFactor (sketchCollection σ) := by
  classical
  refine ⟨1/12, by norm_num, ?_⟩
  intro ε hε _hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)^(1/ε))
  refine ⟨max 2 N, ?_⟩
  intro n hn X σ k hk hfin hcard
  have hn2 : 2 ≤ n := le_trans (le_max_left ..) hn
  have hNr : (N:ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right 2 N) hn)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have logN := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) (hN.le.trans hNr)
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<2),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at logN
  have scale : 1 ≤ ε * Real.logb 2 n := by
    have e := (div_le_iff₀ hε).mp logN
    linarith
  let q := ⌈(n:ℝ)^ε⌉₊
  have lo : (n:ℝ)^ε ≤ q := Nat.le_ceil _
  have pos : 0 < q := by
    exact_mod_cast (lt_of_lt_of_le (Real.rpow_pos_of_pos hn' ε) lo)
  have logpos : 0 < Real.logb 2 n := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (by omega : 1 < n)
  have one : 1 ≤ (n:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1≤n)) hε.le
  have qbound : (q:ℝ) ≤ 2*(n:ℝ)^ε := by
    have e := Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^ε from zero_le_one.trans one)
    change (q:ℝ) < _ at e
    linarith
  have logq := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num)
    (by exact_mod_cast pos : 0 < (q:ℝ)) qbound
  rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hn' ε).ne',
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), Real.logb_rpow_eq_mul_logb_of_pos hn'] at logq
  have budget : (k:ℝ) ≤ (q:ℝ)/2*Real.logb 2 n :=
    hk.trans (by nlinarith [mul_le_mul_of_nonneg_right lo logpos.le])
  obtain ⟨x,hx,hard⟩ := sparse_sketch_hard_fibre hn2 pos X σ budget hfin hcard
  let U := {p : Fin n → ℝ | p ∈ stdSimplex ℝ (Fin n) ∧ σ p = x}
  obtain ⟨p₀,hp₀,he⟩ := hx
  have hU : U ∈ sketchCollection σ := ⟨⟨p₀,hp₀,he⟩,x,rfl⟩
  unfold approxFactor
  apply le_iSup_of_le U
  apply le_iSup_of_le hU
  apply le_iInf
  intro T
  obtain ⟨p,hp,hx',hs,hcost⟩ := hard T
  apply le_iSup_of_le p
  apply le_iSup_of_le (show p ∈ U from ⟨hp,hx'⟩)
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨hopt,hupper⟩ := sparse_support_opt_upper_bound hn2 pos p hp hs
  have upper : OPT p ≤ 3*(ε*Real.logb 2 n) := by linarith
  apply (le_div_iff₀ hopt).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hε).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcost hε.le]

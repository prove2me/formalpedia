-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fc85bd2b-c9eb-55cf-a44e-9eb9fb9576cd

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
import Theorems.Thm_UnramifiedWhittaker_summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self

set_option autoImplicit false

noncomputable section

namespace RS11G1

open UnramifiedWhittaker Complex Finset

abbrev t (a b : ℂ) : ℕ → ℂ := heckeRecursionSeq 1 a b

theorem t_zero (a b : ℂ) : t a b 0 = 1 := by simp [t, heckeRecursionSeq]
theorem t_one (a b : ℂ) : t a b 1 = a := by simp [t, heckeRecursionSeq]
theorem t_succ_succ (a b : ℂ) (m : ℕ) : t a b (m + 2) = a * t a b (m + 1) - b * t a b m := by
  simp [t, heckeRecursionSeq]

theorem t_conj (a b : ℂ) : ∀ m : ℕ, t ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) m = (starRingEnd ℂ) (t a b m) := by
  have key : ∀ m : ℕ, t ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) m = (starRingEnd ℂ) (t a b m) ∧
      t ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) (m + 1) = (starRingEnd ℂ) (t a b (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨by simp [t_zero], by simp [t_one]⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [t_succ_succ, t_succ_succ, ih.1, ih.2, map_sub, map_mul, map_mul]
  exact fun m => (key m).1

theorem norm_t_le (a b : ℂ) : ∀ m : ℕ, ‖t a b m‖ ≤ (‖a‖ + ‖b‖ + 1) ^ m := by
  set C : ℝ := ‖a‖ + ‖b‖ + 1 with hC
  have hC1 : 1 ≤ C := by rw [hC]; linarith [norm_nonneg a, norm_nonneg b]
  have key : ∀ m : ℕ, ‖t a b m‖ ≤ C ^ m ∧ ‖t a b (m + 1)‖ ≤ C ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp [t_zero], ?_⟩
      rw [t_one, pow_one, hC]; linarith [norm_nonneg b]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [t_succ_succ]
      calc ‖a * t a b (m + 1) - b * t a b m‖ ≤ ‖a * t a b (m + 1)‖ + ‖b * t a b m‖ := norm_sub_le _ _
        _ = ‖a‖ * ‖t a b (m + 1)‖ + ‖b‖ * ‖t a b m‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖a‖ * C ^ (m + 1) + ‖b‖ * C ^ (m + 1) := by
            have h1 : ‖t a b m‖ ≤ C ^ (m + 1) :=
              ih.1.trans (pow_le_pow_right₀ hC1 (Nat.le_succ m))
            gcongr
            · exact ih.2
        _ = (‖a‖ + ‖b‖) * C ^ (m + 1) := by ring
        _ ≤ C * C ^ (m + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hC]; linarith
        _ = C ^ (m + 1 + 1) := by ring
  exact fun m => (key m).1

def w (b : ℂ) (j : ℕ) : ℝ := if Even j then ‖b‖ ^ j else 0

theorem w_nonneg (b : ℂ) (j : ℕ) : 0 ≤ w b j := by
  unfold w; split_ifs <;> positivity

theorem w_le (b : ℂ) (j : ℕ) : w b j ≤ ‖b‖ ^ j := by
  unfold w; split_ifs <;> [exact le_rfl; positivity]

def e (a b : ℂ) (n : ℕ) : ℝ := ∑ ij ∈ antidiagonal n, ‖t a b ij.1‖ ^ 2 * w b ij.2

theorem e_zero (a b : ℂ) : e a b 0 = 1 := by
  simp [e, w, t_zero]

theorem e_one (a b : ℂ) : e a b 1 = ‖a‖ ^ 2 := by
  rw [e, Nat.antidiagonal_succ, sum_cons, sum_map]
  simp [w, t_zero, t_one]

theorem e_nonneg (a b : ℂ) (n : ℕ) : 0 ≤ e a b n :=
  sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (w_nonneg b _)

theorem e_le (a b : ℂ) (n : ℕ) : e a b n ≤ (2 * (‖a‖ + ‖b‖ + 1)) ^ (2 * n) := by
  set C : ℝ := ‖a‖ + ‖b‖ + 1 with hC
  have hC1 : 1 ≤ C := by rw [hC]; linarith [norm_nonneg a, norm_nonneg b]
  have hbC : ‖b‖ ≤ C := by rw [hC]; linarith [norm_nonneg a]
  have hterm : ∀ ij ∈ antidiagonal n, ‖t a b ij.1‖ ^ 2 * w b ij.2 ≤ C ^ (2 * n) := by
    intro ij hij
    rw [mem_antidiagonal] at hij
    calc ‖t a b ij.1‖ ^ 2 * w b ij.2 ≤ (C ^ ij.1) ^ 2 * ‖b‖ ^ ij.2 := by
          apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_t_le a b ij.1) 2) (w_le b _)
            (w_nonneg b _) (by positivity)
      _ ≤ (C ^ ij.1) ^ 2 * C ^ ij.2 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hbC _) (by positivity)
      _ = C ^ (2 * ij.1 + ij.2) := by ring
      _ ≤ C ^ (2 * n) := pow_le_pow_right₀ hC1 (by omega)
  calc e a b n ≤ ∑ _ij ∈ antidiagonal n, C ^ (2 * n) := sum_le_sum hterm
    _ = (n + 1) * C ^ (2 * n) := by rw [sum_const, Nat.card_antidiagonal]; simp
    _ ≤ 2 ^ (2 * n) * C ^ (2 * n) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (n : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
        calc (n : ℝ) + 1 ≤ 2 ^ n := this
          _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = (2 * C) ^ (2 * n) := by rw [mul_pow]

theorem hasSum_even_geometric {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => if Even j then z ^ j else 0) (1 - z ^ 2)⁻¹ := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by norm_num)
  have h := hasSum_geometric_of_norm_lt_one hz2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun x y hxy => by simpa using hxy
  have hout : ∀ j : ℕ, j ∉ Set.range (fun k : ℕ => 2 * k) → (fun j : ℕ => if Even j then z ^ j else 0) j = 0 := by
    intro j hj
    have : ¬ Even j := fun ⟨k, hk⟩ => hj ⟨k, by show 2 * k = j; omega⟩
    simp [this]
  refine (hinj.hasSum_iff hout).mp ?_
  have hfun : ((fun j : ℕ => if Even j then z ^ j else 0) ∘ fun k : ℕ => 2 * k) = fun k => (z ^ 2) ^ k := by
    funext k
    simp only [Function.comp_apply, even_two_mul, ↓reduceIte, pow_mul]
  rw [hfun]
  exact h

theorem main (a b : ℂ) :
    ∃ e : ℕ → ℝ, e 0 = 1 ∧ e 1 = ‖a‖ ^ 2 ∧ (∀ n : ℕ, 0 ≤ e n) ∧
      (∀ n : ℕ, e n ≤ (2 * (‖a‖ + ‖b‖ + 1)) ^ (2 * n)) ∧
      ∀ y : ℂ, ‖y‖ * (‖a‖ + ‖b‖ + 1) ^ 2 < 1 →
        HasSum (fun n : ℕ => (e n : ℂ) * y ^ n)
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y)⁻¹ := by
  refine ⟨e a b, e_zero a b, e_one a b, e_nonneg a b, e_le a b, ?_⟩
  intro y hy
  set C : ℝ := ‖a‖ + ‖b‖ + 1 with hC
  have hC1 : 1 ≤ C := by rw [hC]; linarith [norm_nonneg a, norm_nonneg b]
  have hbC : ‖b‖ ≤ C := by rw [hC]; linarith [norm_nonneg a]
  have hyC : ‖y‖ * C ^ 2 < 1 := hy
  have hy1 : ‖y‖ * C < 1 := by
    calc ‖y‖ * C ≤ ‖y‖ * C ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg y); nlinarith
      _ < 1 := hyC

  set u : ℕ → ℂ := heckeRecursionSeq 1 ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) with hu
  set u' : ℕ → ℂ := heckeRecursionSeq 1 a b with hu'
  have huu' : ∀ m, u m * u' m = ((‖t a b m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    rw [hu, hu', show heckeRecursionSeq 1 ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) m =
      (starRingEnd ℂ) (t a b m) from t_conj a b m, Complex.conj_mul']
    norm_cast
  have hy' : ‖y‖ * (max 1 (‖(starRingEnd ℂ) a‖ + ‖(1 : ℂ) * (starRingEnd ℂ) b‖)) *
      (max 1 (‖a‖ + ‖(1 : ℂ) * b‖)) < ‖(1 : ℂ)‖ ^ 2 := by
    have hmax : max 1 (‖a‖ + ‖b‖) ≤ C := max_le hC1 (by rw [hC]; linarith)
    have hm0 : 0 ≤ max 1 (‖a‖ + ‖b‖) := le_trans zero_le_one (le_max_left _ _)
    simp only [one_mul, Complex.norm_conj, norm_one, one_pow]
    calc ‖y‖ * max 1 (‖a‖ + ‖b‖) * max 1 (‖a‖ + ‖b‖) ≤ ‖y‖ * C * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hmax (norm_nonneg y)) hmax hm0 (by positivity)
      _ = ‖y‖ * C ^ 2 := by ring
      _ < 1 := hyC
  have hsumF : Summable fun m : ℕ => u m * u' m * y ^ m :=
    UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow 1 _ _ _ _ one_ne_zero y hy'
  have hprodF := UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
    1 ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b one_ne_zero y hsumF
  simp only [one_mul, one_pow, div_one] at hprodF

  set F : ℕ → ℂ := fun m => ((‖t a b m‖ ^ 2 : ℝ) : ℂ) * y ^ m with hF
  have hFeq : (fun m : ℕ => u m * u' m * y ^ m) = F := by funext m; rw [hF, huu']
  rw [hFeq] at hsumF hprodF

  set z : ℂ := ((‖b‖ : ℝ) : ℂ) * y with hz
  have hz1 : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg b), mul_comm]
    calc ‖y‖ * ‖b‖ ≤ ‖y‖ * C := mul_le_mul_of_nonneg_left hbC (norm_nonneg y)
      _ < 1 := hy1
  set G : ℕ → ℂ := fun j => ((w b j : ℝ) : ℂ) * y ^ j with hG
  have hGeq : G = fun j : ℕ => if Even j then z ^ j else 0 := by
    funext j
    simp only [hG, w, hz]
    split_ifs with hj
    · push_cast; ring
    · simp
  have hsumG : HasSum G (1 - z ^ 2)⁻¹ := by rw [hGeq]; exact hasSum_even_geometric hz1

  have hFn : Summable fun m => ‖F m‖ := summable_norm_iff.mpr hsumF
  have hGn : Summable fun j => ‖G j‖ := summable_norm_iff.mpr hsumG.summable

  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn
  have hcauchy_summable : Summable fun n : ℕ => ∑ ij ∈ antidiagonal n, F ij.1 * G ij.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hFn hGn).of_norm
  have hterm : (fun n : ℕ => ∑ ij ∈ antidiagonal n, F ij.1 * G ij.2) = fun n => ((e a b n : ℝ) : ℂ) * y ^ n := by
    funext n
    rw [e, Complex.ofReal_sum, sum_mul]
    refine sum_congr rfl fun ij hij => ?_
    rw [mem_antidiagonal] at hij
    simp only [hF, hG]
    push_cast
    rw [← hij, pow_add]; ring

  have hz2 : (starRingEnd ℂ) b * b * y ^ 2 = z ^ 2 := by
    rw [hz, Complex.conj_mul']; ring
  rw [hz2] at hprodF
  have hne : 1 - z ^ 2 ≠ 0 := by
    intro h0
    have : ‖z ^ 2‖ = 1 := by rw [← sub_eq_zero.mp h0]; simp
    rw [norm_pow] at this
    have := pow_lt_one₀ (norm_nonneg z) hz1 (two_ne_zero)
    linarith
  have hPne : (LanglandsTunnell.RankinSelberg.rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hprodF; exact hne hprodF.symm
  have hFne : (∑' m, F m) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprodF; exact hne hprodF.symm
  have hval : ((LanglandsTunnell.RankinSelberg.rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y)⁻¹ =
      (∑' m, F m) * (∑' j, G j) := by
    rw [hsumG.tsum_eq, ← hprodF, mul_inv_rev, ← mul_assoc, mul_comm (∑' m, F m), mul_assoc,
      mul_inv_cancel₀ hFne, mul_one]
  rw [hval, hcauchy, hterm]
  rw [hterm] at hcauchy_summable
  exact hcauchy_summable.hasSum

end RS11G1

open LanglandsTunnell.RankinSelberg in

theorem solution
    (a b : ℂ) :
    ∃ e : ℕ → ℝ, e 0 = 1 ∧ e 1 = ‖a‖ ^ 2 ∧ (∀ n : ℕ, 0 ≤ e n) ∧
      (∀ n : ℕ, e n ≤ (2 * (‖a‖ + ‖b‖ + 1)) ^ (2 * n)) ∧
      ∀ y : ℂ, ‖y‖ * (‖a‖ + ‖b‖ + 1) ^ 2 < 1 →
        HasSum (fun n : ℕ => (e n : ℂ) * y ^ n)
          ((rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y)⁻¹ :=
  RS11G1.main a b

end
end S_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self (solution)

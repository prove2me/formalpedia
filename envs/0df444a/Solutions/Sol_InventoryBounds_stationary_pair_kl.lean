-- Prove2me | solution 1 for InventoryBounds.stationary_pair_kl
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:23.156337+00:00
-- url     : https://prove2.me/submissions/e925502e-b149-4464-a016-a471c9fe1ecd

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open InventoryBounds

namespace S214IBK

lemma kl_le (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKL p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  unfold binaryKL
  have h1 : Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((1 - p) / (1 - q)) ≤ (1 - p) / (1 - q) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have e : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) = (p - q) ^ 2 / (q * (1 - q)) := by
    have : (1 - q) ≠ 0 := by linarith
    field_simp
    ring
  calc _ ≤ p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) := by
        gcongr
    _ = _ := e

lemma one (t δ p q : ℝ) (ht : 8 ≤ t) (hδ : 0 < δ) (hδt : δ ≤ 1 / (8 * t))
    (hq : q = 1 - 1 / (2 * t) + δ ∨ q = 1 - 1 / (2 * t) - δ)
    (hp : p = 1 - 1 / (2 * t) + δ ∨ p = 1 - 1 / (2 * t) - δ) (hpq : (p - q) ^ 2 = 4 * δ ^ 2) :
    binaryKL p q ≤ 22 * t * δ ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hinv : 1 / t ≤ 1 / 8 := by rw [div_le_div_iff₀ ht0 (by norm_num)]; linarith
  have hδ' : δ * (8 * t) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hδt
  have hu : 1 / (2 * t) = (1 / t) / 2 := by field_simp
  have htinv : t * (1 / t) = 1 := by field_simp
  -- q ∈ [1 - 5/(8t), 1 - 3/(8t)]
  have hqlo : 3 / 8 * (1 / t) ≤ 1 - q := by
    rcases hq with rfl | rfl <;> rw [hu] <;> nlinarith
  have hqhi : 1 - q ≤ 5 / 8 * (1 / t) := by
    rcases hq with rfl | rfl <;> rw [hu] <;> nlinarith
  have hplo : 0 < 1 - p := by
    rcases hp with rfl | rfl <;> rw [hu] <;> nlinarith
  have hphi : 1 - p ≤ 5 / 8 * (1 / t) := by
    rcases hp with rfl | rfl <;> rw [hu] <;> nlinarith
  have hq0 : 0 < q := by nlinarith
  have hq1 : q < 1 := by nlinarith [show 0 < 1 / t by positivity]
  have hp0 : 0 < p := by nlinarith
  refine (kl_le p q hp0 (by linarith) hq0 hq1).trans ?_
  rw [hpq, div_le_iff₀ (by nlinarith)]
  -- 4 δ² ≤ 22 t δ² q (1-q): need 4 ≤ 22 t q (1-q)
  have hq59 : 59 / 64 ≤ q := by nlinarith
  have key : 4 ≤ 22 * t * (q * (1 - q)) := by
    have : 3 / 8 ≤ t * (1 - q) := by nlinarith
    nlinarith
  nlinarith [sq_nonneg δ, mul_le_mul_of_nonneg_left key (sq_nonneg δ)]

end S214IBK

theorem solution (T : ℕ) (hT : 8 ≤ T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ) / 1024) :
    max (binaryKL (rhoPlus T ε) (rhoMinus T ε))
      (binaryKL (rhoMinus T ε) (rhoPlus T ε)) ≤
      22 * (T : ℝ) * (128 * ε / (T : ℝ) ^ 2) ^ 2 := by
  have ht : (8 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  set δ := 128 * ε / (T : ℝ) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδt : δ ≤ 1 / (8 * (T : ℝ)) := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ε * 1024 ≤ T := by linarith [(le_div_iff₀ (by norm_num : (0:ℝ) < 1024)).mp hεT]
    nlinarith
  have hP : rhoPlus T ε = 1 - 1 / (2 * (T : ℝ)) + δ := rfl
  have hM : rhoMinus T ε = 1 - 1 / (2 * (T : ℝ)) - δ := rfl
  refine max_le ?_ ?_
  · exact S214IBK.one T δ _ _ ht hδ hδt (Or.inr hM) (Or.inl hP) (by rw [hP, hM]; ring)
  · exact S214IBK.one T δ _ _ ht hδ hδt (Or.inl hP) (Or.inr hM) (by rw [hP, hM]; ring)

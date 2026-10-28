-- Prove2me | solution 1 for HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:46:11.062493+00:00
-- url     : https://prove2.me/submissions/a1994ac5-2e73-40a1-85ab-6b01a6305448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_LpThreshold_hlawka_holds_below
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.LpThreshold

/-- The coordinate `p`-norm of an explicit three-term vector. -/
lemma lpNorm_vec3 (p a b c : ℝ) :
    lpNorm p (![a, b, c] : Fin 3 → ℝ) = (|a| ^ p + |b| ^ p + |c| ^ p) ^ (1 / p) := by
  simp [lpNorm, Fin.sum_univ_three]

/-- The three cyclic vectors all have norm `A_p(t)`. -/
lemma lpNorm_cyclicA_x {p t : ℝ} (ht0 : 0 ≤ t) :
    lpNorm p (![-t, 1, 1] : Fin 3 → ℝ) = cyclicA p t := by
  rw [lpNorm_vec3, cyclicA]
  congr 1
  simp only [abs_neg, abs_of_nonneg ht0, abs_one, Real.one_rpow]
  ring

lemma lpNorm_cyclicA_y {p t : ℝ} (ht0 : 0 ≤ t) :
    lpNorm p (![1, -t, 1] : Fin 3 → ℝ) = cyclicA p t := by
  rw [lpNorm_vec3, cyclicA]
  congr 1
  simp only [abs_neg, abs_of_nonneg ht0, abs_one, Real.one_rpow]
  ring

lemma lpNorm_cyclicA_z {p t : ℝ} (ht0 : 0 ≤ t) :
    lpNorm p (![1, 1, -t] : Fin 3 → ℝ) = cyclicA p t := by
  rw [lpNorm_vec3, cyclicA]
  congr 1
  simp only [abs_neg, abs_of_nonneg ht0, abs_one, Real.one_rpow]
  ring

/-- Every pairwise sum of two cyclic vectors has norm `B_p(t)`. -/
lemma lpNorm_cyclicB_xy {p t : ℝ} :
    lpNorm p (![-t + 1, 1 - t, 2] : Fin 3 → ℝ) = cyclicB p t := by
  rw [lpNorm_vec3, cyclicB]
  congr 1
  have h1 : (-t + 1 : ℝ) = 1 - t := by ring
  rw [h1, show |(2 : ℝ)| = 2 by norm_num]
  ring

lemma lpNorm_cyclicB_xz {p t : ℝ} :
    lpNorm p (![-t + 1, 2, 1 - t] : Fin 3 → ℝ) = cyclicB p t := by
  rw [lpNorm_vec3, cyclicB]
  congr 1
  have h1 : (-t + 1 : ℝ) = 1 - t := by ring
  rw [h1, show |(2 : ℝ)| = 2 by norm_num]
  ring

lemma lpNorm_cyclicB_yz {p t : ℝ} :
    lpNorm p (![2, -t + 1, 1 - t] : Fin 3 → ℝ) = cyclicB p t := by
  rw [lpNorm_vec3, cyclicB]
  congr 1
  have h1 : (-t + 1 : ℝ) = 1 - t := by ring
  rw [h1, show |(2 : ℝ)| = 2 by norm_num]
  ring

/-- The total sum of the three cyclic vectors has norm `3^{1/p}(2-t)`. -/
lemma lpNorm_cyclic_total {p t : ℝ} (hp0 : 0 < p) (ht2 : t ≤ 2) :
    lpNorm p (![2 - t, 2 - t, 2 - t] : Fin 3 → ℝ) = (3 : ℝ) ^ (1 / p) * (2 - t) := by
  have ht : (0 : ℝ) ≤ 2 - t := by linarith
  rw [lpNorm_vec3]
  rw [show |2 - t| = 2 - t by rw [abs_of_nonneg ht]]
  rw [show (2 - t) ^ p + (2 - t) ^ p + (2 - t) ^ p = 3 * (2 - t) ^ p by ring]
  rw [Real.mul_rpow (show (0 : ℝ) ≤ 3 by norm_num) (Real.rpow_nonneg ht p)]
  rw [← Real.rpow_mul ht p (1 / p)]
  rw [show p * (1 / p) = 1 by
    rw [mul_one_div, div_self (ne_of_gt hp0)]]
  rw [Real.rpow_one]

/-- If Hlawka's inequality holds with constant one for a triple whose seven norms are
the cyclic data, then the cyclic ratio at `t` is at most one. -/
lemma cyclicRatio_le_one {p t : ℝ} (hp : 1 < p) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (h : 3 * cyclicB p t ≤ 3 * cyclicA p t + (3 : ℝ) ^ (1 / p) * (2 - t)) :
    cyclicRatio p t ≤ 1 := by
  have hden : 0 < 6 * cyclicA p t - 3 * cyclicB p t := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, abs_of_nonneg (show (0 : ℝ) ≤ 2 - t by linarith)]
  rw [div_le_one hden]
  linarith

end HlawkaSchatten.LpThreshold

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.LpThreshold

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → cyclicConstant p ≤ 1 := by
  intro p hp2 hpT
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  refine csSup_le ⟨cyclicRatio p 2, 2, by norm_num, rfl⟩ ?_
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have ht2 : t ≤ 2 := ht.2
  -- the vector identities for the pairwise sums
  have hxyv : (![-t, 1, 1] + ![1, -t, 1] : Fin 3 → ℝ) = ![-t + 1, 1 - t, 2] := by
    funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  have hxzv : (![-t, 1, 1] + ![1, 1, -t] : Fin 3 → ℝ) = ![-t + 1, 2, 1 - t] := by
    funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  have hyzv : (![1, -t, 1] + ![1, 1, -t] : Fin 3 → ℝ) = ![2, -t + 1, 1 - t] := by
    funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  have htotv : (![-t, 1, 1] + ![1, -t, 1] + ![1, 1, -t] : Fin 3 → ℝ) = ![2 - t, 2 - t, 2 - t] := by
    funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring
  -- apply the Hlawka atom in dimension three
  have hH := hlawka_holds_below p hp2 hpT 3
    (![-t, 1, 1] : Fin 3 → ℝ) (![1, -t, 1] : Fin 3 → ℝ) (![1, 1, -t] : Fin 3 → ℝ)
  simp only [tripleGap, pairGapSum, pairGap] at hH
  rw [htotv, hxyv, hxzv, hyzv] at hH
  rw [lpNorm_cyclicA_x ht0, lpNorm_cyclicA_y ht0, lpNorm_cyclicA_z ht0,
    lpNorm_cyclicB_xy, lpNorm_cyclicB_xz, lpNorm_cyclicB_yz, lpNorm_cyclic_total hp0 ht2] at hH
  refine cyclicRatio_le_one hp1 ht0 ht2 ?_
  linarith

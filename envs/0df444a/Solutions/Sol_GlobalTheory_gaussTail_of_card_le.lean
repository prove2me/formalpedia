-- Prove2me | solution 1 for GlobalTheory.gaussTail_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:29.420805+00:00
-- url     : https://prove2.me/submissions/7ca3d7ff-fd21-42a2-938e-8ac59fef63c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_GaussTailOfCardLe
import Theorems.Thm_GlobalTheory_summable_exp_neg_of_card_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Ext.GaussianTailBound := by
  intro ι h g R0 hR0 hg hh hcard
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = R0 ^ 2 / 16 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have ht' : 2 * (g : ℝ) + 1 ≤ t := by rw [ht_def]; linarith

  have key := GlobalTheory.summable_exp_neg_of_card_le (fun i => h i ^ 2 / 16) (t := t) (C := 9 ^ g)
    (fun i => by
      have h1 := hh i
      have h2 : R0 ^ 2 ≤ h i ^ 2 := by nlinarith
      rw [ht_def]
      linarith)
    (fun s u htu hs => by
      have hu0 : 0 < u := lt_of_lt_of_le ht htu
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 4 * Real.sqrt u := ⟨_, rfl⟩
      have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
      have hR2 : R ^ 2 = 16 * u := by rw [hR, mul_pow, hsq]; norm_num
      have hRnn : 0 ≤ R := by rw [hR]; positivity

      have hle : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 16 * u → x ≤ R := fun x hx hx2 => by
        nlinarith
      have hR0R : R0 ≤ R := hle R0 hR0.le (by rw [ht_def] at htu; linarith)
      have hsS : ∀ i ∈ s, h i ≤ R := fun i hi => by
        have h3 := hs i hi
        exact hle (h i) (hR0.le.trans (hh i)) (by linarith)
      refine (hcard R hR0R s hsS).trans ?_
      have hpow : (3 * R / R0) ^ (2 * g) = 9 ^ g * (u / t) ^ g := by
        rw [pow_mul, ← mul_pow]
        congr 1
        rw [div_pow, mul_pow, hR2, ht_def]
        field_simp
        ring
      rw [hpow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)

      have hx : u / t ≤ Real.exp (u / t - 1) := by
        have := Real.add_one_le_exp (u / t - 1)
        linarith
      have hy : u - t = t * (u / t - 1) := by field_simp
      have hy0 : 0 ≤ u / t - 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      calc (u / t) ^ g ≤ Real.exp (u / t - 1) ^ g := by gcongr
        _ = Real.exp (g * (u / t - 1)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((u - t) / 2) := by
          apply Real.exp_le_exp.mpr
          rw [hy]
          nlinarith [mul_le_mul_of_nonneg_right ht' hy0])
  have e : ∀ i, -(h i) ^ 2 / 16 = -(h i ^ 2 / 16) := fun i => by ring
  simp only [e]
  refine ⟨key.1, key.2.trans_eq ?_⟩
  rw [ht_def, neg_div]
end GlobalTheory

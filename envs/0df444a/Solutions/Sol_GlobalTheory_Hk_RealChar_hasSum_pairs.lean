-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.hasSum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:28.223156+00:00
-- url     : https://prove2.me/submissions/7dea64b4-a69f-4105-9081-195ee26ad51c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_nonneg
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_le
import Theorems.Thm_GlobalTheory_Hk_RealChar_scale_integrable
import Theorems.Thm_GlobalTheory_Hk_RealChar_scale_integral
import Theorems.Thm_GlobalTheory_Hk_RealChar_summable_th

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    {v : ℝ} (hv : 0 < v) :
    HasSum (fun p : ℕ × ℕ => a p.1 * b p.2 * besW (v * p.1 * p.2))
      (∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w) := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have hD : 0 ≤ D := by simpa using (abs_nonneg _).trans (ha 1)
  set f : ℕ × ℕ → ℝ → ℝ := fun p w =>
    a p.1 * b p.2 * (Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w) with hf
  have hz : ∀ p : ℕ × ℕ, a p.1 * b p.2 = 0 ∨ (0 < p.1 ∧ 0 < p.2) := by
    rintro ⟨m, n⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left; simp [a0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [b0]
    exact Or.inr ⟨hm, hn⟩
  have hint : ∀ p, Integrable (f p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · exact (scale_integrable (y := v * p.1) (n := p.2) (by positivity) (by positivity)).const_mul _
  have hval : ∀ p, ∫ w in Set.Ioi (0 : ℝ), f p w = a p.1 * b p.2 * besW (v * p.1 * p.2) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · simp only [hf]
      rw [integral_const_mul, scale_integral (v * p.1) (n := p.2) (by positivity)]
  obtain ⟨G, hG0, hG⟩ := besW_le
  have hs2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum : Summable fun p => ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun w => norm_nonneg _) (fun p => ?_)
      ((hs2.mul_of_nonneg hs2 (fun n => by positivity) (fun n => by positivity)).mul_left
        (D * D * G / v ^ 3))
    rcases hz p with h | ⟨h1, h2⟩
    · simp only [hf, h, zero_mul, norm_zero, integral_zero]
      positivity
    · have e : ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ = |a p.1| * |b p.2| * besW (v * p.1 * p.2) := by
        rw [← scale_integral (v * p.1) (n := p.2) (by positivity), ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
        have : 0 < w := hw
        simp only [hf]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w)]
        rfl
      rw [e]
      have h1' : (0 : ℝ) < p.1 := by positivity
      have h2' : (0 : ℝ) < p.2 := by positivity
      calc |a p.1| * |b p.2| * besW (v * p.1 * p.2)
          ≤ (D * p.1) * (D * p.2) * (G / (v * p.1 * p.2) ^ 3) := by
            gcongr
            · exact besW_nonneg _
            · exact ha _
            · exact hb _
            · exact hG _ (by positivity)
        _ = _ := by field_simp
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [hval] at H
  suffices e : ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w
      = ∫ w in Set.Ioi (0 : ℝ), ∑' p, f p w by rw [e]; exact H
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw' : 0 < w := hw
  simp only [th]
  rw [tsum_mul_tsum_of_summable_norm (summable_th ha (by positivity)) (summable_th hb hw'),
    ← tsum_div_const]
  refine tsum_congr fun p => ?_
  simp only [hf]
  rw [show v / w * (p.1 : ℝ) = v * p.1 / w by ring]
  ring
end GlobalTheory.Hk.RealChar

-- Prove2me | solution 1 for GlobalTheory.Hk.tsum_exp_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:52:10.721864+00:00
-- url     : https://prove2.me/submissions/22b160f2-50d1-428a-ae45-803726c22220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_integral_mul_exp_neg_Ioi

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
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (c : ℕ → ℂ) (h0 : c 0 = 0) {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun n : ℕ => ‖c n‖ * Real.exp (-(t * n)))) :
    ∑' n : ℕ, c n * (Real.exp (-(t * n)) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n) * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) := by
  set φ : ℕ → ℝ → ℝ := fun n x => (Set.Ici (n : ℝ)).indicator (fun x => t * Real.exp (-(t * x))) x with hφ
  have hφi : ∀ n, Integrable (φ n) (volume.restrict (Set.Ioi (1 : ℝ))) := fun n =>
    (integral_mul_exp_neg_Ioi ht 1).1.indicator measurableSet_Ici
  have hφ0 : ∀ n x, 0 ≤ φ n x := fun n x =>
    Set.indicator_nonneg (fun y _ => by positivity) x
  have hφv : ∀ n : ℕ, n ≠ 0 → ∫ x in Set.Ioi (1 : ℝ), φ n x = Real.exp (-(t * n)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [hφ]
    simp only
    rw [setIntegral_indicator measurableSet_Ici, ← (integral_mul_exp_neg_Ioi ht n).2]
    apply setIntegral_congr_set
    have e1 : (Set.Ioi (1 : ℝ) : Set ℝ) =ᵐ[volume] Set.Ici 1 := Ioi_ae_eq_Ici
    have e2 : (Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) : Set ℝ) =ᵐ[volume] (Set.Ici 1 ∩ Set.Ici (n : ℝ) : Set ℝ) :=
      ae_eq_set_inter e1 (ae_eq_refl _)
    rw [Set.Ici_inter_Ici, sup_eq_right.2 hn1] at e2
    exact e2.trans Ioi_ae_eq_Ici.symm
  have hv : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), c n * (φ n x : ℂ) = c n * (Real.exp (-(t * n)) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · rw [integral_const_mul, integral_complex_ofReal, hφv n hn]
  have hn : ∀ n : ℕ, ∫ x in Set.Ioi (1 : ℝ), ‖c n * (φ n x : ℂ)‖ = ‖c n‖ * Real.exp (-(t * n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _ _)]
      rw [integral_const_mul, hφv n hn]
  have key := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (F := fun n x => c n * (φ n x : ℂ)) (fun n => ((hφi n).ofReal).const_mul _)
    (by simpa only [hn] using hs)
  simp only [hv] at key
  rw [key.tsum_eq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one (le_of_lt hx)
  simp only
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro n hn
    have : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 (Finset.mem_Icc.1 hn).2
    simp only [hφ]
    rw [Set.indicator_of_mem (show x ∈ Set.Ici (n : ℝ) from this)]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [h0]
    · have : ¬ (n : ℝ) ≤ x := by
        intro h
        exact hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, (Nat.le_floor_iff hx0).2 h⟩)
      simp only [hφ]
      rw [Set.indicator_of_notMem (show x ∉ Set.Ici (n : ℝ) from this)]
      simp
end GlobalTheory.Hk

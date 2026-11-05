-- Prove2me | solution 1 for GraphonGames.Existence.proof_3_15_aggregate_in_image_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:46:11.779611+00:00
-- url     : https://prove2.me/submissions/9b6c1ee6-c400-48f5-8cc7-715420631c82

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

open GraphonGames.Existence

theorem solution (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz c0 : ℝ)
    (h1 : Asm1 b μ0 cα cz) (h5 : Asm5 b c0) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1) (α : I → ℝ) (hα : MemLp α 2 volume)
    (z : I → ℝ) (hz : IsAggregate w b α z) :
    ∃ g : I → ℝ, MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ ENNReal.ofReal c0 ∧
      z =ᵐ[volume] graphonApply w g := by
  obtain ⟨hcα, hcz, hlip, -⟩ := h1
  obtain ⟨hc0, hb⟩ := h5
  -- `b` is Lipschitz, hence continuous
  have hbc : Continuous (Function.uncurry b) := by
    have hL : LipschitzWith (Real.toNNReal (Real.sqrt (cα + cz))) (Function.uncurry b) := by
      refine LipschitzWith.of_dist_le_mul fun p q => ?_
      rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.dist_eq, Prod.dist_eq, Real.dist_eq,
        Real.dist_eq]
      set d := max |p.1 - q.1| |p.2 - q.2|
      have h1' : |p.1 - q.1| ≤ d := le_max_left _ _
      have h2' : |p.2 - q.2| ≤ d := le_max_right _ _
      have hd : 0 ≤ d := le_trans (abs_nonneg _) h1'
      have key := hlip p.1 p.2 q.1 q.2
      have e1 : (p.1 - q.1) ^ 2 ≤ d ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1' 2
      have e2 : (p.2 - q.2) ^ 2 ≤ d ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2' 2
      have : (Function.uncurry b p - Function.uncurry b q) ^ 2 ≤ ((cα + cz) * d ^ 2) := by
        have := mul_le_mul_of_nonneg_left e1 hcα
        have := mul_le_mul_of_nonneg_left e2 hcz
        show (b p.1 p.2 - b q.1 q.2) ^ 2 ≤ _
        nlinarith
      calc |Function.uncurry b p - Function.uncurry b q|
          = Real.sqrt ((Function.uncurry b p - Function.uncurry b q) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((cα + cz) * d ^ 2) := Real.sqrt_le_sqrt this
        _ = Real.sqrt (cα + cz) * d := by
          rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hd]
    exact hL.continuous
  refine ⟨fun y => b (α y) (z y), ?_, ?_, ?_⟩
  · have hm : AEStronglyMeasurable (fun y => b (α y) (z y)) volume := by
      have := hbc.comp_aestronglyMeasurable (hα.1.prodMk hz.1.1)
      exact this
    refine memLp_of_bounded (a := -c0) (b := c0) ?_ hm 2
    exact Filter.Eventually.of_forall fun y => abs_le.mp (hb _ _)
  · refine (eLpNorm_le_of_ae_bound (C := c0) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
    · simpa [Real.norm_eq_abs] using hb (α y) (z y)
    · simp
  · filter_upwards [hz.2] with x hx
    simpa [graphonApply] using hx

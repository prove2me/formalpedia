-- Prove2me | solution 1 for KingmanSubadditive.PositiveMatrices.limit_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:53:48.901131+00:00
-- url     : https://prove2.me/submissions/2a0ac9bb-8a92-41dc-a177-0abb52fcb214

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
import Theorems.Thm_KingmanSubadditive_Ergodic_theorem_1
import Theorems.Thm_KingmanSubadditive_PositiveMatrices_x_subadditive
import Theorems.Thm_KingmanSubadditive_PositiveMatrices_S3_bound
open MeasureTheory Filter Topology

open KingmanSubadditive.PositiveMatrices in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    ∃ lam : Ω → ℝ, Integrable lam P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |Real.log (X Y n ω 0 0) / n - lam ω| ∂P) atTop (𝓝 0) := by
  obtain ⟨hmeas, hS1, hS2, hint⟩ := x_subadditive P Y hY
  obtain ⟨_, hS3⟩ := S3_bound P Y hY
  have hproc : KingmanSubadditive.Ergodic.IsSubadditiveProcess P (x Y) := by
    refine ⟨hmeas, hS1, hS2, ⟨fun t ht => (hint 0 t (by omega)).1, ?_⟩⟩
    refine ⟨∫ ω, Real.log (rowSumNorm (Y 1 ω)) ∂P, fun t ht => ?_⟩
    have := hS3 t ht
    simp only [KingmanSubadditive.Ergodic.mean, g] at this ⊢
    linarith
  obtain ⟨ξ, hξi, hξae, hξL1, -⟩ := KingmanSubadditive.Ergodic.theorem_1 P (x Y) hproc
  have hx : ∀ n ω, x Y 0 n ω = -Real.log (X Y n ω 0 0) := fun n ω => rfl
  refine ⟨fun ω => -ξ ω, hξi.neg, ?_, ?_⟩
  · filter_upwards [hξae] with ω hω
    have := hω.neg
    simp only [hx, neg_div, neg_neg] at this
    exact this
  · refine hξL1.congr (fun n => ?_)
    congr 1
    funext ω
    rw [hx, ← abs_neg]
    congr 1
    ring

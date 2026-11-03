-- Prove2me | solution 1 for HedgeContract.OPE.lemma_6_3_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:07:32.679934+00:00
-- url     : https://prove2.me/submissions/c8cdd94f-3d27-4047-af9e-1f1f5dd05352
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HedgeContract_OPE_lemma_6_3_lower
import Theorems.Thm_HedgeContract_OPE_lemma_6_3_upper
set_option autoImplicit false

open HedgeContract.OPE MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem solution (P : Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) (h2 : 0 ≤ netSup P) (h6 : P.δ * P.Φ ≤ P.mu) :
    ∀ y : ℝ, 0 ≤ y →
      (valueSet P P₀ B hB y).Nonempty ∧
      BddAbove (valueSet P P₀ B hB y) ∧
      Wlow P y ≤ sSup (valueSet P P₀ B hB y) ∧
      sSup (valueSet P P₀ B hB y) ≤ Wbar P y := by
  intro y hy
  obtain ⟨C, hC, hpay⟩ := lemma_6_3_lower P hP P₀ B hB h1 h2 h6 y hy
  have hmem : Wlow P y ∈ valueSet P P₀ B hB y := ⟨C, hC, hpay.symm⟩
  have hub : Wbar P y ∈ upperBounds (valueSet P P₀ B hB y) := by
    rintro v ⟨D, hD, rfl⟩
    exact lemma_6_3_upper P hP P₀ B hB h1 h2 h6 y hy D hD
  exact ⟨⟨_, hmem⟩, ⟨_, hub⟩, le_csSup ⟨_, hub⟩ hmem, csSup_le ⟨_, hmem⟩ hub⟩

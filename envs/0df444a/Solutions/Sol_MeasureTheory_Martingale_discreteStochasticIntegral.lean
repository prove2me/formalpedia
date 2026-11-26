-- Prove2me | solution 1 for MeasureTheory.Martingale.discreteStochasticIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:06.942193+00:00
-- url     : https://prove2.me/submissions/725e45aa-dae1-4057-bc0d-4a931ac67e94

import Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08

open MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

theorem solution [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H)
    (hH_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖H n ω‖ ≤ C) :
    Martingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by
  exact Prove2MeSourceProof.h_eae059fb1d843e68f8ce3b08 hX hH hH_bdd

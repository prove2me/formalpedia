-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonCompactUpperBoundAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:36:00.858407+00:00
-- url     : https://prove2.me/submissions/31b9c283-c7af-48b0-87e5-988210bfbf8c

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_isCadlag_comp_nnrealCoe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A compound-Poisson sample path is bounded above on each compact horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    ∀ᵐ ω ∂Q,
      ∀ T : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ≥0, t ≤ T →
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤ K := by
  filter_upwards [ProbabilityTheory.compoundPoisson_ae_isCadlag hdriver hrate]
    with ω hcadlag
  intro T
  obtain ⟨K, hK⟩ := Kyprianou.Ch01.cadlag_runningSup_bddAbove
    (fun t : ℝ≥0 =>
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω) (isCadlag_comp_nnrealCoe hcadlag) T
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hK ⟨t, ht, rfl⟩).trans (le_max_left _ _)

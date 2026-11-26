-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GatedDriftModelV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:10:44.002418+00:00
-- url     : https://prove2.me/submissions/30f7bfaf-91f3-4fcf-a6a8-9012dc2a932d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49AddLinearLevyV4
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_full_good_event
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_levy
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04 AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (b : ℝ) :
    ∃ X : NNReal → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ,
      IsLevyProcess X P ∧ ∀ᵐ w ∂P, ∀ t : NNReal,
        X t w = LevyFoundations.compoundPoisson b τ Y (t : ℝ) w := by
  classical
  obtain ⟨G,hG,hGae,hGzero,_,_,_⟩ := avram_a06_original_compound_full_good_event P τ Y h
  let Z : NNReal → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t w => if w ∈ G then LevyFoundations.compoundPoisson 1 τ Y (t : ℝ) w else 0
  have hZ : IsLevyProcess Z P := avram_a06_original_compound_gated_levy P τ Y h G hG hGae hGzero
  refine ⟨fun t w => Z t w + (b - 1) * (t : ℝ),exercise49AddLinearLevyV4 P Z hZ (b-1),?_⟩
  filter_upwards [hGae] with w hw
  intro t
  simp only [Z,if_pos hw,LevyFoundations.compoundPoisson,LevyFoundations.piecewisePath]
  ring

-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_8_i_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:28.234703+00:00
-- url     : https://prove2.me/submissions/d8dcaad0-ff1a-4df6-bc74-779d7dd8d069

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_true_martingale_productGrid
import Theorems.Thm_Kyprianou_Ch04_kw48_stieltjes_left_uniform_grid
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex two-parameter Kella–Whitt martingale certificate. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_8_i_v2 := by
  intro Ω inst P F L hBV Psi hPsi alpha beta
  dsimp only
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L]
  refine ⟨Kyprianou.Ch04.KW48.S L beta,?_,?_⟩
  · exact Eventually.of_forall fun w t =>
      Kyprianou.Ch04.kw48_stieltjes_left_uniform_grid L alpha beta w t
  · exact Kyprianou.Ch04.kw48_true_martingale_productGrid P F L Psi hPsi alpha beta

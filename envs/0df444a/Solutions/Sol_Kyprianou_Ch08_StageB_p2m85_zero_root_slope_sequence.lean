-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_root_slope_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:03:30.003445+00:00
-- url     : https://prove2.me/submissions/d42988f1-597f-4bc0-baf7-28781a44cd40

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_discount_sequence
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_root_inverse_at_positive
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0)
    (c : ℝ) (hlim : Tendsto (fun q : ℝ => q / Phi ψ q)
      (nhdsWithin 0 (Ioi 0)) (𝓝 c)) :
    Tendsto (fun n : ℕ => ψ (1 / ((n : ℝ)+1)) / (1 / ((n : ℝ)+1)))
      atTop (𝓝 c) := by
  have h := p2m85_zero_root_discount_sequence ψ W hW hc hz hφ
  apply (hlim.comp h).congr'
  apply Eventually.of_forall
  intro n
  have hp : 0 < (1 / ((n : ℝ)+1)) := by positivity
  simp only [Function.comp_def, p2m85_zero_root_inverse_at_positive ψ W hW hc hz hφ _ hp]

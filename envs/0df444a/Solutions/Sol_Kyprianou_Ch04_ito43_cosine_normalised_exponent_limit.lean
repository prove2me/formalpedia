-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_normalised_exponent_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:37:48.611812+00:00
-- url     : https://prove2.me/submissions/e54d63c1-db56-4cc0-981c-d261874bf951

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_levy_intensity_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_exponent_identity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution (tr : ProbabilityTheory.LevyKhintchineTriple) :
    Tendsto (fun m : ℕ => -(Kyprianou.Ch01.levyTripleExponent tr ((m:ℝ)+1)).re/((m:ℝ)+1)^2)
      atTop (nhds ((tr.gaussianVariance:ℝ)/2)) := by
  have h := Kyprianou.Ch04.ito43_cosine_levy_intensity_limit tr
  have H := (tendsto_const_nhds (x := ((tr.gaussianVariance:ℝ)/2))).add h
  convert H using 1
  · funext m
    exact Kyprianou.Ch04.ito43_cosine_exponent_identity tr ((m:ℝ)+1) (by positivity)
  · simp

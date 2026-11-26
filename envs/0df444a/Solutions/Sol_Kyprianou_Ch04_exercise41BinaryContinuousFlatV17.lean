-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BinaryContinuousFlatV17
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:16:34.244795+00:00
-- url     : https://prove2.me/submissions/7a53fb7c-ec7e-4451-ab3f-810cd8c3bca9

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → ℝ) (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (s t : NNReal) (hst : s ≤ t) (hcont : ContinuousOn f (Icc s t)) :
    f s = f t := by
  by_contra hn
  rcases hVal s with hs | hs <;> rcases hVal t with ht | ht
  · exact hn (hs.trans ht.symm)
  · obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hst hcont
      (show (-1/2 : ℝ) ∈ Icc (f t) (f s) by rw [hs,ht]; norm_num)
    rcases hVal u with h | h <;> linarith
  · obtain ⟨u,hu,he⟩ := intermediate_value_Icc hst hcont
      (show (-1/2 : ℝ) ∈ Icc (f s) (f t) by rw [hs,ht]; norm_num)
    rcases hVal u with h | h <;> linarith
  · exact hn (hs.trans ht.symm)

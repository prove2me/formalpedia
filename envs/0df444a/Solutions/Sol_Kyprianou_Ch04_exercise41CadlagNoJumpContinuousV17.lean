-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CadlagNoJumpContinuousV17
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:16:35.073949+00:00
-- url     : https://prove2.me/submissions/44a5bc26-712e-4452-b957-163676f7591f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → ℝ)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (s t : NNReal)
    (hJump : ∀ u ∈ Ioc s t, f u - Function.leftLim f u = 0) :
    ContinuousOn f (Icc s t) := by
  intro u hu
  change Tendsto f (nhdsWithin u (Icc s t)) (nhds (f u))
  rw [← nhdsWithinLT_sup_nhdsWithinGE (s := Icc s t) u, tendsto_sup]
  refine ⟨?_,(hR u).mono_left (nhdsWithin_mono _ inter_subset_right)⟩
  by_cases hs : s < u
  · have hl := hL u (lt_of_le_of_lt bot_le hs)
    rw [← sub_eq_zero.mp (hJump u ⟨hs,hu.2⟩)] at hl
    exact hl.mono_left (nhdsWithin_mono _ inter_subset_right)
  · have he : Icc s t ∩ Iio u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact (not_lt_of_ge ((le_of_not_gt hs).trans hv.1.1)) hv.2
    rw [he,nhdsWithin_empty]
    exact tendsto_bot

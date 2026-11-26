-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthGeometryV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:35:44.163437+00:00
-- url     : https://prove2.me/submissions/1fdde344-a4b2-4765-979a-8827bbd32e8a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49StrictPassagePathFactsV1
import Theorems.Thm_Kyprianou_Ch04_exercise49DepthSplitOfLUBV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthIsLUBV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hB : BddAbove (Set.range (fun t => -Y t))) (a : NNReal)
    (ha : (a : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t < 0}) :
    (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal =
      -Y a + (⨆ q : ℚ, ENNReal.ofReal (-(Y (a + Real.toNNReal q) - Y a))).toReal := by
  let Z : NNReal → ℝ := fun u => Y (a+u)-Y a
  have hz0 : Z 0 = 0 := by simp [Z]
  have hzB : BddAbove (Set.range (fun t => -Z t)) := by
    obtain ⟨b,hb⟩ := hB
    refine ⟨b+Y a, ?_⟩
    rintro v ⟨t,rfl⟩
    have h := hb (Set.mem_range_self (a+t))
    dsimp [Z] at *
    linarith
  have hzr (t : NNReal) : ContinuousWithinAt Z (Ici t) t := by
    apply (ContinuousWithinAt.comp (t := Ici (a+t)) (g := fun u => Y u)
      (f := fun u : NNReal => a+u) (hr (a+t))
      (continuous_const.add continuous_id).continuousWithinAt
      (fun u hu => add_le_add_right hu a)).sub continuousWithinAt_const
  obtain ⟨hp,ht⟩ := Kyprianou.Ch04.exercise49StrictPassagePathFactsV1 Y h0 hr a ha
  exact Kyprianou.Ch04.exercise49DepthSplitOfLUBV1 Y a _ _ hp ht
    (Kyprianou.Ch04.exercise49RationalDepthIsLUBV1 Y h0 hr hB)
    (Kyprianou.Ch04.exercise49RationalDepthIsLUBV1 Z hz0 hzr hzB)

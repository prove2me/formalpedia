-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_leftGridPoint
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:53.509559+00:00
-- url     : https://prove2.me/submissions/052c65c8-f840-42a2-86e3-04349537407c

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F000
import Mathlib.Analysis.SpecificLimits.Basic
open Filter
open scoped Topology
open LevyStochCalc.Probability

theorem solution (s : ℝ) :
    Tendsto (fun k : ℕ => leftGridPoint k s) atTop (𝓝[<] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hm : Tendsto (fun k : ℕ => (1 : ℝ) / 2 ^ k) atTop (𝓝 0) := by
      simpa only [div_pow, one_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 2) (by norm_num) (by norm_num))
    have hl : Tendsto (fun k : ℕ => s - 1 / 2 ^ k) atTop (𝓝 s) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := s)).sub hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
      (fun k => by linarith [sub_leftGridPoint_le k s]) (fun k => (leftGridPoint_lt k s).le)
  · exact Filter.Eventually.of_forall (fun k => leftGridPoint_lt k s)

#print axioms solution

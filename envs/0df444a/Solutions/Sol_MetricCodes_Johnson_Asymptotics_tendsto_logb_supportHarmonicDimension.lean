-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_supportHarmonicDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/963f69d3-537e-462e-bde0-d4bb435285ad

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_supportDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_booleanHarmonicDimension_of_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (shellWeight a n) (supportDegree b n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  by_cases hbzero : b = 0
  · subst b
    simp [supportDegree, MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.booleanHarmonicDimension]
  · have hb : 0 < b := lt_of_le_of_ne h.support_nonneg
      (Ne.symm hbzero)
    have hba : b < a := by
      nlinarith [h.support_lt_half, h.weight_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * supportDegree b n ≤ shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.support_half)
    have hN : ∀ᶠ n : ℕ in atTop, shellWeight a n ≤ n := by
      apply Eventually.of_forall
      intro n
      exact MetricCodes.Hamming.longitudinalDegree_le_dimension
        (by linarith [h.weight_lt_half]) n
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_shellWeight_ratio h.weight_pos.le)
      (tendsto_supportDegree_ratio h.support_nonneg)
      hb hba hhalf hN
end MetricCodes.Johnson.Asymptotics

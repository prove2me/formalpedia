-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_complementHarmonicDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/f599fca7-7ab8-4ebc-ad69-c1f3034c7128

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_weight_complement_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_booleanHarmonicDimension_of_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementShellWeight_ratio

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
            (n - shellWeight a n) (complementDegree g n) : ℝ) /
            (n : ℝ))
      atTop (nhds
        ((1 - a) * MetricCodes.binaryEntropy (g / (1 - a)))) := by
  by_cases hgzero : g = 0
  · subst g
    simp [complementDegree, MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.booleanHarmonicDimension]
  · have hg : 0 < g := lt_of_le_of_ne h.complement_nonneg
      (Ne.symm hgzero)
    have hga : g < 1 - a := by
      nlinarith [h.complement_lt_half, h.weight_complement_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * complementDegree g n ≤ n - shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.complement_half)
    have hN :
        ∀ᶠ n : ℕ in atTop, n - shellWeight a n ≤ n :=
      Eventually.of_forall (fun n => Nat.sub_le n _)
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_complementShellWeight_ratio
        h.weight_pos.le (by linarith [h.weight_lt_half]))
      (tendsto_complementDegree_ratio h.complement_nonneg)
      hg hga hhalf hN
end MetricCodes.Johnson.Asymptotics

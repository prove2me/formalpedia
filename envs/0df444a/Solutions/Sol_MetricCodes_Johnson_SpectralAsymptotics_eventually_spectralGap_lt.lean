-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.eventually_spectralGap_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/dc5d1157-4b94-4a4f-b27e-0dcc17d2de9d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Hamming_tendsto_threshold_ceil
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_threshold_ceil
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralGap_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap d a b g u <
        MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n) -
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))) := by
  have hpositive := spectralGap_pos h
  let A := MetricCodes.Johnson.asymptoticThreshold d a
  let S := MetricCodes.Johnson.spectralLimit a b g u
  have hupper : S - spectralGap d a b g u < S := by
    linarith
  have hlower : A < A + spectralGap d a b g u := by
    linarith
  have heigen := eventually_topEigenvalue_gt h.1 hupper
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h.1).eventually
      (gt_mem_nhds hlower)
  filter_upwards [heigen, hthreshold] with n hn ht
  dsimp [A, S] at hn ht
  unfold spectralGap at hpositive hn ht ⊢
  linarith
end MetricCodes.Johnson.SpectralAsymptotics

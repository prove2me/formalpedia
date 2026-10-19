-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.diagonalLimit_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/7ccaf708-aa1c-41ec-94fd-668d67929393

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (_h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a 0 0 u =
      MetricCodes.Johnson.centeredWeight a ^ 2 *
        (1 - MetricCodes.Johnson.centeredDegree u ^ 2) /
        (MetricCodes.Johnson.centeredDegree u ^ 2 *
          (1 - MetricCodes.Johnson.centeredWeight a ^ 2)) := by
  unfold diagonalLimit MetricCodes.Johnson.centeredSigma
    MetricCodes.Johnson.centeredEta
  have heta : 1 - 2 * a + 2 * (0 : ℝ) - 2 * 0 =
      MetricCodes.Johnson.centeredWeight a := by
    unfold MetricCodes.Johnson.centeredWeight
    ring
  rw [heta]
  norm_num
  ring
end MetricCodes.Johnson.SpectralAsymptotics

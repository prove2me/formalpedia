-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.edgeLimit_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/926d6e38-d07a-4c97-b9fc-433ca8bfc34c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_sq_sub_eta_sq_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_zeroFibreParameters

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
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    edgeLimit a 0 0 u =
      (MetricCodes.Johnson.centeredDegree u ^ 2 -
        MetricCodes.Johnson.centeredWeight a ^ 2) *
        Real.sqrt (1 - MetricCodes.Johnson.centeredDegree u ^ 2) /
        (2 * MetricCodes.Johnson.centeredDegree u ^ 2 *
          (1 - MetricCodes.Johnson.centeredWeight a ^ 2)) := by
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  unfold edgeLimit
  have heta : MetricCodes.Johnson.centeredEta a 0 0 =
      MetricCodes.Johnson.centeredWeight a := by
    simp [MetricCodes.Johnson.centeredEta, MetricCodes.Johnson.centeredWeight]
  have hsigma : MetricCodes.Johnson.centeredSigma 0 0 = 1 := by
    norm_num [MetricCodes.Johnson.centeredSigma]
  rw [heta, hsigma]
  have hrad :
      Real.sqrt
          ((MetricCodes.Johnson.centeredDegree u ^ 2 -
              MetricCodes.Johnson.centeredWeight a ^ 2) *
            (MetricCodes.Johnson.centeredDegree u ^ 2 -
              MetricCodes.Johnson.centeredWeight a ^ 2) *
            ((1 : ℝ) ^ 2 - MetricCodes.Johnson.centeredDegree u ^ 2)) =
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
          Real.sqrt (1 - MetricCodes.Johnson.centeredDegree u ^ 2) := by
    rw [one_pow]
    rw [← pow_two]
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq hfactor'.le]
  rw [hrad]
end MetricCodes.Johnson.SpectralAsymptotics

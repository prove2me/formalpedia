-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.spectralAtom_scale_sub_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/466b5736-d918-4ede-8fdd-2300395febe4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_lt_half
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_sq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_strictMonoOn

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {c u : ℝ}
    (hc : 1 ≤ c) (hc' : c ≤ 2) (hu : 0 ≤ u) :
    quadraticCoordinate u * (c - 1) /
        ((1 + 8 * quadraticCoordinate u) *
          (1 + 4 * quadraticCoordinate u)) ≤
      spectralAtom (scaleCoordinate c u) - spectralAtom u := by
  let x : ℝ := quadraticCoordinate u
  let q : ℝ := spectralAtom u
  let Q : ℝ := spectralAtom (scaleCoordinate c u)
  have hx : 0 ≤ x := by
    dsimp [x]
    unfold quadraticCoordinate
    positivity
  have hcpos : 0 < c := by linarith
  have hscale : 0 ≤ scaleCoordinate c u :=
    scaleCoordinate_nonneg hcpos.le hu
  have hsq : Q ^ 2 - q ^ 2 =
      x * (c - 1) / ((1 + 4 * c * x) * (1 + 4 * x)) := by
    dsimp [Q, q]
    rw [spectralAtom_sq hscale, spectralAtom_sq hu,
      quadraticCoordinate_scaleCoordinate hcpos.le hu]
    change c * x / (1 + 4 * (c * x)) - x / (1 + 4 * x) = _
    have hden₁ : 1 + 4 * c * x ≠ 0 := by positivity
    have hden₂ : 1 + 4 * x ≠ 0 := by positivity
    field_simp [hden₁, hden₂]
    ring
  have hqu : 0 ≤ q := spectralAtom_nonneg hu
  have hQ : 0 ≤ Q := spectralAtom_nonneg hscale
  have hqhalf : q < (1 / 2 : ℝ) := spectralAtom_lt_half hu
  have hQhalf : Q < (1 / 2 : ℝ) := spectralAtom_lt_half hscale
  have hqle : q ≤ Q := by
    have hquad : quadraticCoordinate u ≤
        quadraticCoordinate (scaleCoordinate c u) := by
      rw [quadraticCoordinate_scaleCoordinate hcpos.le hu]
      dsimp [x] at hx ⊢
      nlinarith
    by_contra hnot
    have hreverse : Q < q := lt_of_not_ge hnot
    have hreverse' : scaleCoordinate c u < u := by
      by_contra hnot'
      exact (not_le_of_gt hreverse)
        (spectralAtom_strictMonoOn.monotoneOn hu hscale
          (le_of_not_gt hnot'))
    exact (not_le_of_gt (quadraticCoordinate_strictMonoOn hscale hu hreverse'))
      hquad
  have hfactor : Q ^ 2 - q ^ 2 ≤ Q - q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqle)
      (show 0 ≤ 1 - (Q + q) by linarith)]
  have hden₁ : 0 < (1 + 4 * c * x) * (1 + 4 * x) := by positivity
  have hden₂ : 0 < (1 + 8 * x) * (1 + 4 * x) := by positivity
  have hnum : 0 ≤ x * (c - 1) := mul_nonneg hx (sub_nonneg.mpr hc)
  have hdenle :
      (1 + 4 * c * x) * (1 + 4 * x) ≤
        (1 + 8 * x) * (1 + 4 * x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc') hx]
  have hfractions :
      x * (c - 1) / ((1 + 8 * x) * (1 + 4 * x)) ≤
        x * (c - 1) / ((1 + 4 * c * x) * (1 + 4 * x)) := by
    exact (div_le_div_iff₀ hden₂ hden₁).mpr
      (mul_le_mul_of_nonneg_left hdenle hnum)
  dsimp [x, Q, q] at hfractions hfactor hsq ⊢
  linarith
end MetricCodes.Spherical.HigherHierarchy

-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_compensated_append_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/0e17f130-622d-4236-816b-62a2bf069c2f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_append
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scaleCoordinate_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scalingGainCoefficient_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_scale_sub_lower_bound
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_appendSpectralLossUpper_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_append_scaled_spectralLoss_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compensatedScalingSlope_pos

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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r))
    {ε : ℝ} (hε : 0 < ε)
    (hmoderate : compensatedScalingFactor a b ε ≤ 2) :
    Gamma a b <
      Gamma
        (appendAmbient (scaleAmbient (compensatedScalingFactor a b ε) a))
        (appendStabilizer
          (scaleStabilizer (compensatedScalingFactor a b ε) b)
          (scaleCoordinate (compensatedScalingFactor a b ε) ε)) := by
  let c : ℝ := compensatedScalingFactor a b ε
  let e : ℝ := quadraticCoordinate ε
  let D : ℝ := scalingGainCoefficient a b
  let M : ℝ := appendSpectralLossUpper a b
  have he : 0 < e := by
    dsimp [e]
    unfold quadraticCoordinate
    positivity
  have hD : 0 < D := scalingGainCoefficient_pos h hlast
  have hM : 0 < M := appendSpectralLossUpper_pos h hlast
  have hslope : 0 < compensatedScalingSlope a b :=
    compensatedScalingSlope_pos h hlast
  have hc : 1 < c := by
    dsimp [c, compensatedScalingFactor]
    nlinarith
  have hscale : Interlacing (scaleAmbient c a) (scaleStabilizer c b) :=
    h.scale (by linarith)
  have hlast' : 0 < scaleAmbient c a (Fin.last r) :=
    scaleCoordinate_pos (by linarith) hlast
  have hgain := Gamma_scale_sub_lower_bound h hc.le hmoderate
  have hloss := append_scaled_spectralLoss_le h hlast
    (show 0 < c by linarith) hε.le
  have hrelation : (c - 1) * D = e * (M + 1) := by
    dsimp [c, D, M, compensatedScalingFactor, compensatedScalingSlope]
    field_simp [(scalingGainCoefficient_pos h hlast).ne']
    ring
  rw [Gamma_append hscale hlast']
  dsimp [c] at hgain hloss hrelation ⊢
  nlinarith
end MetricCodes.Spherical.HigherHierarchy

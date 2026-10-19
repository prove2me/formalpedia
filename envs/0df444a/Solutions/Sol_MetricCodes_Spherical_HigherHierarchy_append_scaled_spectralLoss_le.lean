-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.append_scaled_spectralLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/31cacc32-12e2-492e-83f9-af0b89fd7f64

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_lt_half
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_scale

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
    {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) :
    quadraticCoordinate (scaleCoordinate c ε) *
        appendSpectralLoss (scaleAmbient c a) (scaleStabilizer c b) ≤
      quadraticCoordinate ε * appendSpectralLossUpper a b := by
  rw [quadraticCoordinate_scaleCoordinate hc.le hε]
  unfold appendSpectralLoss appendSpectralLossUpper
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [lagrangeWeight_scale h hc i]
  dsimp [scaleAmbient]
  rw [quadraticCoordinate_scaleCoordinate hc.le (h.ambient_nonneg i)]
  change c * quadraticCoordinate ε *
      (lagrangeWeight a b i * spectralAtom (scaleCoordinate c (a i)) /
        (c * quadraticCoordinate (a i))) ≤
      quadraticCoordinate ε *
        (lagrangeWeight a b i / (2 * quadraticCoordinate (a i)))
  have hai : 0 < a i :=
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hx : 0 < quadraticCoordinate (a i) := by
    unfold quadraticCoordinate
    positivity
  have he : 0 ≤ quadraticCoordinate ε := by
    unfold quadraticCoordinate
    positivity
  have hatom := spectralAtom_lt_half
    (scaleCoordinate_nonneg hc.le hai.le)
  have hweight := h.lagrangeWeight_pos i
  field_simp [hc.ne', hx.ne']
  nlinarith [mul_nonneg he hweight.le,
    mul_nonneg (mul_nonneg he hweight.le)
      (sub_nonneg.mpr hatom.le)]
end MetricCodes.Spherical.HigherHierarchy

-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/11e69c56-0ae8-44da-87a5-2ba697fe209f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_append_castSucc

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
    (ε : ℝ) :
    Gamma (appendAmbient a) (appendStabilizer b ε) =
      Gamma a b - quadraticCoordinate ε * appendSpectralLoss a b := by
  unfold Gamma
  rw [Fin.sum_univ_castSucc]
  have hzero : spectralAtom ((appendAmbient a) (Fin.last (r + 1))) = 0 := by
    simp [appendAmbient, spectralAtom, quadraticCoordinate]
  rw [hzero, mul_zero, add_zero]
  simp_rw [lagrangeWeight_append_castSucc h hlast ε]
  simp only [appendAmbient, Fin.snoc_castSucc]
  unfold appendSpectralLoss
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
end MetricCodes.Spherical.HigherHierarchy

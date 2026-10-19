-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_sameLevel_opening_strict_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/7b9de5d8-c43e-473b-9ee2-1a2a81da4c95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_Phi_opening_lt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingContractionSpeed_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_Gamma_opening_gt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_opening_interlacing

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
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) :
    ∃ A : Fin (r + 1) → ℝ,
      0 < A (Fin.last r) ∧ Interlacing A b ∧
        Gamma a b < Gamma A b ∧ Phi A b < Phi a b := by
  let η : ℝ := openingContractionSpeed a b
  have hη : 0 < η := openingContractionSpeed_pos h
  have hspectral := eventually_Gamma_opening_gt h hzero
  have hentropy := eventually_Phi_opening_lt hr h hzero hη
  have hinterlacing := eventually_opening_interlacing h hzero η
  have hgood : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∃ A : Fin (r + 1) → ℝ,
        0 < A (Fin.last r) ∧ Interlacing A b ∧
          Gamma a b < Gamma A b ∧ Phi A b < Phi a b := by
    filter_upwards [hspectral, hentropy, hinterlacing, self_mem_nhdsWithin]
      with t htGamma htPhi htInterlacing (ht : 0 < t)
    refine ⟨openingAmbient a (η * t) (t ^ 2), ?_,
      htInterlacing, htGamma, htPhi⟩
    simp [openingAmbient, sq_pos_of_pos ht]
  obtain ⟨t, ht⟩ := hgood.exists
  exact ht
end MetricCodes.Spherical.HigherHierarchy

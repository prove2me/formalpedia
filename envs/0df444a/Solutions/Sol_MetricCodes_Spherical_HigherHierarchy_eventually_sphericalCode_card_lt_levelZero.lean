-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_sphericalCode_card_lt_levelZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/b2f7daaf-60bb-4945-bef3-e5744c4a515e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_zero
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_sphericalCode_card_lt_rpow
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_oneRow_certificate_better_than_levelZero

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
noncomputable section
open Filter Topology
open scoped Topology
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (a : Fin 1 → ℝ) (b : Fin 0 → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s < 2 * Gamma a b) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) <
        (2 : ℝ) ^ (Phi a b * (n : ℝ)) := by
  have ha_nonneg : 0 ≤ a 0 := hinterlacing.ambient_nonneg 0
  have ha : 0 < a 0 := by
    by_contra hnot
    have hazero : a 0 = 0 := le_antisymm (le_of_not_gt hnot) ha_nonneg
    rw [Gamma_zero, hazero] at hspectral
    norm_num [spectralAtom, quadraticCoordinate] at hspectral
    linarith
  rw [Gamma_zero] at hspectral
  obtain ⟨A, B, hB, hBA, hgap, hcost⟩ :=
    exists_oneRow_certificate_better_than_levelZero ha hspectral
  rw [Phi_zero]
  exact MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
    hs' hB hBA hgap hcost
end MetricCodes.Spherical.HigherHierarchy

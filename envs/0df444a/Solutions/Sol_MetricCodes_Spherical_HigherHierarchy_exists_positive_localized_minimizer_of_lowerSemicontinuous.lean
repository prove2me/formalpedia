-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_localized_minimizer_of_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/3067a5ac-97cb-48a8-99dd-5775210ce2db

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_localizedEnvelope_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_localized_minimizer_of_lowerSemicontinuous

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
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ κ t)
    (hlsc : LowerSemicontinuousOn
      (fun t => κ t +
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t)
      (Set.Icc 0 s))
    (hzero : ∃ u ∈ Set.Icc (0 : ℝ) s,
      κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u <
        κ 0 + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0) :
    ∃ t ∈ Set.Ioc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  obtain ⟨t, ht, heq⟩ :=
    exists_localized_minimizer_of_lowerSemicontinuous hs hs' hκ hlsc
  obtain ⟨u, hu, huzero⟩ := hzero
  have htu :
      κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t ≤
        κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u := by
    rw [← heq]
    exact MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_le
      hs' hu hκ
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht.1 with htpos | rfl
    · exact htpos
    · linarith
  exact ⟨t, ⟨htpos, ht.2⟩, heq⟩
end MetricCodes.Spherical.HigherHierarchy

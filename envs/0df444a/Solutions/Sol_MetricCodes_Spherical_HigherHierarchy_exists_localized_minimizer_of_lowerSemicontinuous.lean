-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_localized_minimizer_of_lowerSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/7ba7db0e-da69-43e1-9085-35f6828a6e3d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_localizedEnvelope_bddBelow

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
      (Set.Icc 0 s)) :
    ∃ t ∈ Set.Icc (0 : ℝ) s,
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope κ s =
        κ t + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  obtain ⟨t, ht, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      (Set.nonempty_Icc.mpr hs) isCompact_Icc hlsc
  refine ⟨t, ht, ?_⟩
  unfold MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_antisymm
  · exact csInf_le
      (MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope_bddBelow
        hs' hκ)
      ⟨t, ht, rfl⟩
  · apply le_csInf (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs))
    rintro _ ⟨x, hx, rfl⟩
    exact hmin hx
end MetricCodes.Spherical.HigherHierarchy

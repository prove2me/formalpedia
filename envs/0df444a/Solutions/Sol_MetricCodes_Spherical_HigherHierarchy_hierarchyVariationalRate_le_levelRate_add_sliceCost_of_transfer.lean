-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_levelRate_add_sliceCost_of_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/d63fae0c-d371-4b0d-a898-a937522d6b9c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_mem_source_interval

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
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (ht : 0 ≤ t) (hts : t ≤ s)
    (htransfer : ∀ {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ},
      Interlacing A B → t < 2 * Gamma A B →
        hierarchyVariationalRate s ≤
          Phi A B +
            MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    hierarchyVariationalRate s ≤
      levelRate r t +
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  have hnonempty : (levelRateSet r t).Nonempty :=
    levelRateSet_nonempty_of_mem_source_interval hs hs' hts
  have hlower :
      hierarchyVariationalRate s -
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t ≤
        levelRate r t := by
    unfold levelRate
    apply le_csInf hnonempty
    rintro _ ⟨A, B, hAB, hgap, rfl⟩
    linarith [htransfer hAB hgap]
  linarith
end MetricCodes.Spherical.HigherHierarchy

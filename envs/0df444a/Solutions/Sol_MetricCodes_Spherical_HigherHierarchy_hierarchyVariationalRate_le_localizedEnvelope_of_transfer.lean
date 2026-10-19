-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedEnvelope_of_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/f35d4e01-1206-41e7-bbc6-4ecbdc728000

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_levelRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_levelRate_add_sliceCost_of_transfer

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
    {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (htransfer : ∀ {t : ℝ}, 0 ≤ t → t < s →
      ∀ {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ},
        Interlacing A B → t < 2 * Gamma A B →
          hierarchyVariationalRate s ≤
            Phi A B +
              MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t) :
    hierarchyVariationalRate s ≤
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  unfold MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_csInf
    (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs.le))
  rintro _ ⟨t, ⟨ht, hts⟩, rfl⟩
  rcases lt_or_eq_of_le hts with hlt | rfl
  · exact hierarchyVariationalRate_le_levelRate_add_sliceCost_of_transfer
      hs hs' ht hts (htransfer ht hlt)
  · simpa [MetricCodes.Spherical.SidelnikovLocalization.sliceCost_self hs']
      using (hierarchyVariationalRate_le_levelRate (r := r) hs hs')
end MetricCodes.Spherical.HigherHierarchy

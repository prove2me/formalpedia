-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.rowVariationalRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/dcc65926-e1aa-46da-a664-c83366bf2460

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Johnson_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_sphericalEntropy_pos
import Theorems.Thm_MetricCodes_Gamma_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_rowVariationalRate_nonneg_all

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    MetricCodes.Spherical.variationalRate 0 = 0 := by
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).pow 2).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hentropy : Tendsto
      (fun t : ℝ => MetricCodes.sphericalEntropy (t ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def, MetricCodes.sphericalEntropy] using
      (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt
        (x := (0 : ℝ))).tendsto.comp hsquare
  apply le_antisymm (ge_of_tendsto hentropy ?_)
    (rowVariationalRate_nonneg_all 0)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  let a : ℝ := t ^ 2
  let b : ℝ := a / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b]; linarith
  have hgamma : 0 < MetricCodes.Gamma a b :=
    MetricCodes.Gamma_pos hb.le hba
  have hfeasible : MetricCodes.Spherical.Feasible 0 a b :=
    ⟨hb, hba, by linarith⟩
  have hbound := MetricCodes.Spherical.variationalRate_le_of_feasible hfeasible
  have hbentropy := MetricCodes.sphericalEntropy_pos hb
  dsimp [a] at hbound ⊢
  linarith
end MetricCodes.Spherical.HigherHierarchy

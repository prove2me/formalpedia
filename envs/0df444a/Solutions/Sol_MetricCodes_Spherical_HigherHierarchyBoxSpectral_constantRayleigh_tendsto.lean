-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/1e86c40d-1884-4c37-b249-bdc371cb5588

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_constantRayleigh_eq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_constantRayleigh_const

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchyBoxSpectral
theorem _root_.solution {r m : ℕ}
    (edge : ℕ → BoxVertex r m → Fin (r + 1) → ℝ)
    (weight : Fin (r + 1) → ℝ)
    (hlimit : ∀ (v : BoxVertex r m) (i : Fin (r + 1)),
      Tendsto (fun n : ℕ => edge n v i) atTop (𝓝 (weight i))) :
    Tendsto (fun n : ℕ => constantRayleigh (edge n))
      atTop
      (𝓝 ((2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i)) := by
  classical
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
            if (v i).val < m then edge n v i else 0)
        atTop
        (𝓝 (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
          if (v i).val < m then weight i else 0)) := by
    apply tendsto_finsetSum
    intro v _
    apply tendsto_finsetSum
    intro i _
    by_cases h : (v i).val < m
    · simpa [h] using hlimit v i
    · simp [h]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hquotient :
      Tendsto
        (fun n : ℕ =>
          (2 * (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
            if (v i).val < m then edge n v i else 0)) /
              (Fintype.card (BoxVertex r m) : ℝ))
        atTop
        (𝓝 ((2 * (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
          if (v i).val < m then weight i else 0)) /
            (Fintype.card (BoxVertex r m) : ℝ))) :=
    (htwo.mul hsum).div_const
      (Fintype.card (BoxVertex r m) : ℝ)
  have hresult :
      Tendsto (fun n : ℕ => constantRayleigh (edge n)) atTop
        (𝓝 (constantRayleigh (fun _ : BoxVertex r m => weight))) := by
    simpa only [constantRayleigh_eq] using hquotient
  rw [constantRayleigh_const] at hresult
  exact hresult
end MetricCodes.Spherical.HigherHierarchyBoxSpectral

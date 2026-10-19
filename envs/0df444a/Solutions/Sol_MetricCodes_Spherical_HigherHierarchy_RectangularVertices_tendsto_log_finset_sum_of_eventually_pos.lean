-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_log_finset_sum_of_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/83fd686e-0fbb-425f-a2fa-add13ba1efc4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_log_finset_sum

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
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (H : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < f i n)
    (hlim : ∀ i, Tendsto (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 H)) :
    Tendsto (fun n : ℕ => Real.log (∑ i, f i n) / (n : ℝ))
      atTop (𝓝 H) := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hf)
  let g : ι → ℕ → ℝ := fun i n => if N ≤ n then f i n else 1
  have hg : ∀ i n, 0 < g i n := by
    intro i n
    dsimp [g]
    split_ifs with hn
    · exact hN n hn i
    · norm_num
  have hgeq : ∀ i, (fun n => g i n) =ᶠ[atTop] (fun n => f i n) := by
    intro i
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [g, hn]
  have hglim : ∀ i, Tendsto
      (fun n : ℕ => Real.log (g i n) / (n : ℝ)) atTop (𝓝 H) := by
    intro i
    apply (hlim i).congr'
    filter_upwards [hgeq i] with n hn
    rw [hn]
  have hsum := tendsto_log_finset_sum g H hg hglim
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [g, hn]
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices

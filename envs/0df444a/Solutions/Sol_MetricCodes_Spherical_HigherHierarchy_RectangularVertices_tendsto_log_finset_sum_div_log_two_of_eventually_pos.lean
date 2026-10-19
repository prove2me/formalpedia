-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_log_finset_sum_div_log_two_of_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/de8e407f-7c53-4101-8244-e91742dcf3b4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_log_finset_sum_of_eventually_pos

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
    (hlim : ∀ i, Tendsto
      (fun n : ℕ => (Real.log (f i n) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 H)) :
    Tendsto
      (fun n : ℕ => (Real.log (∑ i, f i n) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 H) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlim' : ∀ i, Tendsto
      (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 (H * Real.log 2)) := by
    intro i
    have h := (hlim i).mul_const (Real.log 2)
    simpa [hlog] using h
  have hsum := tendsto_log_finset_sum_of_eventually_pos
    f (H * Real.log 2) hf hlim'
  have h := hsum.div_const (Real.log 2)
  simpa [hlog] using h
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices

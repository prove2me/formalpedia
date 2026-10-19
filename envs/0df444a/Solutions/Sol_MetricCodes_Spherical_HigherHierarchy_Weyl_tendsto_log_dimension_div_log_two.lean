-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_dimension_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/6f29b8b4-4837-48f9-b99c-e0a89c5693fb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_dimension_div

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
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution
    {r : ℕ} (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i)
    (hanti : StrictAnti a)
    (hdominant : ∀ n, Antitone (lam n))
    (hTop : ∀ i, Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlim : ∀ i,
      Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
        atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (dimension n (lam n)) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  have h := (tendsto_log_dimension_div lam a ha hanti hdominant hTop hlim).div_const
    (Real.log 2)
  have hentropy :
      (∑ i : Fin (r + 1),
        ((1 + a i) * Real.log (1 + a i) - a i * Real.log (a i))) /
          Real.log 2 =
        ∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  rw [hentropy] at h
  exact h
end MetricCodes.Spherical.HigherHierarchy.Weyl

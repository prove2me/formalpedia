-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_hierarchyStieltjesRatio_of_coordinatewise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/dc32960d-c5af-4c0d-b057-8649ac8435c4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_quadraticCoordinate_of_tendsto

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
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => hierarchyStieltjesRatio (a n) (b n) t)
      atTop (𝓝 (hierarchyStieltjesRatio A B t)) := by
  have hnum :
      Tendsto (fun n =>
        ∏ i : Fin r, (t + quadraticCoordinate (b n i)))
        atTop (𝓝 (∏ i : Fin r, (t + quadraticCoordinate (B i)))) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact (tendsto_const_nhds (x := t)).add
      (tendsto_quadraticCoordinate_of_tendsto (hb i))
  have hden :
      Tendsto (fun n =>
        ∏ i : Fin (r + 1), (t + quadraticCoordinate (a n i)))
        atTop (𝓝 (∏ i : Fin (r + 1), (t + quadraticCoordinate (A i)))) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact (tendsto_const_nhds (x := t)).add
      (tendsto_quadraticCoordinate_of_tendsto (ha i))
  have hnonzero :
      (∏ i : Fin (r + 1), (t + quadraticCoordinate (A i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hq : 0 ≤ quadraticCoordinate (A i) := by
      unfold quadraticCoordinate
      exact mul_nonneg (hA i) (by linarith [hA i])
    linarith
  exact hnum.div hden hnonzero
end MetricCodes.Spherical.HigherHierarchy

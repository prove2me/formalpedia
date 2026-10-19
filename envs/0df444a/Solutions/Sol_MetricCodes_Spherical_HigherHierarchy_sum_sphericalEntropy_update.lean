-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sum_sphericalEntropy_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/3fd6424e-6145-4061-b21a-3272f3ba546c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    (∑ j : Fin n, MetricCodes.sphericalEntropy (Function.update a i x j)) =
      (∑ j : Fin n, MetricCodes.sphericalEntropy (a j)) -
        MetricCodes.sphericalEntropy (a i) + MetricCodes.sphericalEntropy x := by
  classical
  have hupdate :
      (fun j : Fin n => MetricCodes.sphericalEntropy (Function.update a i x j)) =
        Function.update (fun j : Fin n => MetricCodes.sphericalEntropy (a j))
          i (MetricCodes.sphericalEntropy x) := by
    funext j
    by_cases hij : j = i <;> simp [hij]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun j => MetricCodes.sphericalEntropy (a j)) (Finset.mem_univ i)
  linarith
end MetricCodes.Spherical.HigherHierarchy

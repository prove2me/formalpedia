-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.reachable_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/ee73c070-0856-4ede-830e-f0f7523eeb23

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_grid_adj_nextVertex

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
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
theorem _root_.solution {r m : ℕ} (v : Vertex r m) :
    (grid r m).Reachable (fun _ => 0) v := by
  classical
  induction hN : height v using Nat.strong_induction_on generalizing v with
  | h N ih =>
      by_cases hz : v = (fun _ => 0)
      · subst v
        exact SimpleGraph.Reachable.rfl
      · have hpositive : ∃ i : Fin (r + 1), 0 < (v i).val := by
          by_contra hnot
          apply hz
          funext i
          apply Fin.ext
          apply Nat.eq_zero_of_not_pos
          intro hi
          exact hnot ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hpositive
        let u : Vertex r m :=
          Function.update v i ⟨(v i).val - 1, by omega⟩
        have hu : height u < height v := by
          unfold height
          change
            (∑ j : Fin (r + 1),
              (Function.update v i
                (⟨(v i).val - 1, by omega⟩ : Fin (m + 1)) j).val) <
              ∑ j : Fin (r + 1), (v j).val
          have hpoint (j : Fin (r + 1)) :
              (Function.update v i
                (⟨(v i).val - 1, by omega⟩ : Fin (m + 1)) j).val =
                Function.update (fun k : Fin (r + 1) => (v k).val)
                  i ((v i).val - 1) j := by
            by_cases hji : j = i
            · subst j
              simp
            · simp [Function.update_of_ne hji]
          simp_rw [hpoint]
          rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
          have hold :=
            Finset.sum_erase_add (Finset.univ : Finset (Fin (r + 1)))
              (fun j => (v j).val) (Finset.mem_univ i)
          rw [Finset.sdiff_singleton_eq_erase]
          omega
        have hless : height u < N := hN ▸ hu
        have hreach := ih (height u) hless u rfl
        have hstep : (u i).val < m := by
          dsimp [u]
          simp
          omega
        have heq : nextVertex u i hstep = v := by
          funext j
          by_cases hji : j = i
          · subst j
            apply Fin.ext
            simp [nextVertex, u]
            omega
          · simp [nextVertex, u, hji]
        have hedge : (grid r m).Reachable u v := by
          rw [← heq]
          exact (grid_adj_nextVertex u i hstep).reachable
        exact hreach.trans hedge
end MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency

-- Prove2me | solution 1 for OAI.BoundedTreePotentials.TreeCalculus.main_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:43.04459+00:00
-- url     : https://prove2.me/submissions/8acb88af-d653-4506-8023-65837c813fd3

import Mathlib
import Definitions.Def_BoundedTreePotentials
import Definitions.Def_OAIQWBTP000
import Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_averaged_modulus_real
import Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_completed_space
import Theorems.Thm_OAI_BoundedTreePotentials_TreeCalculus_four_no_equivalent_AUC_real

section
-- module Solutions.OAIQW_BoundedTreePotentials.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace BoundedTreePotentials.TreeCalculus

/-- Every root convention and quadratic budget gives a complete separable
infinite-dimensional space with a positive real averaged midpoint modulus,
but no continuously linearly equivalent space has an AUC norm. -/
theorem main_counterexample_oai (r : Bool) (k : QuadraticKind) :
    (CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
      TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
      ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k))) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      Real.sqrt (1 + t ^ 2 / 4) - 1 ≤
        averagedModulusReal (TestCompletion (treeTestFamily r k)) t) ∧
    (∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y],
      (TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) → ¬IsAUCReal Y) := by
  refine ⟨four_completed_space r k, ?_, ?_⟩
  · intro t ht ht1
    exact four_averaged_modulus_real r k ht ht1
  · intro Y _ _ equivalence
    exact four_no_equivalent_AUC_real r k equivalence

end BoundedTreePotentials.TreeCalculus

end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedTreePotentials.TreeCalculus.main_counterexample_oai.{u} := @OAI.BoundedTreePotentials.TreeCalculus.main_counterexample_oai.{u}

-- Prove2me | solution 1 for OAI.BoundedTreePotentials.TreeCalculus.four_completed_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:24:40.000689+00:00
-- url     : https://prove2.me/submissions/21958b4a-64ae-47c1-9ab9-6ba46c984540

import Mathlib
import Definitions.Def_BoundedTreePotentials
import Definitions.Def_OAIQWBTP000

section
-- module Solutions.OAIQW_BoundedTreePotentials.Moduli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section TestSeparable
open scoped Classical
variable {I : Type*}

lemma coordinates_linearlyIndependent (K : TestFamily I) :
    LinearIndependent ℝ (coordinateVector K) := by
  have h := (testVectorBasis K).linearIndependent.map'
    (UniformSpace.Completion.toComplL : TestVector K →L[ℝ] TestCompletion K).toLinearMap
    (LinearMap.ker_eq_bot.mpr (UniformSpace.Completion.coe_injective (TestVector K)))
  exact h

lemma testCompletion_infiniteDimensional (K : TestFamily I) [Infinite I] :
    ¬ Module.Finite ℝ (TestCompletion K) := by
  intro h
  have := h
  have := (coordinates_linearlyIndependent K).finite
  exact not_finite I

end TestSeparable


end BoundedTreePotentials

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedTreePotentials.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
open scoped Classical

namespace TreeCalculus
/-- Completeness, separability and infinite dimension for every literal test-norm completion. -/


theorem four_completed_space_oai (r : Bool) (k : QuadraticKind) :
    CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
    TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
    ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k)) := by
  exact ⟨inferInstance,inferInstance,testCompletion_infiniteDimensional _⟩
end TreeCalculus
end BoundedTreePotentials

end

end OAI
end

theorem solution : type_of% @OAI.BoundedTreePotentials.TreeCalculus.four_completed_space_oai := @OAI.BoundedTreePotentials.TreeCalculus.four_completed_space_oai

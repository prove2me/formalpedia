-- Prove2me | solution 1 for OAI.EditApproximation.physicalRefinement_zero_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:30.96133+00:00
-- url     : https://prove2.me/submissions/59a29911-c766-4855-94e7-6b78eb44e5a6

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity, exact zero states and spatial regularity of the full stage. -/

namespace EditApproximation

theorem physicalRefinement_nonneg {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  have h := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q).1
  have hzero : 0 ≤ physicalLower source target (refinementFactor A F : ℝ) (node, q) :=
    (abs_nonneg _).trans (le_max_right _ _)
  exact (Rat.cast_nonneg (K := ℝ)).mp (hzero.trans h)

theorem physicalRefinement_zero_cost_oai {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length)
    (hcost : stateEditCost (physicalSource source node) target q = 0) :
    physicalRefinement source target U N P F A T delta choices node t q = 0 := by
  have hb := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q
  have hu := hb.2.1.trans (hb.2.2.1.trans (hb.2.2.2.1.trans hb.2.2.2.2))
  rw [hcost] at hu
  simp only [Nat.cast_zero, mul_zero] at hu
  exact le_antisymm hu (physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q)

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalRefinement_zero_cost_oai.{u_1} := @OAI.EditApproximation.physicalRefinement_zero_cost_oai.{u_1}

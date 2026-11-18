-- Prove2me | solution 1 for OAI.EditApproximation.stageWarmupMass_child_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:44:18.711212+00:00
-- url     : https://prove2.me/submissions/10a47333-5612-41a0-a7a5-0599708b309b

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stage masses and representatives supply the comparison-node warmup hypotheses. -/

namespace EditApproximation

theorem stageWarmupMass_child_lower_oai {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J) :
    ∀ i s, max ((stateEditCost
      (substring source (sourceChild (physicalSourceInterval source.length node) i).lo
        (sourceChild (physicalSourceInterval source.length node) i).hi) target s : ℝ) /
          (refinementFactor A F : ℝ))
      |stateLengthGap (substring source (sourceChild (physicalSourceInterval source.length node) i).lo
        (sourceChild (physicalSourceInterval source.length node) i).hi) target s| ≤
      (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ) := by
  intro i s
  have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
    (physicalChild node hbelow i, s)
  have hmass : (stageWarmup source target U N P F A T (physicalChild node hbelow i, s) : ℝ) ≤
      stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) := Rat.cast_le.mpr h.2.1
  exact h.1.trans hmass

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.stageWarmupMass_child_lower_oai.{u_1} := @OAI.EditApproximation.stageWarmupMass_child_lower_oai.{u_1}

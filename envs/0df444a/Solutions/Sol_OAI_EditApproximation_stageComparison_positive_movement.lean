-- Prove2me | solution 1 for OAI.EditApproximation.stageComparison_positive_movement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:45.443893+00:00
-- url     : https://prove2.me/submissions/1efe8ad8-86f9-4504-aa36-0ca040cbc0a1

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonEnergy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual averaged warmup supplies the local mass and energy charges. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

include hM hsize hP hF hA hseed hT hc in
/-- The rounded representative has positive true cost, and its movement is
smaller than the actual parent averaged warmup mass. -/
theorem stageComparison_positive_movement_oai
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    0 < stateEditCost (physicalSource source node) target r ∧
      (targetEndpointDistance q r : ℝ) ≤ stageWarmupMass source target U N P F A T (node, q) := by
  dsimp only
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let r := roundInterval (seedGridSpacing b P) q
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let e : ℝ := targetEndpointDistance q r
  let a : ℝ := refinementFactor A F
  have ha : 1 ≤ a := by
    dsimp only [a]
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have ha0 : 0 < a := by linarith only [ha]
  have hc0 : 0 < c := by dsimp only [c]; exact_mod_cast hc
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have hb : (b : ℝ) ≤ c := by
    dsimp only [b, c]
    exact_mod_cast (cost_dyadicScale _ _ hc le_rfl).2.1
  have herror : e * (P : ℝ) ≤ 2 * (b : ℝ) := by
    dsimp only [e, r]
    exact_mod_cast rounded_seedGrid_error b P (by omega) q
  have hPfour : (4 : ℝ) ≤ P := by exact_mod_cast (show 4 ≤ P by omega)
  have hmul := mul_le_mul_of_nonneg_left hPfour he0
  have hhalf : e ≤ c / 2 := by nlinarith only [hmul, herror, hb]
  have hspatial : c ≤ stateEditCost (physicalSource source node) target r + e := by
    dsimp only [c, e]
    exact_mod_cast stateEditCost_spatial (physicalSource source node) target q r
  have hsmall : e ≤ c / a := by
    have h := mul_le_mul_of_nonneg_left hscale he0
    apply (le_div_iff₀ ha0).2
    nlinarith only [h, herror, hb]
  have hinv := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hlower : c / a ≤ (stageWarmupMass source target U N P F A T (node, q) : ℝ) :=
    ((le_max_left _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
  exact ⟨by exact_mod_cast (show (0 : ℝ) < stateEditCost (physicalSource source node) target r by linarith),
    hsmall.trans hlower⟩

end Stage

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.stageComparison_positive_movement_oai.{u_1} := @OAI.EditApproximation.stageComparison_positive_movement_oai.{u_1}

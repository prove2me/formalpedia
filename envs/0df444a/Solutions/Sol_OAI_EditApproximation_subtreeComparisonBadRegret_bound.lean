-- Prove2me | solution 1 for OAI.EditApproximation.subtreeComparisonBadRegret_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:47:01.083415+00:00
-- url     : https://prove2.me/submissions/7c55d7cd-5f20-4a8d-ab63-7345809325ea

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalNode_generic_regret
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_zero_cost
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants
import Theorems.Thm_OAI_EditApproximation_subtreeComparisonCharges_local
import Theorems.Thm_OAI_EditApproximation_subtreeComparisonCharges_total

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- Exceptional-node cost uses the total curvature/discrepancy charge;
no count of nodes or independence assumption is needed. -/
theorem bad_node_cost_from_curvature {ι : Type*} (nodes : Finset ι)
    (cost scale curvature discrepancy : ι → ℝ) (ratio totalBound : ℝ)
    (hratio : 0 ≤ ratio)
    (hcost : ∀ i ∈ nodes, cost i ≤ 2 * scale i)
    (hcurvature : ∀ i ∈ nodes, 0 ≤ curvature i)
    (hdiscrepancy : ∀ i ∈ nodes, 0 ≤ discrepancy i)
    (htotal : (∑ i ∈ nodes, (curvature i + discrepancy i)) ≤ totalBound) :
    (∑ i ∈ nodes with scale i < ratio * curvature i ∨ scale i < ratio * discrepancy i,
      cost i) ≤ 2 * ratio * totalBound := by
  classical
  let bad := nodes.filter fun i => scale i < ratio * curvature i ∨
    scale i < ratio * discrepancy i
  have hpoint (i : ι) (hi : i ∈ bad) : cost i ≤ 2 * ratio * (curvature i + discrepancy i) := by
    obtain ⟨hinode, hbad⟩ := mem_filter.mp hi
    have hK := mul_nonneg hratio (hcurvature i hinode)
    have hG := mul_nonneg hratio (hdiscrepancy i hinode)
    rcases hbad with hbad | hbad <;> nlinarith [hcost i hinode]
  have hpartial : (∑ i ∈ bad, (curvature i + discrepancy i)) ≤
      ∑ i ∈ nodes, (curvature i + discrepancy i) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro i hi _
    exact add_nonneg (hcurvature i hi) (hdiscrepancy i hi)
  have hsum := sum_le_sum hpoint
  rw [← mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (hpartial.trans htotal) (by positivity))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

theorem comparisonChildren_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
      target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) ≤
        (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  (Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)).2.2.2.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonPhysical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Active comparison states have precisely the corresponding physical source interval. -/

namespace EditApproximation

theorem comparisonStep_active_parent {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) (i : Fin M)
    (resultParent : TargetInterval source.length) (resultQ : TargetInterval target.length)
    (heq : comparisonStep source target hM P hP node i = some (resultParent, resultQ))
    (hactive : ¬ comparisonStopped source target resultParent resultQ) :
    ∃ parent q, node = some (parent, q) ∧ ¬ comparisonStopped source target parent q ∧
      resultParent = sourceChild parent i := by
  classical
  cases node with
  | none => cases heq
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs] at heq
      split_ifs at heq with hi
      · have hpq := Option.some.inj heq
        have hp : parent = resultParent := congrArg Prod.fst hpq
        have hq : q = resultQ := congrArg Prod.snd hpq
        exact False.elim (hactive (by rw [← hp, ← hq]; exact hs))
    · simp only [comparisonStep, dite_eq_right hs] at heq
      have hpq := Option.some.inj heq
      have hp : sourceChild parent i = resultParent := congrArg Prod.fst hpq
      exact ⟨parent, q, rfl, hs, hp.symm⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLift
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual physical tables on the stopped comparison tree. Stopped states retain
their exact cost while the complete-tree representation carries them forward.
-/

namespace EditApproximation

open Finset

theorem stoppedComparisonValue_physical {α : Type*} {M J : ℕ} (source target : List α)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    stoppedComparisonValue source target (fun r => table (node, r))
      (some (physicalSourceInterval source.length node, q)) = table (node, q) := by
  classical
  unfold stoppedComparisonValue
  dsimp only
  split_ifs with hstop
  · exact (hterminal node q hstop).symm
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





theorem physicalRefinement_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rw [physicalRefinement]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  split_ifs <;>
    simp only [stageInitial, physicalInitialTable, ite_eq_left hlength,
      shortSourceCost_eq_edit _ _ hlength] <;> rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalGenericRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic regret bound for the actual complete physical recurrence. -/

namespace EditApproximation

open Finset

section Node

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (hleaf : ¬ (physicalSourceInterval source.length node).hi -
    (physicalSourceInterval source.length node).lo ≤ 1)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

local notation "parent" => physicalSourceInterval source.length node
local notation "b" => 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
local notation "r" => roundInterval (seedGridSpacing b P) q
local notation "action" => comparisonChildren source target hM P hP parent q hc
local notation "mass" => fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
local notation "W" => comparisonActionMass action mass
local notation "value" => fun t (s : PhysicalEntry M J target.length) =>
  (physicalRefinement source target U N P F A T delta choices (Prod.fst s) t (Prod.snd s) : ℝ)
local notation "regret" => fun t =>
  max (stateEditCost (physicalSource source node) target q : ℝ) (value (t + 1) (node, q)) -
    (128 * (F : ℝ)) * targetEndpointDistance q r -
    physicalComparisonClipped source target U N P F A T delta choices node hbelow action (t + 1)

include hsize hF hA hseed hT in
 theorem physicalComparison_mass_upper (hMP : 4 * (M : ℝ) / P ≤ 1) :
    W ≤ 4 * F * stateEditCost (physicalSource source node) target q := by
  have hcost := comparisonChildren_cost_bound source target hM P hP parent q hc
  change (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
    (1 + 4 * (M : ℝ) / P) * stateEditCost (physicalSource source node) target q at hcost
  have hsum : W ≤ 2 * (F : ℝ) * ∑ i,
      (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ) := by
    change (∑ i, mass i (action i)) ≤ _
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
      (physicalChild node hbelow i, action i)
    have hQ := h.2.2.1.trans h.2.2.2
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hQ
  have hfactor := mul_le_mul_of_nonneg_left hcost (show (0 : ℝ) ≤ 2 * F by positivity)
  have hcost0 : (0 : ℝ) ≤ stateEditCost (physicalSource source node) target q := Nat.cast_nonneg _
  have hfactor2 := mul_le_mul_of_nonneg_right hMP hcost0
  have hfactor3 := mul_le_mul_of_nonneg_left hfactor2 (show (0 : ℝ) ≤ 2 * F by positivity)
  nlinarith only [hsum, hfactor, hfactor3]

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_generic_regret_upper (hMP : 4 * (M : ℝ) / P ≤ 1) (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤ 4 * F * stateEditCost (physicalSource source node) target q := by
  exact (physicalNode_generic_regret source target hM U N P F A hsize hP hF hA hseed T hT delta choices node
    hbelow hleaf q hc S).trans ((sub_le_self _ (abs_nonneg _)).trans
      (physicalComparison_mass_upper source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hMP))

end Node

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageTerminal
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Warmup masses and refinement values equal the true cost at stopped states. -/

namespace EditApproximation

theorem physicalRefinement_at_stopped {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rcases hstop with hleaf | hcost
  · exact physicalRefinement_at_leaf source target U N P F A T delta choices node hleaf t q
  · rw [physicalRefinement_zero_cost source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices node t q hcost]
    rw [show stateEditCost (physicalSource source node) target q = 0 from hcost, Nat.cast_zero]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison paths below an arbitrary physical node retain their original
global table labels. No refinement program or random law is changed. -/

namespace EditApproximation

theorem physicalSubtreeNode_child {M J : ℕ} (root : PhysicalNode M J)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (i : Fin M) :
    physicalChild (physicalSubtreeNode root d path hd.le) hd i =
      physicalSubtreeNode root (d + 1) (path, i) (by omega) := rfl

theorem comparisonSubtree_active_source {α : Type*} (source target : List α)
    {M J : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path = some (parent, q))
    (hactive : ¬ comparisonStopped source target parent q) :
    parent = sourceIntervalAt M source.length (root.1.val + d) (treeLayerAppend root.2 d path) := by
  induction d generalizing parent q with
  | zero =>
    exact (congrArg Prod.fst (Option.some.inj heq)).symm
  | succ d ih =>
    obtain ⟨previousParent, previousQ, hprevious, hpreviousActive, hchild⟩ :=
      comparisonStep_active_parent source target hM P hP _ path.2 parent q heq hactive
    rw [ih path.1 previousParent previousQ hprevious hpreviousActive] at hchild
    exact hchild

theorem comparisonSubtreeLift_step_active {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (hd : root.1.val + d < J) (q : TargetInterval target.length)
    (hfrontier : comparisonFrontier source target hM P hP
      (some (physicalSourceInterval source.length root, rootQ)) d path =
        some (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d path hd.le)) q) (i : Fin M) :
    let node := physicalSubtreeNode root d path hd.le
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    comparisonSubtreeLift source target hM P hP table root rootQ (d + 1) (path, i) =
      table (physicalChild node hd i,
        comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i) := by
  classical
  dsimp only
  unfold comparisonSubtreeLift
  rw [dite_eq_left (by omega : root.1.val + (d + 1) ≤ J)]
  change stoppedComparisonValue source target _
    (comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP _ d path) i) = _
  rw [hfrontier]
  simp only [comparisonStep, dite_eq_right hactive]
  rw [← physicalSubtreeNode_child root d path hd i]
  exact stoppedComparisonValue_physical source target table hterminal _ _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonBad
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional comparison-node costs are bounded by the actual global curvature charge. -/

namespace EditApproximation

open Finset

theorem comparisonActiveCost_scale {α : Type*} (source target : List α)
    (state : ComparisonState source.length target.length) :
    comparisonActiveScale source target state ≤ comparisonActiveCost source target state ∧
      comparisonActiveCost source target state ≤ 2 * comparisonActiveScale source target state := by
  classical
  cases state with
  | none => simp only [comparisonActiveScale, comparisonActiveCost, mul_zero, le_refl, and_self]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [comparisonActiveScale, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl, and_self]
    · have hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q := by
        unfold comparisonStopped at hstop
        omega
      have hb := cost_dyadicScale _ _ hc le_rfl
      simp only [comparisonActiveScale, comparisonActiveCost, ite_eq_right hstop]
      exact ⟨by exact_mod_cast hb.2.1, by exact_mod_cast hb.2.2.le⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeBad
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (root : PhysicalNode M J) (K : ℕ)
  (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))

include hsize hF hA hseed hT in
 theorem subtreeComparisonBadCost_bound (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hcapacity : source.length ≤ M ^ J)
    (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    subtreeComparisonBadCost source target hM U N P F A hP T root K hheight rootQ ratio ≤
      10000 * ratio * F * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  classical
  let ι := Σ d : Fin K, TreeLayer M d.val
  let cost : ι → ℝ := fun v => comparisonActiveCost source target (frontier v.1.val v.2)
  let scale : ι → ℝ := fun v => comparisonActiveScale source target (frontier v.1.val v.2)
  let curvature : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1
  let G : ι → ℝ := fun v => (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2
  have h := bad_node_cost_from_curvature (univ : Finset ι) cost scale curvature G ratio _ hratio
    (fun v _ => (comparisonActiveCost_scale source target _).2)
    (fun v _ => (subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale v.1 v.2).1)
    (fun v _ => (subtreeComparisonCharges_local source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale v.1 v.2).2.1)
    (subtreeComparisonCharges_total source target hM U N P F A hsize hP hF hA hseed
      T hT root K hheight rootQ hscale hcapacity hsmall)
  change subtreeComparisonBadCost source target hM U N P F A hP T root K hheight rootQ ratio ≤ _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

include hM hsize hP hF hA hseed hT in
 theorem physicalClippedTable_at_stopped (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) (t : ℕ) :
    physicalClippedTable source target U N P F A T delta choices t (node, q) =
      stateEditCost (physicalSource source node) target q := by
  have h := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q hstop
  simp only [physicalClippedTable, h, Rat.cast_natCast, max_self]

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (root : PhysicalNode M J) (K : ℕ) (hheight : root.1.val + K = J) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (physicalSourceInterval source.length root, rootQ))
local notation "lifted" => subtreeClippedLift source target hM U N P F A hP T delta choices root rootQ

 theorem subtreeComparisonTreeRegret_none (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (heq : frontier d.val path = none) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  have hnext (i : Fin M) : frontier (d.val + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d.val path) i = none
    rw [heq]
    rfl
  simp only [subtreeComparisonTreeRegret, subtreeClippedLift, comparisonSubtreeLift, heq, hnext,
    stoppedComparisonValue, comparisonMovement, mul_zero, sub_self, sum_const_zero]

 theorem subtreeComparisonTreeRegret_stopped (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d.val path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = 0 := by
  classical
  have hpoint (i : Fin M) : lifted (t + 1) (d.val + 1) (path, i) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    unfold subtreeClippedLift comparisonSubtreeLift
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d.val path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  unfold subtreeComparisonTreeRegret
  simp_rw [hpoint]
  simp only [subtreeClippedLift, comparisonSubtreeLift, heq, stoppedComparisonValue, ite_eq_left hstop,
    comparisonMovement, mul_zero, sub_zero, sum_ite_eq', mem_univ, ite_true, if_true, sub_self]

include hsize hF hA hseed hT in
 theorem subtreeComparisonTreeRegret_active (t : ℕ) (d : Fin K) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega)), q))
    (hactive : ¬ comparisonStopped source target
      (physicalSourceInterval source.length (physicalSubtreeNode root d.val path (by omega))) q) :
    let node := physicalSubtreeNode root d.val path (by omega)
    let hbelow : node.1.val < J := by dsimp only [node, physicalSubtreeNode]; omega
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      dsimp only [node]
      unfold comparisonStopped at hactive
      omega
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q
    subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path =
      max (stateEditCost (physicalSource source node) target q : ℝ)
        (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
          (128 * (F : ℝ)) * targetEndpointDistance q r -
          physicalComparisonClipped source target U N P F A T delta choices node hbelow
            (comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc) (t + 1) := by
  classical
  dsimp only
  have hnext (i : Fin M) := comparisonSubtreeLift_step_active source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices (t + 1))
    (fun label s hstop => physicalClippedTable_at_stopped source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices label s hstop (t + 1)) root rootQ d.val path (by omega) q heq hactive i
  have hcurrent : comparisonSubtreeLift source target hM P hP
      (physicalClippedTable source target U N P F A T delta choices (t + 1)) root rootQ d.val path =
      physicalClippedTable source target U N P F A T delta choices (t + 1)
        (physicalSubtreeNode root d.val path (by omega), q) := by
    unfold comparisonSubtreeLift
    rw [heq]
    simp only [stoppedComparisonValue, ite_eq_right hactive]
    rw [dite_eq_left (by omega : root.1.val + d.val ≤ J)]
  have hmovement : comparisonMovement source target P (frontier d.val path) =
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (physicalSource source (physicalSubtreeNode root d.val path (by omega))) target q)) P) q) := by
    rw [heq]
    simp only [comparisonMovement, ite_eq_right hactive]
    rfl
  unfold subtreeComparisonTreeRegret subtreeClippedLift
  rw [hcurrent, hmovement]
  simp_rw [hnext]
  rfl

include hsize hF hA hseed hT hheight in
 theorem subtreeComparisonTreeRegret_generic (hMP : 4 * (M : ℝ) / P ≤ 1)
    (S : ℕ) (d : Fin K) (path : TreeLayer M d.val) :
    (∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path) ≤
      4 * F * comparisonActiveCost source target (frontier d.val path) := by
  classical
  generalize heq : frontier d.val path = state
  cases state with
  | none =>
    simp only [subtreeComparisonTreeRegret_none source target hM U N P F A hP T delta choices root K rootQ
      _ d path heq, sum_const_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · simp only [subtreeComparisonTreeRegret_stopped source target hM U N P F A hP T delta choices root K rootQ
        _ d path parent q heq hstop, sum_const_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonSubtree_active_source source target hM P hP root rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := physicalSubtreeNode root d.val path (by omega)
      have hp' : parent = physicalSourceInterval source.length node := hp
      subst parent
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
          (physicalSourceInterval source.length node).hi) target q
        change ¬ ((physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 ∨
            stateEditCost (substring source (physicalSourceInterval source.length node).lo
              (physicalSourceInterval source.length node).hi) target q = 0) at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      have h := physicalNode_generic_regret_upper source target hM U N P F A hsize hP hF hA hseed T hT
        delta choices node (by dsimp only [node, physicalSubtreeNode]; omega) hleaf q hc hMP S
      have hpoint (t : ℕ) : subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t d path = _ :=
        subtreeComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta choices root K hheight rootQ t d path q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target
          (sourceIntervalAt M source.length (root.1.val + d.val) (treeLayerAppend root.2 d.val path)) q := hstop
      simpa only [comparisonActiveCost, ite_eq_right hstop', physicalSource, physicalSourceInterval,
        node, physicalSubtreeNode] using h

include hsize hF hA hseed hT in
 theorem subtreeComparisonBadRegret_bound_oai (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) (S : ℕ) :
    (∑ v : (Σ d : Fin K, TreeLayer M d.val) with
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) <
        ratio * (subtreeComparisonCharges source target hM U N P F A hP T root K hheight rootQ v.1 v.2).2,
      ∑ t ∈ range S, subtreeComparisonTreeRegret source target hM U N P F A hP T delta choices root K rootQ t v.1 v.2) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (K : ℝ) / P + (K : ℝ) / T) *
        comparisonStateCost source target (some (physicalSourceInterval source.length root, rootQ)) := by
  classical
  have htotal := subtreeComparisonBadCost_bound source target hM U N P F A hsize hP hF hA hseed
    T hT root K hheight rootQ ratio hratio hscale hcapacity hsmall
  have hpoint := fun (v : Σ d : Fin K, TreeLayer M d.val) =>
    subtreeComparisonTreeRegret_generic source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices root K hheight rootQ hMP S v.1 v.2
  apply (sum_le_sum (fun v _ => hpoint v)).trans
  rw [← mul_sum]
  have h := mul_le_mul_of_nonneg_left htotal (show (0 : ℝ) ≤ 4 * F by positivity)
  unfold subtreeComparisonBadCost at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Tree

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.subtreeComparisonBadRegret_bound_oai.{u_1} := @OAI.EditApproximation.subtreeComparisonBadRegret_bound_oai.{u_1}

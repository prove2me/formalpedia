-- Prove2me | solution 1 for OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:33.564254+00:00
-- url     : https://prove2.me/submissions/c0ad79bc-eeaa-4211-9f67-e91666c0bebd

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_queryChargedFamilyTable_work_bound
import Theorems.Thm_OAI_EditApproximation_queryFamilyBoundedActive_work_bound

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cell-keyed shared draws permit direct local group enumeration. The
complete and local finite programs use the same draw at every cell label. -/

namespace EditApproximation

theorem targetCell_of_cellTargetStates {n g : ℕ} {side : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (hside : 0 < side) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n g side cell) : targetCell side r = cell := by
  have hc := (cellTargetStates_mem cell hg r).mp hr
  apply Prod.ext
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.1⟩
  · apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hside.le)).2
    exact ⟨(le_div_iff₀ hside).2 hc.2.2.2.2.1, (div_lt_iff₀ hside).2 hc.2.2.2.2.2⟩

theorem chooseCellGroupAction_center {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell draw = some action) :
    action.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  exact (unskippedBandList_mem_iff _ _).mp
    (chooseUnskippedGroup_spec Q current _ hempty draw).1

theorem representativeCells_mem {n N P F b : ℕ} (a theta : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hr : (b, r) ∈ representativeList N P F a initial) :
    targetCell (theta * b) r ∈ representativeCells N P F b a theta initial := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  exact ⟨(b, r), List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩



section CellPrograms

variable {α : Type*} {M : ℕ} (source target : List α)
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q)

local notation "theta" => (2 : ℚ) ^ (-(exponent : ℤ))



theorem cellGroupAction_location (b : ℕ) (hb : b ∈ dyadicScales N) (cell : ℕ × ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : chooseCellGroupAction source target parent b P F exponent Q tau a
      parentInitial child initial current cell (draw b cell) = some action) :
    (b, action.center) ∈ representativeList N P F a parentInitial ∧
      targetCell (theta * b) action.center = cell := by
  have hcenter := chooseCellGroupAction_center source target parent b P F exponent Q tau a
    parentInitial child initial current cell (draw b cell) action hselected
  have hrep := cellRepresentativeStates_mem_representatives a parentInitial theta cell action.center hb hcenter
  have hbpos : 0 < b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    positivity
  have hcell := (List.mem_filter.mp hcenter).1
  exact ⟨hrep, targetCell_of_cellTargetStates cell (by unfold seedGridSpacing; omega)
    (by positivity) action.center hcell⟩

theorem localCellGroupActions_subset (q : TargetInterval target.length) :
    ∀ action ∈ localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q,
      action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  have hb' := (List.mem_filter.mp hb).1
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb' cell action hselected
  have hcell := representativeCells_mem a theta parentInitial action.center hlocation.1
  rw [hlocation.2] at hcell
  exact List.mem_flatMap.mpr ⟨b, hb', List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩⟩

theorem completeCellGroupActions_wide :
    ∀ action ∈ completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw,
      action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  intro action ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp ha
  exact chooseCellGroupAction_wide_mem source target parent N b P F exponent Q tau a parentInitial
    child initial current cell (draw b cell) hb action hselected

end CellPrograms

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalWideStep
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One concrete refinement entry, using direct local representative and
cell loops. Band data and previously gathered child tables are arguments;
no complete current-index child table is enumerated. -/

namespace EditApproximation

theorem rationalLocalWideStep_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) (hdelta : 0 ≤ delta) (hinitial : 0 ≤ parentInitial q)
    (hold : ∀ i r, 0 ≤ old i r) (hcurrent : ∀ i r, 0 ≤ current i r) :
    0 ≤ rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ∧
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ≤ parentInitial q := by
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun is => old is.1 is.2) q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
  let cone := rationalMinimum fallback
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (fun is => current is.1 is.2) q))
  have hfallback : 0 ≤ fallback := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hinitial, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action ha) (fun i => hold _ _)
  have hgroups : ∀ action ∈ groups, action ∈
      rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
    intro action ha
    exact completeCellGroupActions_wide source target parent N P F exponent Q tau a parentInitial
      childMass childInitial current draw action
      (localCellGroupActions_subset source target parent N P F exponent Q tau a parentInitial
        childMass childInitial current draw q action ha)
  have hcone : 0 ≤ cone := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hfallback, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action (hgroups action ha)) (fun i => hcurrent _ _)
  have hupper : cone ≤ parentInitial q := (rationalMinimum_le_fallback _ _).trans
    (rationalMinimum_le_fallback _ _)
  change 0 ≤ rationalRefinementUpdate delta cone _ ∧ rationalRefinementUpdate delta cone _ ≤ parentInitial q
  cases hmin : rationalOnlineMinimum (online.map
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => current is.1 is.2) q)) with
  | none => exact ⟨hcone, hupper⟩
  | some value =>
    exact ⟨le_min hcone ((div_nonneg hcone (by linarith)).trans (le_max_left _ _)),
      (min_le_left _ _).trans hupper⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal warmup can be calculated by direct bounded endpoint
loops. Equality with the complete tables is only asserted on good seeds;
the local rules themselves remain finite and bounded on every seed. -/

namespace EditApproximation

open Finset

theorem physicalLocalWarmup_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (state : PhysicalEntry M J target.length) :
    0 ≤ physicalLocalWarmup source target U N P F A t state ∧
      physicalLocalWarmup source target U N P F A t state ≤ stageInitial source target U N P F A state := by
  induction t generalizing state with
  | zero => exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
  | succ t ih =>
    rw [physicalLocalWarmup]
    split_ifs
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩
    · refine ⟨?_, rationalMinimum_le_fallback _ _⟩
      apply (le_rationalMinimum_iff _ _ _).2
      refine ⟨stageInitial_nonneg_all_seeds source target U N P F A state, ?_⟩
      intro v hv
      obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
      unfold rationalActionValue
      apply add_nonneg
      · exact add_nonneg (by positivity)
          (rationalActualWideActions_connection_nonneg _ _ _ action ha)
      · exact Finset.sum_nonneg (fun i _ => (ih _).1)
    · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A state, le_rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local finite refinement recurrence, with direct query groups and
local warmup data. Current-index dependencies go only to physical children;
the recurrence is well founded before any accuracy assertion. -/

namespace EditApproximation

theorem physicalLocalRefinement_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ) (hdelta : 0 ≤ delta)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ∧
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ≤
        stageInitial source target U N P F A (node, q) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
  · cases t with
    | zero => exact physicalLocalWarmup_bounds source target U N P F A T (node, q)
    | succ t =>
      let children : PhysicalChildTables M target.length := fun i =>
        physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online
          (physicalChild node hbelow i)
      have hold (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i t r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) t r).1
      have hcurrent (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i (t + 1) r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) (t + 1) r).1
      exact rationalLocalWideStep_bounds source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (t + 1)) (online node children (t + 1) q) q hdelta
        (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hold hcurrent
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

theorem queryRestrictedPhysicalOracle_table
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.val.combinedRank T S})
    (hb : child.val.Bounded passes copies T S) :
    queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child) =
      oracle (Sum.inr ⟨⟨child.val, hb⟩, child.property⟩) := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  rw [dite_eq_left ((querySupportedChildWithWork_value passes copies T S parent (Sum.inr child)).mpr hb)]
  rfl

end Body
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistorySemantic
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section History
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial
local notation "seed" pass => localSeedSequence source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial pass

theorem localRequestValue_bounds (hdelta : 0 ≤ delta) (request : PhysicalTableRequest M J target.length) :
    0 ≤ requestValue request ∧ requestValue request ≤
      stageInitial source target (seed request.pass) N P F (factor request.pass) (request.node, request.state) := by
  unfold localRequestValue unifiedPhysicalValue
  dsimp only
  split
  · exact physicalLocalWarmup_bounds source target _ N P F _ _ _
  · exact physicalLocalRefinement_bounds source target _ N P F exponent Q _ tau delta T hdelta _ _ _ _ _

theorem queryPhysicalEarlierRead_history_bound
    (passes pass copy t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies) (hdelta : 0 ≤ delta)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval target.length)
    (oracle : {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
    (hread : ∀ key, key.val.Bounded passes copies T S → (oracle key).value = requestValue key.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).value ≤
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value oracle).value := by
  have hinit :
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value oracle).value =
      stageInitial source target (seed pass) N P F (factor pass)
        (physicalChild node hbelow input.1, input.2.2) := by
    change (oracle _).value = _
    rw [hread _ ⟨hpass, hcopy, Nat.zero_le _⟩]
    rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy _ 0 (Nat.zero_le T)]
    rfl
  rw [hinit]
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · rename_i htime
    have htime' := (binaryNaturalCompareWithWork_lt _ _).mp htime
    change (oracle _).value ≤ _
    rw [hread _ ⟨hpass, hcopy, by change T + input.2.1 ≤ T + S; omega⟩]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial hdelta _).2
  · simp only [BitQuery.value, BinaryFraction.nat_value, Nat.cast_zero]
    exact stageInitial_nonneg_all_seeds source target (seed pass) N P F (factor pass) _

end History
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySemanticRestriction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section History
variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial

theorem queryRestrictedPhysicalOracle_history_bound
    (passes pass copy t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies) (hdelta : 0 ≤ delta)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval target.length)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (heq : parent.val = PhysicalTableRequest.refinement pass copy node T t q)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hread : ∀ key, (oracle (Sum.inr key)).value = requestValue key.val.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    let rawOracle := fun child : {r : PhysicalTableRequest M J target.length // r.combinedRank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} =>
      queryRestrictedPhysicalOracle passes copies T S parent oracle
        (Sum.inr ⟨child.val, by rw [heq]; exact child.property⟩)
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value rawOracle).value ≤
      ((queryPhysicalWarmupRead copies pass copy T S t ht node q
        (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2.2).value rawOracle).value := by
  dsimp only
  apply queryPhysicalEarlierRead_history_bound source target N P F exponent H Q T S copies
    factor multiplier tau eta kappa delta group integer initial passes pass copy t ht htS
    hpass hcopy hdelta node hbelow q _ _ input
  intro child hb
  rw [queryRestrictedPhysicalOracle_table passes copies T S parent oracle _ hb]
  exact hread _

end History
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedSemanticCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section History
variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := σ) (passes + 1) copies T S parent → BinaryFraction)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau eta kappa delta group integer initial
local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
local notation "tableOracle" => (fun key => queryActiveOracle T parent.val hindex S rawOracle (Sum.inr key))

theorem queryFamilyBoundedActive_history_bound (hdelta : 0 ≤ delta)
    (hread : ∀ key, (oracle (Sum.inr key)).value = requestValue key.val.val)
    (input : Fin M × ℕ × TargetInterval target.length) :
    ((queryPhysicalEarlierRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
      parent.val.node hbelow parent.val.state input).value tableOracle).value ≤
    ((queryPhysicalWarmupRead copies parent.val.pass parent.val.copy T S (parent.val.index - T)
      (Nat.sub_pos_of_lt hindex) parent.val.node parent.val.state
      (physicalChild parent.val.node hbelow input.1) (by change parent.val.node.1.val ≤ parent.val.node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2.2).value tableOracle).value := by
  have ht : parent.val.index - T ≤ S := by have := parent.property.2.2; omega
  have h := queryRestrictedPhysicalOracle_history_bound source target N P F exponent H Q T S copies
    factor multiplier tau eta kappa delta group integer initial (passes + 1) parent.val.pass parent.val.copy
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) ht parent.property.1 parent.property.2.1 hdelta
    parent.val.node hbelow parent.val.state parent (queryRefinementRequest_eq T parent.val hindex).symm
    oracle hread input
  exact h

end History
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryTableSemanticCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local irreducible] queryFamilyBoundedActive queryFamilyActive queryFamilyRefinement
  queryPhysicalRandomDataRequest queryLocalProgram localRequestValue
open BinaryFraction

section Table
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF Amax B E Scale V C : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (oracle : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → BinaryFraction)
  (readWork : ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent) → ℕ)
  (factor : ℕ → ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "requestValue" => localRequestValue source target N P F exponent H Q T S copies
  factor multiplier tau.value eta.value kappa.value delta.value group integer initial
local notation "activeBudget" => queryLocalProgramBitBudget M N P F exponent eM eF B Scale (parent.val.index - T)
  (queryPhysicalDataBudget T J B V (50 * B + 21 + (C + 1) + 1)
    (queryFamilySourceReadBudget J B (50 * B + 21 + (C + 1) + 1 + 1)))

theorem queryChargedFamilyTable_semantic_work_bound_oai
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
      tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
    (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hJ : Nat.size J ≤ B) (hi : Nat.size parent.val.index ≤ B)
    (hT : Nat.size T ≤ B) (hS : Nat.size S ≤ B)
    (hrank : Nat.size (parent.val.combinedRank T S) ≤ B)
    (hA : (A parent.val.pass).width ≤ B)
    (hAone : 1 ≤ (A parent.val.pass).value) (hAmax : (A parent.val.pass).value ≤ Amax)
    (hp : Nat.size parent.val.pass ≤ B) (hcopy : Nat.size parent.val.copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hc : ∀ key, readWork key ≤ C) (hdelta : 0 ≤ delta.value)
    (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        r.val.combinedRank T S < parent.val.combinedRank T S},
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
        requestValue child.val.val) :
    (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).work oracle readWork ≤
        queryChargedTableBitBudget M P F Amax copies J symbolBits positionBits B C activeBudget := by
  have hMb : Nat.size M ≤ B := by have := hn.aritySize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  apply queryChargedFamilyTable_work_bound source target N P F exponent H Q eM eF Amax B C activeBudget
    hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent oracle readWork
    hn.largeBits hn.inputSize hn.precisionSize hn.factorSize hFpos hn.sourceSize hn.targetSize ht' hinit
    hMb hJ hi hT hA hn.factorWidth hAone hAmax hp hm (fun key => (hv key).trans hVB) hc
  intro hindex hbelow
  apply queryFamilyBoundedActive_work_bound source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow _ _ V (C + 1) hn
    ((Nat.size_le_size (Nat.sub_le _ _)).trans hi) hPd hV hVB hMean
  · intro key
    have h := hc (Sum.map id (fun child =>
      ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩) key)
    omega
  · intro key
    exact hv _
  · exact hsv
  · intro child
    change (oracle (Sum.inr ⟨Sum.inr child.val, _⟩)).value ≥ 0
    rw [hread child]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau.value eta.value kappa.value delta.value group integer initial hdelta child.val.val).1
  · exact queryFamilyBoundedActive_history_bound source target N P F exponent H Q T S passes copies
      factor multiplier tau.value eta.value kappa.value delta.value group integer initial parent hindex hbelow
      _ hdelta hread
  · exact hp
  · exact hcopy
  · exact hps
  · exact hcs
  · exact hT
  · exact hS
  · exact hrank
  · exact hbound


end Table
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound_oai := @OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound_oai

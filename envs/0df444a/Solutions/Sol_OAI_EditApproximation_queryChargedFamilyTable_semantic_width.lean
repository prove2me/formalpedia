-- Prove2me | solution 1 for OAI.EditApproximation.queryChargedFamilyTable_semantic_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:35:02.408312+00:00
-- url     : https://prove2.me/submissions/12e43255-0faa-4f11-910a-b840f2ee9809

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
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryLocalRefinement_finish_bounds
import Theorems.Thm_OAI_EditApproximation_queryChargedFamilyTable_width

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's numerical loops executed on Boolean fraction storage.
The value proofs identify the unreduced numerator and denominator, not just
the represented rational. Thus the raw storage bounds apply to this code. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le_storageBits (n : ℕ) : (nat n).width ≤ (nat n).representation.storageBits := by
  rw [nat_representation]
  have hw : (nat n).width = max (Nat.size n) 1 := by
    simp only [nat, width, SignedBinary.ofInt, Int.natAbs_natCast, ← Nat.size_eq_bits_len,
      List.length_cons, List.length_nil]
  rw [hw]
  simp only [UnreducedRational.nat, UnreducedRational.storageBits, Int.natAbs_natCast, Nat.size_one]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedStorage
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial raw storage bounds used by the Boolean numerical loops. -/

namespace EditApproximation
namespace UnreducedRational

open Finset

theorem storageBits_nat (n : ℕ) : (nat n).storageBits = Nat.size n + 2 := by
  simp [nat, storageBits]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUpdateWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bit cost of the actual coordinate update, including construction of
its rational step and complement. -/

namespace EditApproximation
namespace BinaryFraction

theorem nat_width_le (n : ℕ) : (nat n).width ≤ Nat.size n + 2 := by
  have h := nat_width_le_storageBits n
  rw [nat_representation, UnreducedRational.storageBits_nat] at h
  exact h

end BinaryFraction
end EditApproximation

end OAI
end

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite stored-word tables for gathered earlier values. The lookup scan
and the construction of every gathered warmup mean are explicit. -/

namespace EditApproximation
namespace BinaryFraction



theorem gatheredWordLookupWithWork_value {κ : Type*} [DecidableEq κ]
    (equal : κ → κ → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (keys : List κ) (values : List BinaryFraction) (query : κ) :
    (gatheredWordLookupWithWork equal keys values query).1.value =
      finiteAnswerTable keys (values.map BinaryFraction.value) query := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, finiteAnswerTable, nat_value, Nat.cast_zero]
  | cons key keys ih =>
    cases values with
    | nil => simp only [gatheredWordLookupWithWork, List.map_nil, finiteAnswerTable, nat_value, Nat.cast_zero]
    | cons value values =>
      simp only [gatheredWordLookupWithWork, List.map_cons, finiteAnswerTable]
      by_cases h : query = key
      · rw [ite_eq_left ((heq query key).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hx => h ((heq query key).mp hx)), ite_eq_right h]
        exact ih values

theorem gatheredWordLookupWithWork_width {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (keys : List κ) (values : List BinaryFraction) (query : κ)
    (B : ℕ) (hB : 2 ≤ B) (hvalues : ∀ value ∈ values, value.width ≤ B) :
    (gatheredWordLookupWithWork equal keys values query).1.width ≤ B := by
  induction keys generalizing values with
  | nil => exact (nat_width_le 0).trans (by simpa using hB)
  | cons key keys ih =>
    cases values with
    | nil => exact (nat_width_le 0).trans (by simpa using hB)
    | cons value values =>
      simp only [gatheredWordLookupWithWork]
      split_ifs
      · exact hvalues value List.mem_cons_self
      · exact ih values (fun v hv => hvalues v (List.mem_cons_of_mem _ hv))

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery





theorem value_bind {ι α β : Type*} (oracle : ι → BinaryFraction)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)
  | charge steps continuation ih => exact ih

theorem value_collect {ι κ β : Type*} (oracle : ι → BinaryFraction)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).value oracle =
      (next (inputs.map fun key => (reader key).value oracle)).value oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key inputs ih => simp only [collect, value_bind, value, ih, List.map_cons]

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteBufferRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The default-zero finite buffers preserve the nonnegative bounds of
paired initial/history coordinates when the initial buffer covers them. -/

namespace EditApproximation

theorem finiteAnswerTable_nonneg {κ : Type*} [DecidableEq κ]
    (keys : List κ) (values : List ℚ) (query : κ) (hv : ∀ value ∈ values, 0 ≤ value) :
    0 ≤ finiteAnswerTable keys values query := by
  induction keys generalizing values with
  | nil => exact le_rfl
  | cons key keys ih =>
    cases values with
    | nil => exact le_rfl
    | cons value values =>
      unfold finiteAnswerTable
      split_ifs
      · exact hv value List.mem_cons_self
      · exact ih values (fun v h => hv v (List.mem_cons_of_mem _ h))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





theorem queryEraseLoopWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1 = List.eraseDupsBy.loop (· == ·) xs seen := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    have ht : (memberByWithWork equal a seen).1 = seen.any (a == ·) := by
      apply Bool.eq_iff_iff.mpr
      simp only [memberByWithWork_value equal heq, List.any_eq_true, beq_iff_eq]
      exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hab⟩ => hab ▸ hb⟩
    simp only [queryEraseLoopWithWork, ht, ih, List.eraseDupsBy.loop]
    cases seen.any (a == ·) <;> rfl

@[simp] theorem queryEraseWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1 = xs.eraseDups :=
  queryEraseLoopWithWork_value equal heq xs []

theorem queryEraseLoopWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) (hs : seen.Nodup) :
    (queryEraseLoopWithWork equal xs seen).1.Nodup := by
  induction xs generalizing seen with
  | nil => simpa only [queryEraseLoopWithWork, List.nodup_reverse] using hs
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.Nodup
    by_cases h : (memberByWithWork equal a seen).1 = true
    · rw [ite_eq_left h]
      exact ih seen hs
    · rw [ite_eq_right h]
      apply ih
      exact List.nodup_cons.mpr ⟨fun ha => h ((memberByWithWork_value equal heq a seen).mpr ha), hs⟩

theorem queryEraseWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1.Nodup :=
  queryEraseLoopWithWork_nodup equal heq xs [] (by simp)

theorem queryIntervalEqualWithWork_cost {n : ℕ} (a b : TargetInterval n)
    (B : ℕ) (hn : Nat.size n ≤ B) :
    (queryIntervalEqualWithWork a b).2 ≤ 16 * B + 5 := by
  have hl := naturalEqualWithWork_cost a.lo b.lo B
    ((Nat.size_le_size (a.ordered.trans a.valid)).trans hn)
    ((Nat.size_le_size (b.ordered.trans b.valid)).trans hn)
  have hh := naturalEqualWithWork_cost a.hi b.hi B
    ((Nat.size_le_size a.valid).trans hn) ((Nat.size_le_size b.valid).trans hn)
  change _ + _ + 1 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted insertion sorting for the distinct-key lists. The numerical
encoding determines exactly the order used by the reference query. -/

namespace EditApproximation





theorem queryInsertWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).1 = List.orderedInsert r a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [queryInsertWithWork, hle, List.orderedInsert_cons, decide_eq_true_eq]
    split <;> simp only [ih]

theorem querySortWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b)) (xs : List α) :
    (querySortWithWork le xs).1 = xs.insertionSort r := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [querySortWithWork, queryInsertWithWork_value r le hle, ih, List.insertionSort_cons]



theorem queryOrderedInputsWithWork_value {α : Type*} [DecidableEq α]
    (encode : α → ℕ) (hinjective : Function.Injective encode)
    (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b)) (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).1 = orderedInputs encode hinjective xs.toFinset := by
  let : LinearOrder α := LinearOrder.lift' encode hinjective
  have hle' : ∀ a b, (le a b).1 = decide (a ≤ b) := hle
  rw [queryOrderedInputsWithWork, querySortWithWork_value (· ≤ ·) le hle',
    queryEraseWithWork_value equal heq]
  have hd := queryEraseWithWork_nodup equal heq xs
  rw [queryEraseWithWork_value equal heq] at hd
  have hn : (xs.eraseDups.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) xs.eraseDups).nodup_iff.mpr hd
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr
    (List.pairwise_insertionSort (· ≤ ·) xs.eraseDups)
  have hf : (xs.eraseDups.insertionSort (· ≤ ·)).toFinset = xs.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_insertionSort, List.mem_eraseDups]
  rw [hf] at hs
  exact hs.symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputCodes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



theorem queryEncodedLEWithWork_value {α : Type*} (code : α → ℕ × ℕ) (a b : α) :
    (queryEncodedLEWithWork code a b).1 = decide ((code a).1 ≤ (code b).1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryEncodedLEWithWork, wordLEWithWork_value, bitWordValue_bits, decide_eq_true_eq]



@[simp] theorem queryOrderedChildInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1 =
      orderedInputs childInputCode (childInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value childInputCode (childInputCode_injective M n)
    _ _ coordinateEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value]



@[simp] theorem queryOrderedHistoryInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1 =
      orderedInputs historyInputCode (historyInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value historyInputCode (historyInputCode_injective M n)
    _ _ queryHistoryEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawCentersWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryRawCentersWithWork N P F a value q).1 =
      rawRefinementCenters N P F a.value value.value q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P)
      ⌈value.value⌉₊ q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  simp only [queryRawCentersWithWork, queryEraseWithWork_value _ queryIntervalEqualWithWork_value,
    arithmeticFlatMapWithWork_value, seedGridSpacingWithWork_value _ _ hP,
    naturalCeilingWithWork_value, hg, queryScalesWithWork_value, rawRefinementCenters]



@[simp] theorem queryInitialSupportWithWork_value {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1 =
      refinementInitialSupport N P F exponent a.value value.value q := by
  simp only [queryInitialSupportWithWork, queryRawCentersWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value _ _ hP, canonicalMulWithWork_value, inversePowerTwo_value,
    nat_value, queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    localOnlineSourceKeys, List.map_map, refinementInitialSupport]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted representative and child-coordinate lists for adaptive band
data gathers. All initial-table lookups are included in the work counter. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryWideInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryWideInputsWithWork M parent P representatives).1 = wideWarmupInputs parent P representatives := by
  simp only [queryWideInputsWithWork, queryEraseWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    wideChildGridWithWork_value _ _ _ _ _ hP, wideWarmupInputs]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



namespace BinaryFraction



@[simp] theorem queryOnlineIntegerReadWithWork_value {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    (queryOnlineIntegerReadWithWork keys values b q).1 =
      ⌊finiteAnswerTable keys (values.map value) (b, q)⌋₊ := by
  simp only [queryOnlineIntegerReadWithWork, naturalFloorWithWork_value,
    gatheredWordLookupWithWork_value _ queryOnlineKeyEqualWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryChildReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × TargetInterval n)) (values : List BinaryFraction)
    (i : Fin M) (q : TargetInterval n) :
    (queryChildReadWithWork keys values i q).1.value =
      finiteAnswerTable keys (values.map value) (i, q) :=
  gatheredWordLookupWithWork_value _ coordinateEqualWithWork_value keys values (i, q)



@[simp] theorem queryHistoryReadWithWork_value {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) :
    (queryHistoryReadWithWork keys values s input).1.value =
      finiteAnswerTable keys (values.map value) (input.1, s, input.2) :=
  gatheredWordLookupWithWork_value _ queryHistoryEqualWithWork_value keys values (input.1, s, input.2)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite reader budgets for the executable adaptive program. These
uniform bounds follow from stored-key widths, regardless of answer values. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryParentReadWithWork_value {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).1.value = finiteAnswerTable keys (words.map value) r :=
  gatheredWordLookupWithWork_value _ queryIntervalEqualWithWork_value keys words r

theorem queryParentReadWithWork_cost {n : ℕ} (keys : List (TargetInterval n))
    (words : List BinaryFraction) (r : TargetInterval n) :
    (queryParentReadWithWork keys words r).2 ≤ 1 + keys.length * (16 * Nat.size n + 6) := by
  exact gatheredWordLookupWithWork_cost queryIntervalEqualWithWork (16 * Nat.size n + 5)
    (fun a b => queryIntervalEqualWithWork_cost a b _ le_rfl) keys words r

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRawHistoryInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (hP : 0 < P) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryRawHistoryInputsWithWork M parent P history representatives).1) :
    input.2.1 < history := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP] at hi
  obtain ⟨br, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
  exact List.mem_range.mp ht

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBufferCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryEarlierInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1) :
    input.2.1 < history := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value] at hi
  have hm := (mem_orderedInputs historyInputCode (historyInputCode_injective M ny) _ input).mp hi
  rw [List.mem_toFinset] at hm
  exact queryRawHistoryInputsWithWork_time M parent P history hP _ input hm

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalReaderBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Physical
variable {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
  (oracle : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

theorem queryPhysicalEarlierRead_width (B : ℕ) (hB : 2 ≤ B)
    (hw : ∀ key, (oracle key).width ≤ B) (input : Fin M × ℕ × TargetInterval n) :
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).width ≤ B := by
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

end Physical
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceWidths
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem mapKeysWithWork_value {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) :
    (mapKeysWithWork f program).value oracle = program.value (fun key => oracle (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih => exact ih (oracle (f key).1)

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryProgramWidth
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate output widths for the executed adaptive refinement. These
bounds concern the words produced before memo-table normalization. -/

namespace EditApproximation
open BinaryFraction

section Refinement
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalRefinement_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi draw integer q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
  let ew := earlier.map fun key => (readEarlier key).value oracle
  let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
    (parentInitial q).1 q draw).1
  let sw := shared.map fun key => (readCurrent key).value oracle
  let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw shared sw q).1
  let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlier ew q).1
  let keys := (queryNeededInputsWithWork groups online).1
  let cw := keys.map fun key => (readCurrent key).value oracle
  have he : ∀ w ∈ ew, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hew key
  have hcur : ∀ w ∈ cw, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hcw key
  have het : ∀ key ∈ earlier, Nat.size key.2.1 ≤ B := by
    intro key hk
    exact (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a
      parentInitial q key hk).le).trans ht
  have h := (queryLocalRefinement_finish_bounds source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer earlier ew
    shared sw cw q B Rp earlier.length hB hN hnx hny hMb hPb hFb ht ha hd hpw hpr hpn he hcur het
    (Nat.le_refl _)).1
  simpa only [queryLocalRefinement, queryRefinementGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Refinement

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalRandomSources_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let gk := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
  let gw := gk.map fun key => (readGroup key).value oracle
  let ok := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
  let ow := ok.map fun key =>
    (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
  have h := queryLocalRefinement_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial child initial R hc hi (queryGroupDrawReadWithWork gk gw)
    (queryOnlineIntegerReadWithWork ok ow) q readEarlier readCurrent oracle B Rp hB hN hnx hny hMb
    hPb hFb ht ha hd hpw hpr hpn hew hcw
  simpa only [queryLocalRandomSources, queryGroupSourceGather, queryOnlineSourceGather,
    BitQuery.value_bind, BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Sources

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalBand_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let keys := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
  let mw := keys.map fun key => (readMass key).value oracle
  let iw := keys.map fun key => (readInitial key).value oracle
  have h := queryLocalRandomSources_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial (queryChildReadWithWork keys mw)
    (queryChildReadWithWork keys iw) (queryDataReadBudget M target.length keys)
    (queryChildReadWithWork_budget keys mw) (queryChildReadWithWork_budget keys iw)
    q readGroup readInteger readEarlier readCurrent oracle B Rp hB hN hnx hny hMb hPb hFb ht ha hd
    hpw hpr hpn hew hcw
  simpa only [queryLocalBand, queryBandGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Band

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalProgram_width (B : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ key, ((readParent key).value oracle).width ≤ B)
    (hpn : ∀ key, 0 ≤ ((readParent key).value oracle).value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let keys := (queryInitialSupportWithWork N P F exponent hP a ((readParent q).value oracle) q).1
  let words := keys.map fun key => (readParent key).value oracle
  have hw : ∀ w ∈ words, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpw key
  have hn : ∀ r, 0 ≤ (queryParentReadWithWork keys words r).1.value := by
    intro r
    rw [queryParentReadWithWork_value]
    apply finiteAnswerTable_nonneg
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpn key
  have h := queryLocalBand_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t (queryParentReadWithWork keys words) readMass readInitial
    readGroup readInteger q readEarlier readCurrent oracle B
    (1 + keys.length * (16 * Nat.size target.length + 6)) hB hN hnx hny hMb hPb hFb ht ha hd
    (fun r => gatheredWordLookupWithWork_width _ keys words r B (by omega) hw)
    (queryParentReadWithWork_cost keys words) (hn q) hew hcw
  simpa only [queryLocalProgram, queryInitialGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Program
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalProgramWidth
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

section Physical
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
  (q : TargetInterval target.length)
  (oracle : Sum σ {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)

theorem queryPhysicalRandomDataRequest_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q).value oracle).width ≤
      preparedKernelWordBudget M B := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgram_width source target (physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t _ _ _ _ _ q _ _ oracle B
    hn.largeBits hn.inputSize (by have := hn.sourceSize; omega) hn.targetSize
    (by have := hn.aritySize; omega) (by have := hn.precisionSize; omega) hn.factorSize htime hn.factorWidth hn.decrementSize
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hv _
  · intro r
    rw [BitQuery.mapKeysWithWork_value]
    exact hnonneg _
  · intro key
    rw [BitQuery.mapKeysWithWork_value]
    exact queryPhysicalEarlierRead_width copies pass copy T S t node hbelow q
      (fun key => oracle (Sum.inr key)) B (by have := hn.largeBits; omega) hv key
  · intro key
    rw [BitQuery.mapKeysWithWork_value]
    exact hv _

end Physical

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)

theorem queryFamilyRefinement_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies pass copy T S t ht node hbelow time q).value oracle).width ≤
      preparedKernelWordBudget M B := by
  unfold queryFamilyRefinement
  exact queryPhysicalRandomDataRequest_width source target N P F exponent H Q eM eF B E Scale
    hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q oracle hn htime hv hnonneg

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRestrictionCost
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BitQuery

theorem restrictWithWork_value {ι : Type*} (P : ι → Prop) (test : ι → Bool × ℕ)
    (htest : ∀ key, (test key).1 = true ↔ P key)
    (program : BitQuery ι BinaryFraction) (oracle : {key // P key} → BinaryFraction) :
    (restrictWithWork P test htest program).value oracle =
      program.value (restrictedOracle P test htest oracle) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih =>
    by_cases h : (test key).1 = true
    · simp only [restrictWithWork, h, dite_true, value, restrictedOracle, ih]
    · simp only [restrictWithWork, h, Bool.false_eq_true, dite_false, value, restrictedOracle, ih]

end EditApproximation.BitQuery

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

theorem queryRestrictPhysicalBody_value
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction) :
    (queryRestrictPhysicalBody passes copies T S parent program).value oracle =
      program.value (queryRestrictedPhysicalOracle passes copies T S parent oracle) := by
  rw [queryRestrictPhysicalBody, BitQuery.mapKeysWithWork_value, BitQuery.restrictWithWork_value]
  rfl

theorem queryRestrictedPhysicalOracle_table_width
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (B : ℕ) (hB : 2 ≤ B) (hw : ∀ key, (oracle (Sum.inr key)).width ≤ B) (child) :
    (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).width ≤ B := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

theorem queryRestrictedPhysicalOracle_table_nonneg
    (oracle : QueryBoundedChild (σ := σ) passes copies T S parent → BinaryFraction)
    (hn : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) (child) :
    0 ≤ (queryRestrictedPhysicalOracle passes copies T S parent oracle (Sum.inr child)).value := by
  unfold queryRestrictedPhysicalOracle BitQuery.restrictedOracle
  split
  · exact hn _
  · simp only [BinaryFraction.nat_value, Nat.cast_zero, le_refl]

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

end History
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActiveCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Active
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → BinaryFraction)
  (readWork : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S < request.combinedRank T S} → ℕ)

open BinaryFraction

theorem queryFamilyActive_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (request.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (request.index - T) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies request hindex hbelow).value oracle).width ≤
      preparedKernelWordBudget M B := by
  rw [queryFamilyActive, BitQuery.mapKeysWithWork_value]
  apply queryFamilyRefinement_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta passes copies request.pass request.copy T S (request.index - T)
    (Nat.sub_pos_of_lt hindex) request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state
    _ hn htime
  · intro key
    exact hv _
  · intro key
    exact hnonneg _

end Active
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryBoundedActiveCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Bounded
variable {α : Type*} {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF B E Scale : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (oracle : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → BinaryFraction)
  (readWork : QueryBoundedChild (σ := PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies) (passes + 1) copies T S parent → ℕ)

local notation "rawOracle" => queryRestrictedPhysicalOracle (passes + 1) copies T S parent oracle
open BinaryFraction

theorem queryFamilyBoundedActive_width
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size (parent.val.index - T) ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (oracle (Sum.inr key)).value) :
    ((queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent hindex hbelow).value oracle).width ≤
      preparedKernelWordBudget M B := by
  rw [queryFamilyBoundedActive, queryRestrictPhysicalBody_value]
  apply queryFamilyActive_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow rawOracle hn htime
  · exact queryRestrictedPhysicalOracle_table_width (passes + 1) copies T S parent oracle B
      (by have := hn.largeBits; omega) hv
  · exact queryRestrictedPhysicalOracle_table_nonneg (passes + 1) copies T S parent oracle hnonneg

end Bounded
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialConeCenters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The initial-cone gather uses the unfiltered center list: a seed at a
center must be read before the eligibility test at that center is known. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryInitialSeedReadWithWork_value {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    bitWordValue (queryInitialSeedReadWithWork value q keys words r).1 =
      if r = q then ⌈value.value⌉₊ else ⌈finiteAnswerTable keys (words.map BinaryFraction.value) r⌉₊ := by
  unfold queryInitialSeedReadWithWork
  by_cases hr : r = q
  · rw [ite_eq_left ((queryIntervalEqualWithWork_value r q).mpr hr), ite_eq_left hr]
    exact naturalCeilingWithWork_value value
  · rw [ite_eq_right (fun h => hr ((queryIntervalEqualWithWork_value r q).mp h)), ite_eq_right hr]
    simp only [naturalCeilingWithWork_value, queryParentReadWithWork_value]

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialSeedReadWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



@[simp] theorem queryOverrideParentReadWithWork_value {n : ℕ} (value : BinaryFraction)
    (q : TargetInterval n) (keys : List (TargetInterval n)) (words : List BinaryFraction)
    (r : TargetInterval n) :
    (queryOverrideParentReadWithWork value q keys words r).1.value =
      if r = q then value.value else finiteAnswerTable keys (words.map BinaryFraction.value) r := by
  unfold queryOverrideParentReadWithWork
  by_cases hr : r = q
  · rw [ite_eq_left ((queryIntervalEqualWithWork_value r q).mpr hr), ite_eq_left hr]
  · rw [ite_eq_right (fun h => hr ((queryIntervalEqualWithWork_value r q).mp h)), ite_eq_right hr]
    exact queryParentReadWithWork_value keys words r

end EditApproximation.BinaryFraction

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


theorem queryChargedFamilyTable_semantic_width_oai
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (parent.val.index - T - 1)
      tau (a parent.val.pass) eta kappa delta (fun _ _ => 0))
    (ht' : Nat.size (target.length + 1) + 2 ≤ B)
    (hinit : Nat.size ((32 * F + 1) * N) + 3 ≤ B)
    (hi : Nat.size parent.val.index ≤ B)
    (hv : ∀ key, (oracle (Sum.inr key)).width ≤ B) (hdelta : 0 ≤ delta.value)
    (hread : ∀ child : {r : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        r.val.combinedRank T S < parent.val.combinedRank T S},
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
        requestValue child.val.val) :
    ((queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa
      delta multiplier occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget M B + preparedKernelWordBudget M B := by
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  apply queryChargedFamilyTable_width source target N P F exponent H Q eM eF B hP hM hF A a tau eta kappa
    delta multiplier occurrence symbolBits positionBits parent oracle hn.largeBits hn.inputSize
    hn.precisionSize hn.factorSize hFpos hn.sourceSize hn.targetSize ht' hinit
    (by have := hn.aritySize; omega) hn.factorWidth hv
  intro hindex hbelow
  apply queryFamilyBoundedActive_width source target N P F exponent H Q eM eF B E Scale hP hM hF
    tau (a parent.val.pass) eta kappa delta T S passes copies parent hindex hbelow _ hn
    ((Nat.size_le_size (Nat.sub_le _ _)).trans hi)
  · intro child
    exact hv _
  · intro child
    change (oracle (Sum.inr ⟨Sum.inr child.val, _⟩)).value ≥ 0
    rw [hread child]
    exact (localRequestValue_bounds source target N P F exponent H Q T S copies factor multiplier
      tau.value eta.value kappa.value delta.value group integer initial hdelta child.val.val).1

end Table
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.queryChargedFamilyTable_semantic_width_oai := @OAI.EditApproximation.queryChargedFamilyTable_semantic_width_oai

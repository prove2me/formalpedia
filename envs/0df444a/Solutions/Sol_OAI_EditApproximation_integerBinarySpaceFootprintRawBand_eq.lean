-- Prove2me | solution 1 for OAI.EditApproximation.integerBinarySpaceFootprintRawBand_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:43:05.221263+00:00
-- url     : https://prove2.me/submissions/53448b3a-3b7f-4077-8af8-16e677bd9427

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
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
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_EditApproxScheme_17
import Definitions.Def_EditApproxScheme_18
import Definitions.Def_EditApproxScheme_19
import Definitions.Def_EditApproxScheme_20
import Definitions.Def_OAIQ361V3Ea004

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.EditApproximation

namespace BinaryFraction



theorem preparedUnskippedReadWithWorkRaw_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    preparedUnskippedReadWithWorkRaw parent b P exponent tau F read initial center =
      Prod.map (Option.map UnskippedBand.raw) id
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
          read initial R C hr hi center) := by
  have hbandValue : (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read).1 =
      representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (read i q).1.value) := by
    apply (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) read R hr).1.trans
    simpa only [inversePowerTwo_value] using preparedRepresentativeWithWork_value source target
      parent center b P hP tau (inversePowerTwo exponent) (fun i q => (read i q).1)
  unfold preparedUnskippedReadWithWorkRaw preparedUnskippedReadWithWork
  dsimp only
  split_ifs with hempty hguard
  · rfl
  · simp only [Prod.map, Option.map_some, id_eq, UnskippedBand.raw, UnskippedBand.actions]
    congr 3
  · rfl

end BinaryFraction
end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandBridges
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation

theorem filterMapWithWork_map_raw {α β γ : Type*} (f : α → Option β × ℕ)
    (g : β → γ) (xs : List α) :
    filterMapWithWork (fun x => Prod.map (Option.map g) id (f x)) xs =
      Prod.map (List.map g) id (filterMapWithWork f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Prod.map, id_eq] at ih
    simp only [filterMapWithWork, Prod.map, id_eq, ih]
    cases (f x).1 <;> rfl

theorem filterMapAllocation_map_raw {α β γ : Type*} (f : α → Option β × ℕ)
    (g : β → γ) (allocation : α → ℕ) (xs : List α) :
    filterMapAllocation (fun x => Prod.map (Option.map g) id (f x)) allocation xs =
      filterMapAllocation f allocation xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Prod.map] at ih
    simp only [filterMapAllocation, Prod.map, ih, Option.isSome_map]

namespace BinaryFraction

theorem scoredArgmaxWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) :
    scoredArgmaxWithWork score (values.map mapping) =
      Prod.map (Option.map (fun result => (mapping result.1, result.2))) id
        (scoredArgmaxWithWork (fun a => score (mapping a)) values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, scoredArgmaxWithWork, ih, Prod.map, id_eq]
    cases (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 with
    | none => rfl
    | some best =>
      simp only [Option.map_some]
      split_ifs <;> rfl

theorem selectGroupWithWork_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) (hne : values ≠ []) :
    selectGroupWithWork (values.map mapping) (by simpa using hne) score =
      Prod.map mapping id (selectGroupWithWork values hne (fun a => score (mapping a))) := by
  unfold selectGroupWithWork
  rw [scoredArgmaxWithWork_map_raw]
  simp only [Prod.map, id_eq, Option.map_map, Function.comp_def]
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
    simp only [List.map_cons, List.head_cons]
    cases (scoredArgmaxWithWork (fun a => ((score (mapping a)).1.neg, (score (mapping a)).2 + 1))
      (head :: tail)).1 <;> rfl

theorem scoredArgmaxAllocation_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (allocation : β → ℕ) (values : List α) :
    scoredArgmaxAllocation score allocation (values.map mapping) =
      scoredArgmaxAllocation (fun a => score (mapping a)) (fun a => allocation (mapping a)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, scoredArgmaxAllocation, ih, scoredArgmaxWithWork_map_raw, Prod.map]
    cases (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 <;> rfl

theorem selectGroupAllocation_map_raw {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (allocation : β → ℕ) (values : List α) :
    selectGroupAllocation (values.map mapping) score allocation =
      selectGroupAllocation values (fun a => score (mapping a)) (fun a => allocation (mapping a)) := by
  exact scoredArgmaxAllocation_map_raw mapping _ allocation values

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
  (drawSource : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent (value tau) (value F)
  (fun i q => value (child i q)) (fun i q => value (Prod.fst (initial i q)))

theorem chooseUnskippedSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    chooseUnskippedSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      Prod.map UnskippedBand.raw id
        (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
          scales drawSource members hne) := by
  exact selectGroupWithWork_map_raw UnskippedBand.raw _ members hne

theorem sampledGroupActionSourceWithWorkRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionSourceWithWorkRaw b exponent Q initial current scales drawSource
      (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current
        scales drawSource members hne := by
  let finish := fun selected : RawUnskippedBand M target.length × ℕ =>
    let rounded := roundedBandReadWithWork exponent b selected.1.actions selected.1.nonempty initial
    let result := endpointActionWithWork selected.1.center rounded.1.get
    (result.1, selected.2 + rounded.2 + result.2 + 3)
  exact congrArg finish (chooseUnskippedSourceWithWorkRaw_eq source target parent b P exponent Q
    tau F child initial current scales drawSource members hne)

theorem chooseUnskippedSourceAllocationRaw_eq (members : List Member) :
    chooseUnskippedSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
      scales drawSource drawAllocation (members.map UnskippedBand.raw) =
      chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
        initialAllocation currentAllocation scales drawSource drawAllocation members := by
  exact selectGroupAllocation_map_raw UnskippedBand.raw _ _ members

theorem sampledGroupActionSourceAllocationRaw_eq (members : List Member) (hne : members ≠ []) :
    sampledGroupActionSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
      scales drawSource drawAllocation (members.map UnskippedBand.raw) (by simpa using hne) =
      sampledGroupActionSourceAllocation source target parent b P exponent Q tau F child initial current
        initialAllocation currentAllocation scales drawSource drawAllocation members hne := by
  unfold sampledGroupActionSourceAllocationRaw sampledGroupActionSourceAllocation
  rw [chooseUnskippedSourceWithWorkRaw_eq, chooseUnskippedSourceAllocationRaw_eq]
  rfl

end Group
end BinaryFraction
end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandOuterBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation.BinaryFraction

theorem preparedOnlineReadWithWorkRaw_eq : @preparedOnlineReadWithWorkRaw = @preparedOnlineReadWithWork := by
  funext α source target M parent P F exponent H b hb hP tau eta kappa child initial table R hc hi t center integer
  unfold preparedOnlineReadWithWorkRaw preparedOnlineReadWithWork
  rw [preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R R hc hi center]
  simp only [Prod.map, id_eq, Option.isSome_map]

theorem preparedOnlineReadAllocationRaw_eq : @preparedOnlineReadAllocationRaw = @preparedOnlineReadAllocation := by
  funext α source target M parent P F exponent H b hb hP tau eta kappa child initial table R hc hi
    childAllocation initialAllocation tableAllocation t center integer
  unfold preparedOnlineReadAllocationRaw preparedOnlineReadAllocation
  rw [preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R R hc hi center]
  simp only [Prod.map, Option.isSome_map]

theorem preparedCellGroupSourceWithWorkRaw_eq : @preparedCellGroupSourceWithWorkRaw = @preparedCellGroupSourceWithWork := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  dsimp only [centers] at hmembers
  unfold preparedCellGroupSourceWithWorkRaw preparedCellGroupSourceWithWork
  simp only [hmembers]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [sampledGroupActionSourceWithWorkRaw_eq]

theorem preparedCellGroupSourceAllocationRaw_eq : @preparedCellGroupSourceAllocationRaw = @preparedCellGroupSourceAllocation := by
  funext α source target M parent b P F exponent Q hb hP tau a parentInitial child initial current
    R C hr hi raw hraw draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell
  have hreader := funext (preparedUnskippedReadWithWorkRaw_eq source target parent b P exponent hb hP tau (nat F)
    child initial R C hr hi)
  let centers := (cellCentersReadWithWork P F b a (inversePowerTwo exponent) parentInitial cell).1
  have hmembers : filterMapWithWork
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial) centers =
      Prod.map (List.map UnskippedBand.raw) id (filterMapWithWork
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi) centers) := by
    rw [hreader]
    exact filterMapWithWork_map_raw _ _ _
  have hallocation : filterMapAllocation
      (preparedUnskippedReadWithWorkRaw parent b P exponent tau (nat F) child initial)
      (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
        child initial childAllocation initialAllocation) centers =
      filterMapAllocation
        (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
          child initial R C hr hi)
        (fun center => preparedUnskippedReadAllocation parent center b P exponent tau (nat F)
          child initial childAllocation initialAllocation) centers := by
    rw [hreader]
    exact filterMapAllocation_map_raw _ _ _ _
  dsimp only [centers] at hmembers hallocation
  unfold preparedCellGroupSourceAllocationRaw preparedCellGroupSourceAllocation
  simp only [hmembers, hallocation]
  simp only [Prod.map, id_eq, List.map_eq_nil_iff]
  split_ifs with h
  · rfl
  · rw [sampledGroupActionSourceAllocationRaw_eq]

end OAI.EditApproximation.BinaryFraction
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandPipelineBridges
attribute [-simp] _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedOnlineReadWithWorkRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand = @OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork := by
  unfold OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWork
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRefinementRawBand_eq : @OAI.EditApproximation.queryLocalRefinementRawBand = @OAI.EditApproximation.queryLocalRefinement := by
  unfold OAI.EditApproximation.queryLocalRefinementRawBand OAI.EditApproximation.queryLocalRefinement
  simp only [OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq : @OAI.EditApproximation.queryLocalRandomSourcesRawBand = @OAI.EditApproximation.queryLocalRandomSources := by
  unfold OAI.EditApproximation.queryLocalRandomSourcesRawBand OAI.EditApproximation.queryLocalRandomSources
  simp only [OAI.EditApproximation.queryLocalRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalBandRawBand_eq : @OAI.EditApproximation.queryLocalBandRawBand = @OAI.EditApproximation.queryLocalBand := by
  unfold OAI.EditApproximation.queryLocalBandRawBand OAI.EditApproximation.queryLocalBand
  simp only [OAI.EditApproximation.queryLocalRandomSourcesRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryLocalProgramRawBand_eq : @OAI.EditApproximation.queryLocalProgramRawBand = @OAI.EditApproximation.queryLocalProgram := by
  unfold OAI.EditApproximation.queryLocalProgramRawBand OAI.EditApproximation.queryLocalProgram
  simp only [OAI.EditApproximation.queryLocalBandRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq : @OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand = @OAI.EditApproximation.queryPhysicalRandomDataRequest := by
  unfold OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand OAI.EditApproximation.queryPhysicalRandomDataRequest
  simp only [OAI.EditApproximation.queryLocalProgramRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyRefinementRawBand_eq : @OAI.EditApproximation.queryFamilyRefinementRawBand = @OAI.EditApproximation.queryFamilyRefinement := by
  unfold OAI.EditApproximation.queryFamilyRefinementRawBand OAI.EditApproximation.queryFamilyRefinement
  simp only [OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyActiveRawBand_eq : @OAI.EditApproximation.queryFamilyActiveRawBand = @OAI.EditApproximation.queryFamilyActive := by
  unfold OAI.EditApproximation.queryFamilyActiveRawBand OAI.EditApproximation.queryFamilyActive
  simp only [OAI.EditApproximation.queryFamilyRefinementRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq : @OAI.EditApproximation.queryFamilyBoundedActiveRawBand = @OAI.EditApproximation.queryFamilyBoundedActive := by
  unfold OAI.EditApproximation.queryFamilyBoundedActiveRawBand OAI.EditApproximation.queryFamilyBoundedActive
  simp only [OAI.EditApproximation.queryFamilyActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyTableRawBand_eq : @OAI.EditApproximation.queryChargedFamilyTableRawBand = @OAI.EditApproximation.queryChargedFamilyTable := by
  unfold OAI.EditApproximation.queryChargedFamilyTableRawBand OAI.EditApproximation.queryChargedFamilyTable
  simp only [OAI.EditApproximation.queryFamilyBoundedActiveRawBand_eq]

@[simp] theorem OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq : @OAI.EditApproximation.queryChargedFamilyGlobalRawBand = @OAI.EditApproximation.queryChargedFamilyGlobal := by
  unfold OAI.EditApproximation.queryChargedFamilyGlobalRawBand OAI.EditApproximation.queryChargedFamilyGlobal
  simp only [OAI.EditApproximation.queryChargedFamilyTableRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.queryFamilyMemoRawRawBand_eq : @OAI.EditApproximation.queryFamilyMemoRawRawBand = @OAI.EditApproximation.queryFamilyMemoRaw := by
  unfold OAI.EditApproximation.queryFamilyMemoRawRawBand OAI.EditApproximation.queryFamilyMemoRaw
  simp only [OAI.EditApproximation.queryChargedFamilyGlobalRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoRawRawBand_eq : @OAI.EditApproximation.computedQueryMemoRawRawBand = @OAI.EditApproximation.computedQueryMemoRaw := by
  unfold OAI.EditApproximation.computedQueryMemoRawRawBand OAI.EditApproximation.computedQueryMemoRaw
  simp only [OAI.EditApproximation.queryFamilyMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq : @OAI.EditApproximation.computedQueryMemoNormalizedRawBand = @OAI.EditApproximation.computedQueryMemoNormalized := by
  unfold OAI.EditApproximation.computedQueryMemoNormalizedRawBand OAI.EditApproximation.computedQueryMemoNormalized
  simp only [OAI.EditApproximation.computedQueryMemoRawRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryMemoResultRawBand_eq : @OAI.EditApproximation.computedQueryMemoResultRawBand = @OAI.EditApproximation.computedQueryMemoResult := by
  unfold OAI.EditApproximation.computedQueryMemoResultRawBand OAI.EditApproximation.computedQueryMemoResult
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryLocalWorkRawBand_eq : @OAI.EditApproximation.computedQueryLocalWorkRawBand = @OAI.EditApproximation.computedQueryLocalWork := by
  unfold OAI.EditApproximation.computedQueryLocalWorkRawBand OAI.EditApproximation.computedQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryMemoNormalizedRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerQueryLocalWorkRawBand_eq : @OAI.EditApproximation.integerQueryLocalWorkRawBand = @OAI.EditApproximation.integerQueryLocalWork := by
  unfold OAI.EditApproximation.integerQueryLocalWorkRawBand OAI.EditApproximation.integerQueryLocalWork
  simp only [OAI.EditApproximation.computedQueryLocalWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq : @OAI.EditApproximation.computedQueryAnswerWithWorkRawBand = @OAI.EditApproximation.computedQueryAnswerWithWork := by
  unfold OAI.EditApproximation.computedQueryAnswerWithWorkRawBand OAI.EditApproximation.computedQueryAnswerWithWork
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryOutputRawBand_eq : @OAI.EditApproximation.integerBinaryOutputRawBand = @OAI.EditApproximation.integerBinaryOutput := by
  unfold OAI.EditApproximation.integerBinaryOutputRawBand OAI.EditApproximation.integerBinaryOutput
  simp only [OAI.EditApproximation.computedQueryAnswerWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryAnswerRawBand_eq : @OAI.EditApproximation.integerBinaryAnswerRawBand = @OAI.EditApproximation.integerBinaryAnswer := by
  unfold OAI.EditApproximation.integerBinaryAnswerRawBand OAI.EditApproximation.integerBinaryAnswer
  simp only [OAI.EditApproximation.integerBinaryOutputRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceAllocationRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand_eq]
  rfl

@[simp] theorem OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand_eq : @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand = @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock := by
  unfold OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlock
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand = @OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand_eq, OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedOnlineReadAllocationRaw_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand = @OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand_eq, OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand = @OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand_eq : @OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand = @OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocation := by
  unfold OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocation
  simp only [OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerBinaryWorkRawBand_eq : @OAI.EditApproximation.integerBinaryWorkRawBand = @OAI.EditApproximation.integerBinaryWork := by
  unfold OAI.EditApproximation.integerBinaryWorkRawBand OAI.EditApproximation.integerBinaryWork
  simp only [OAI.EditApproximation.integerQueryLocalWorkRawBand_eq, OAI.EditApproximation.integerBinaryOutputRawBand_eq]

@[simp] theorem OAI.EditApproximation.integerFinalAllocationRawBand_eq : @OAI.EditApproximation.integerFinalAllocationRawBand = @OAI.EditApproximation.integerFinalAllocation := by
  unfold OAI.EditApproximation.integerFinalAllocationRawBand OAI.EditApproximation.integerFinalAllocation
  simp only [OAI.EditApproximation.computedQueryMemoResultRawBand_eq]
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandPipelineFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



namespace OAI.EditApproximation

universe u v

private theorem footprintRanked_congr {κ : Type*} (rank : κ → ℕ)
    (p q : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (hp : p = q) (a : ∀ key, BitQuery.Footprint (p key))
    (b : ∀ key, BitQuery.Footprint (q key)) (hab : HEq a b)
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) :
    BitQuery.Footprint.rankedBitMemoCells rank p a bits encode addressCells key memory =
      BitQuery.Footprint.rankedBitMemoCells rank q b bits encode addressCells key memory := by
  cases hp
  cases eq_of_heq hab
  rfl

private theorem queryLocalRefinementFootprintRawBand_heq :
    HEq @queryLocalRefinementFootprintRawBand.{u, v} @queryLocalRefinementFootprint.{u, v} := by
  unfold queryLocalRefinementFootprintRawBand queryLocalRefinementFootprint
  unfold queryLocalRefinementRawBand queryLocalRefinement
  rw [BinaryFraction.queryOnlineSelectWithWorkRawBand_eq,
    BinaryFraction.queryGroupSelectWithWorkRawBand_eq]
  simp only [
    BinaryFraction.queryOnlineSelectAllocationRawBand_eq,
    BinaryFraction.queryGroupSelectAllocationRawBand_eq]
  rfl
private theorem queryLocalRandomSourcesFootprintRawBand_heq :
    HEq @queryLocalRandomSourcesFootprintRawBand.{u, v} @queryLocalRandomSourcesFootprint.{u, v} := by
  have hp : @queryLocalRefinementRawBand.{u, v} = @queryLocalRefinement.{u, v} := queryLocalRefinementRawBand_eq
  have hfp : HEq @queryLocalRefinementFootprintRawBand.{u, v} @queryLocalRefinementFootprint.{u, v} := queryLocalRefinementFootprintRawBand_heq
  delta queryLocalRandomSourcesFootprintRawBand queryLocalRandomSourcesFootprint
  delta queryLocalRandomSourcesRawBand queryLocalRandomSources
  generalize hfr : @queryLocalRefinementFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalRefinementFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalRefinementRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalRefinement.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryLocalBandFootprintRawBand_heq :
    HEq @queryLocalBandFootprintRawBand.{u, v} @queryLocalBandFootprint.{u, v} := by
  have hp : @queryLocalRandomSourcesRawBand.{u, v} = @queryLocalRandomSources.{u, v} := queryLocalRandomSourcesRawBand_eq
  have hfp : HEq @queryLocalRandomSourcesFootprintRawBand.{u, v} @queryLocalRandomSourcesFootprint.{u, v} := queryLocalRandomSourcesFootprintRawBand_heq
  delta queryLocalBandFootprintRawBand queryLocalBandFootprint
  delta queryLocalBandRawBand queryLocalBand
  generalize hfr : @queryLocalRandomSourcesFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalRandomSourcesFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalRandomSourcesRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalRandomSources.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryLocalProgramFootprintRawBand_heq :
    HEq @queryLocalProgramFootprintRawBand.{u, v} @queryLocalProgramFootprint.{u, v} := by
  have hp : @queryLocalBandRawBand.{u, v} = @queryLocalBand.{u, v} := queryLocalBandRawBand_eq
  have hfp : HEq @queryLocalBandFootprintRawBand.{u, v} @queryLocalBandFootprint.{u, v} := queryLocalBandFootprintRawBand_heq
  delta queryLocalProgramFootprintRawBand queryLocalProgramFootprint
  delta queryLocalProgramRawBand queryLocalProgram
  generalize hfr : @queryLocalBandFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalBandFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalBandRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalBand.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryPhysicalRandomDataRequestFootprintRawBand_heq :
    HEq @queryPhysicalRandomDataRequestFootprintRawBand.{u, v} @queryPhysicalRandomDataRequestFootprint.{u, v} := by
  have hp : @queryLocalProgramRawBand.{u, v} = @queryLocalProgram.{u, v} := queryLocalProgramRawBand_eq
  have hfp : HEq @queryLocalProgramFootprintRawBand.{u, v} @queryLocalProgramFootprint.{u, v} := queryLocalProgramFootprintRawBand_heq
  delta queryPhysicalRandomDataRequestFootprintRawBand queryPhysicalRandomDataRequestFootprint
  delta queryPhysicalRandomDataRequestRawBand queryPhysicalRandomDataRequest
  generalize hfr : @queryLocalProgramFootprintRawBand.{u, v} = fr at *
  generalize hfo : @queryLocalProgramFootprint.{u, v} = fo at *
  clear hfr hfo
  generalize hpr : @queryLocalProgramRawBand.{u, v} = pr at *
  generalize hpo : @queryLocalProgram.{u, v} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyRefinementFootprintRawBand_heq :
    HEq @queryFamilyRefinementFootprintRawBand.{u} @queryFamilyRefinementFootprint.{u} := by
  have hp : @queryPhysicalRandomDataRequestRawBand.{0, u} = @queryPhysicalRandomDataRequest.{0, u} := queryPhysicalRandomDataRequestRawBand_eq
  have hfp : HEq @queryPhysicalRandomDataRequestFootprintRawBand.{0, u} @queryPhysicalRandomDataRequestFootprint.{0, u} := queryPhysicalRandomDataRequestFootprintRawBand_heq
  delta queryFamilyRefinementFootprintRawBand queryFamilyRefinementFootprint
  delta queryFamilyRefinementRawBand queryFamilyRefinement
  generalize hfr : @queryPhysicalRandomDataRequestFootprintRawBand.{0, u} = fr at *
  generalize hfo : @queryPhysicalRandomDataRequestFootprint.{0, u} = fo at *
  clear hfr hfo
  generalize hpr : @queryPhysicalRandomDataRequestRawBand.{0, u} = pr at *
  generalize hpo : @queryPhysicalRandomDataRequest.{0, u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyActiveFootprintRawBand_heq :
    HEq @queryFamilyActiveFootprintRawBand.{u} @queryFamilyActiveFootprint.{u} := by
  have hp : @queryFamilyRefinementRawBand.{u} = @queryFamilyRefinement.{u} := queryFamilyRefinementRawBand_eq
  have hfp : HEq @queryFamilyRefinementFootprintRawBand.{u} @queryFamilyRefinementFootprint.{u} := queryFamilyRefinementFootprintRawBand_heq
  delta queryFamilyActiveFootprintRawBand queryFamilyActiveFootprint
  delta queryFamilyActiveRawBand queryFamilyActive
  generalize hfr : @queryFamilyRefinementFootprintRawBand.{u} = fr at *
  generalize hfo : @queryFamilyRefinementFootprint.{u} = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyRefinementRawBand.{u} = pr at *
  generalize hpo : @queryFamilyRefinement.{u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyBoundedActiveFootprintRawBand_heq :
    HEq @queryFamilyBoundedActiveFootprintRawBand.{u} @queryFamilyBoundedActiveFootprint.{u} := by
  have hp : @queryFamilyActiveRawBand.{u} = @queryFamilyActive.{u} := queryFamilyActiveRawBand_eq
  have hfp : HEq @queryFamilyActiveFootprintRawBand.{u} @queryFamilyActiveFootprint.{u} := queryFamilyActiveFootprintRawBand_heq
  delta queryFamilyBoundedActiveFootprintRawBand queryFamilyBoundedActiveFootprint
  delta queryFamilyBoundedActiveRawBand queryFamilyBoundedActive
  generalize hfr : @queryFamilyActiveFootprintRawBand.{u} = fr at *
  generalize hfo : @queryFamilyActiveFootprint.{u} = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyActiveRawBand.{u} = pr at *
  generalize hpo : @queryFamilyActive.{u} = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

theorem queryChargedFamilyTableFootprintGen_heq_of
    {q₁ : type_of% @queryFamilyBoundedActive.{0}}
    {q₂ : type_of% @queryFamilyBoundedActive.{0}} (h : @q₁ = @q₂)
    {f₁ : QueryFamilyBoundedActiveFootprintType q₁} {f₂ : QueryFamilyBoundedActiveFootprintType q₂}
    (hf : HEq @f₁ @f₂) :
    HEq (@queryChargedFamilyTableFootprintGen q₁ f₁) (@queryChargedFamilyTableFootprintGen q₂ f₂) := by
  subst h
  cases eq_of_heq hf
  rfl

private theorem queryChargedFamilyTableFootprintRawBand_heq :
    HEq @queryChargedFamilyTableFootprintRawBand @queryChargedFamilyTableFootprint := by
  have hp : @queryFamilyBoundedActiveRawBand.{0} = @queryFamilyBoundedActive.{0} := queryFamilyBoundedActiveRawBand_eq
  have hfp : HEq @queryFamilyBoundedActiveFootprintRawBand.{0} @queryFamilyBoundedActiveFootprint.{0} := queryFamilyBoundedActiveFootprintRawBand_heq
  have e₁ : HEq @queryChargedFamilyTableFootprintRawBand
      (@queryChargedFamilyTableFootprintGen @queryFamilyBoundedActiveRawBand.{0}
        @queryFamilyBoundedActiveFootprintRawBand.{0}) := HEq.rfl
  have e₂ : HEq @queryChargedFamilyTableFootprint
      (@queryChargedFamilyTableFootprintGen @queryFamilyBoundedActive.{0}
        @queryFamilyBoundedActiveFootprint.{0}) := HEq.rfl
  exact e₁.trans ((queryChargedFamilyTableFootprintGen_heq_of hp hfp).trans e₂.symm)

private theorem queryChargedFamilyGlobalFootprintRawBand_heq :
    HEq @queryChargedFamilyGlobalFootprintRawBand @queryChargedFamilyGlobalFootprint := by
  have hp : @queryChargedFamilyTableRawBand = @queryChargedFamilyTable := queryChargedFamilyTableRawBand_eq
  have hfp : HEq @queryChargedFamilyTableFootprintRawBand @queryChargedFamilyTableFootprint := queryChargedFamilyTableFootprintRawBand_heq
  delta queryChargedFamilyGlobalFootprintRawBand queryChargedFamilyGlobalFootprint
  delta queryChargedFamilyGlobalRawBand queryChargedFamilyGlobal
  generalize hfr : @queryChargedFamilyTableFootprintRawBand = fr at *
  generalize hfo : @queryChargedFamilyTableFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryChargedFamilyTableRawBand = pr at *
  generalize hpo : @queryChargedFamilyTable = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem queryFamilyMemoRawFootprintRawBand_heq :
    HEq @queryFamilyMemoRawFootprintRawBand @queryFamilyMemoRawFootprint := by
  have hp : @queryChargedFamilyGlobalRawBand = @queryChargedFamilyGlobal := queryChargedFamilyGlobalRawBand_eq
  have hfp : HEq @queryChargedFamilyGlobalFootprintRawBand @queryChargedFamilyGlobalFootprint := queryChargedFamilyGlobalFootprintRawBand_heq
  delta queryFamilyMemoRawFootprintRawBand queryFamilyMemoRawFootprint
  delta queryFamilyMemoRawRawBand queryFamilyMemoRaw
  generalize hfr : @queryChargedFamilyGlobalFootprintRawBand = fr at *
  generalize hfo : @queryChargedFamilyGlobalFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryChargedFamilyGlobalRawBand = pr at *
  generalize hpo : @queryChargedFamilyGlobal = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

private theorem computedQueryMemoRawFootprintRawBand_heq :
    HEq @computedQueryMemoRawFootprintRawBand @computedQueryMemoRawFootprint := by
  have hp : @queryFamilyMemoRawRawBand = @queryFamilyMemoRaw := queryFamilyMemoRawRawBand_eq
  have hfp : HEq @queryFamilyMemoRawFootprintRawBand @queryFamilyMemoRawFootprint := queryFamilyMemoRawFootprintRawBand_heq
  delta computedQueryMemoRawFootprintRawBand computedQueryMemoRawFootprint
  delta computedQueryMemoRawRawBand computedQueryMemoRaw
  generalize hfr : @queryFamilyMemoRawFootprintRawBand = fr at *
  generalize hfo : @queryFamilyMemoRawFootprint = fo at *
  clear hfr hfo
  generalize hpr : @queryFamilyMemoRawRawBand = pr at *
  generalize hpo : @queryFamilyMemoRaw = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

theorem computedQueryMemoFootprintRawBand_heq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    HEq (computedQueryMemoFootprintRawBand source target N occurrence symbolBits positionBits input)
      (computedQueryMemoFootprint source target N occurrence symbolBits positionBits input) := by
  have hp : @computedQueryMemoRawRawBand = @computedQueryMemoRaw := computedQueryMemoRawRawBand_eq
  have hfp : HEq @computedQueryMemoRawFootprintRawBand @computedQueryMemoRawFootprint := computedQueryMemoRawFootprintRawBand_heq
  delta computedQueryMemoFootprintRawBand computedQueryMemoFootprint
  delta computedQueryMemoNormalizedRawBand computedQueryMemoNormalized
  generalize hfr : @computedQueryMemoRawFootprintRawBand = fr at *
  generalize hfo : @computedQueryMemoRawFootprint = fo at *
  clear hfr hfo
  generalize hpr : @computedQueryMemoRawRawBand = pr at *
  generalize hpo : @computedQueryMemoRaw = po at *
  have hp' : @pr = @po := by simpa only [hpr, hpo] using hp
  clear hp hpr hpo
  cases hp'
  cases eq_of_heq hfp
  rfl

theorem computedQueryTemporaryCellsFootprintRawBand_eq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedQueryTemporaryCellsFootprintRawBand source target N occurrence symbolBits positionBits input =
      computedQueryTemporaryCellsFootprint source target N occurrence symbolBits positionBits input := by
  unfold computedQueryTemporaryCellsFootprintRawBand computedQueryTemporaryCellsFootprint
  apply footprintRanked_congr
  · rw [computedQueryMemoNormalizedRawBand_eq]
  · exact computedQueryMemoFootprintRawBand_heq source target N occurrence symbolBits positionBits input

theorem integerAcceptedSpaceTermsFootprintRawBand_eq (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerAcceptedSpaceTermsFootprintRawBand source target N epsilon input =
      integerAcceptedSpaceTermsFootprint source target N epsilon input := by
  simp only [integerAcceptedSpaceTermsFootprintRawBand, integerAcceptedSpaceTermsFootprint,
    computedQueryTemporaryCellsFootprintRawBand_eq, computedQueryMemoResultRawBand_eq,
    integerFinalAllocationRawBand_eq]

theorem integerBinarySpaceFootprintRawBand_eq_oai (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinarySpaceFootprintRawBand source target N epsilon outcome =
      integerBinarySpaceFootprint source target N epsilon outcome := by
  simp only [integerBinarySpaceFootprintRawBand, integerBinarySpaceFootprint,
    integerAcceptedSpaceTermsFootprintRawBand_eq]
  rfl

end OAI.EditApproximation
end

theorem solution : type_of% @OAI.EditApproximation.integerBinarySpaceFootprintRawBand_eq_oai := @OAI.EditApproximation.integerBinarySpaceFootprintRawBand_eq_oai

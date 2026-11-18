-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgram_conditional_node_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:33.707542+00:00
-- url     : https://prove2.me/submissions/93741122-5f7d-44b8-b5b1-6da174d5e96e

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalProgramRefresh_group_mem
import Theorems.Thm_OAI_EditApproximation_physicalProgramRefresh_online_mem
import Theorems.Thm_OAI_EditApproximation_physical_conditional_node_regret

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite online and whole-cell candidate programs

Physical selections use the representative and guarded band lists. Each
band has its own finite optimizer stream; every whole cell has shared
per-scale child streams. These streams define coherent finite tables.
-/

namespace EditApproximation

open Finset



section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A

theorem physicalProgramBandG_spec (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center)) :
    physicalProgramBandG source target U N P F A T thetaExponent H tau node representative =
      H + (bandCoordinates member.actions.toFinset).card + 2 := by
  simp only [physicalProgramBandG, hget, physicalBandActions, UnskippedBand.actions]


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionResampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal parent-coordinate replacement in the finite selection program. -/

namespace EditApproximation

section Resampling

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "Online" => PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R
local notation "Groups" => PhysicalGroupStreams source target U N P F A thetaExponent Q R
local notation "program" => physicalProgramSelections source target U N P F A T thetaExponent H Q tau η κ

variable [NeZero R]

theorem physicalProgramSelections_online_congr_at (online first : Online) (groups : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, online ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).online node = (program first groups).online node := by
  funext children t q
  dsimp only [physicalProgramSelections]
  unfold physicalProgramOnline
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl

theorem physicalProgramSelections_groups_congr_at (online : Online) (groups first : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, groups ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).groups node = (program online first).groups node := by
  funext children t
  dsimp only [physicalProgramSelections]
  unfold physicalProgramGroups
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl


end Resampling

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The global finite product of actual selection streams

Online slots and whole-cell slots form a finite disjoint union. Each slot
contains its complete finite time array with the prescribed product law.
Mapping the flattened product produces
the actual online/group stream pair without independence hypotheses.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section GlobalLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau : ℚ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_online_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ online.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).1 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).1 label := by
  classical
  funext representative
  have hkey : (Sum.inl ⟨label, representative⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inl online := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inl.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne (show (Sum.inl ⟨label, representative⟩ :
    PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inr group from Sum.inl_ne_inr),
    Function.update_of_ne hkey]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalProgramRefresh_group_other
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalInternalNode M J) (hne : label ≠ group.1) :
    (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).2 label =
      (physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw).2 label := by
  classical
  funext scale cell
  have hkey : (Sum.inr ⟨label, scale, cell⟩ : PhysicalProgramKey source target U N P F A thetaExponent) ≠
      Sum.inr group := by
    intro heq
    exact hne (congrArg Sigma.fst (Sum.inr.inj heq))
  dsimp only [physicalProgramDrawStreams, physicalProgramRefresh]
  rw [Function.update_of_ne hkey,
    Function.update_of_ne (show (Sum.inr ⟨label, scale, cell⟩ :
      PhysicalProgramKey source target U N P F A thetaExponent) ≠ Sum.inl online from Sum.inr_ne_inl)]

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
/-- Refreshing a parent's chosen band/cell coordinates leaves every
strictly deeper raw selection function unchanged. -/
theorem physicalProgramDrawSelections_refresh_deeper [NeZero R] (η κ : ℚ)
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau)
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent) (fresh)
    (label : PhysicalNode M J)
    (honline : online.1.1.1.val < label.1.val) (hgroup : group.1.1.1.val < label.1.val) :
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).groups label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).groups label ∧
    (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)).online label =
        (physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ draw).online label := by
  have hneOnline (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ online.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = online.1.1.1.val at hdepth
    omega
  have hneGroup (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ group.1 := by
    intro heq
    have hdepth := congrArg (fun node : PhysicalInternalNode M J => node.1.1.val) heq
    change label.1.val = group.1.1.1.val at hdepth
    omega
  let oldStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau draw
  let nextStreams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)
  constructor
  · exact physicalProgramSelections_groups_congr_at source target U N P F A T thetaExponent H Q tau η κ
      oldStreams.1 nextStreams.2 oldStreams.2 label (fun hbelow => physicalProgramRefresh_group_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneGroup hbelow))
  · exact physicalProgramSelections_online_congr_at source target U N P F A T thetaExponent H Q tau η κ
      nextStreams.1 oldStreams.1 oldStreams.2 label (fun hbelow => physicalProgramRefresh_online_other source target U N P F A T thetaExponent H Q tau
        draw online group fresh ⟨label, hbelow⟩ (hneOnline hbelow))


end GlobalLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramNodeRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local and global expected regret of the complete finite selection program. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Node

variable {α : Type*} [DecidableEq α]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
  {M J P F b Q thetaExponent R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
  (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
  (hthetaeq : thetaExponent = 40 * smallLogExponent N) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta η κ : ℚ)
  (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (node : PhysicalInternalNode M J)
  (hleaf : ¬ (physicalSourceInterval source.length node.1).hi -
    (physicalSourceInterval source.length node.1).lo ≤ 1)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length) (hscale : (dyadicScales N).get scale = b)
  (cell : ℕ × ℕ)
  (cellIndex : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)
  (hcell : (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).get cellIndex = cell)
  (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell ≠ [])
  (specified : UnskippedBand source target (physicalSourceInterval source.length node.1)
    b P thetaExponent (rationalParameters F).tau F
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    (physicalBandChildInitial source target U N P F A node.1 node.2))
  (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell)
  (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, specified.center))
  (q : TargetInterval target.length) (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node.1) target q)
  (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, specified.center))
  (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
  (htau : 0 < (rationalParameters F).tau)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters F).gamma +
    512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
  (bernstein : ∀ h : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
    (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cellIndex) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "bandG" => physicalProgramBandG source target U N P F A T thetaExponent H tau node representative
local notation "bandK" => physicalProgramBandK source target U N P F A T thetaExponent H tau node representative
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau
local notation "localLaw" =>
  Measure.prod (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inl onlineKey))
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inr groupKey))

include hN hell hM hMeq hPeq hFeq hbeq hQeq hthetaeq hHeq hH hsize hP hF hA hseed hT
  hdelta hη hκ hκhalf hleaf hscale hcell hnonempty hspecified hget hb hquery hc htau hηrange herror bernstein

/-- The actual program satisfies the fixed-child conditional node bound;
both candidate-list premises and both deeper-agreement premises are proved. -/
theorem physicalProgram_conditional_node_regret_oai (draw : Draw) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node.1) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta (choices draw) node.1 node.2 comparison
    (∫ fresh : Fresh, (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
        node.1 (t + 1) q : ℝ) - charge - clipped (t + 1))) ∂localLaw) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  have hscalePow : (dyadicScales N).get scale = 2 ^ eb := hscale.trans hbeq
  clear hbeq
  subst b cell
  have hrep : (((dyadicScales N).get scale), specified.center) ∈
      stageRepresentatives source target U N P F A node.1 := by
    simpa only [hget] using List.get_mem (stageRepresentatives source target U N P F A node.1) representative
  have hbound := physical_conditional_node_regret (G := bandG) (K := bandK) source target N hN hell hM hMeq hPeq hFeq
    eb hscalePow hQeq hthetaeq hHeq hH U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
    (choices draw) node.1 node.2 hleaf
    ((physicalProgramCells source target U N P F A thetaExponent node.1 ((dyadicScales N).get scale)).get cellIndex)
    hnonempty specified hspecified hrep q hb comparison hc
    (physicalProgramBandG_spec source target U N P F A T thetaExponent H tau node representative _ specified hget)
    rfl htau hηrange herror
    (fun fresh => choices (refresh draw onlineKey groupKey fresh))
    (fun fresh label hdeeper =>
      (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
        draw onlineKey groupKey fresh label hdeeper hdeeper).1)
    (fun fresh label hdeeper =>
      (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
        draw onlineKey groupKey fresh label hdeeper hdeeper).2)
    (fun fresh t => physicalProgramRefresh_online_mem source target U N P F A T thetaExponent H Q tau delta η κ
      node representative scale cellIndex draw fresh specified hget t q hquery)
    (fun fresh t => physicalProgramRefresh_group_mem source target U N P F A T thetaExponent H Q tau delta η κ
      node representative scale cellIndex draw fresh hnonempty t)
    bernstein S
  exact hbound

end Node

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgram_conditional_node_regret_oai.{u_1} := @OAI.EditApproximation.physicalProgram_conditional_node_regret_oai.{u_1}

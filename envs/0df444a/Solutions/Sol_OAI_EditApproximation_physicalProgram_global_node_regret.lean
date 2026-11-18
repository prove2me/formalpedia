-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgram_global_node_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:02.74992+00:00
-- url     : https://prove2.me/submissions/c3db7bc3-6292-41c3-b3c8-ba4b5ef24372

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
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalProgramRefresh_clipped
import Theorems.Thm_OAI_EditApproximation_physicalProgram_conditional_node_regret
import Theorems.Thm_OAI_EditApproximation_unskipped_expected_regret_budget

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteResampling
attribute [-instance] _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-refresh identities for finite product probability laws. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section FiniteProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableSingletonClass (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Refreshing one coordinate with its own independent law preserves the
complete finite product law. -/
theorem finite_pi_update_map (i : ι) :
    ((Measure.pi μ).prod (μ i)).map
      (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2) = Measure.pi μ := by
  apply Eq.symm
  apply Measure.pi_eq
  intro sets hsets
  have hpreimage : (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2) ⁻¹'
      Set.univ.pi sets = (Set.univ.pi (Function.update sets i Set.univ)) ×ˢ sets i := by
    ext pair
    constructor
    · intro h
      constructor
      · intro j _
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, Set.mem_univ]
        · simpa only [Function.update_of_ne hji] using h j (Set.mem_univ j)
      · simpa only [Function.update_self] using h i (Set.mem_univ i)
    · rintro ⟨hold, hfresh⟩ j _
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hfresh
      · simpa only [Function.update_of_ne hji] using hold j (Set.mem_univ j)
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.univ_pi hsets),
    hpreimage, Measure.prod_prod, Measure.pi_pi]
  rw [← prod_erase_mul (s := univ) (fun j => μ j (Function.update sets i Set.univ j)) (mem_univ i),
    ← prod_erase_mul (s := univ) (fun j => μ j (sets j)) (mem_univ i)]
  simp only [Function.update_self, measure_univ, mul_one]
  congr 1
  apply prod_congr rfl
  intro j hj
  simp only [Function.update_of_ne (ne_of_mem_erase hj)]

/-- Integrating a fresh coordinate, then the complete original array, is
exactly integration in the original product law. -/
theorem finite_pi_integral_update (i : ι) (payoff : (∀ j, X j) → ℝ) :
    (∫ original, ∫ fresh, payoff (Function.update original i fresh) ∂μ i ∂Measure.pi μ) =
      ∫ original, payoff original ∂Measure.pi μ := by
  rw [← integral_prod (fun pair : (∀ j, X j) × X i =>
    payoff (Function.update pair.1 i pair.2)) (.of_finite)]
  have hmap := finite_pi_update_map μ i
  have hintegral := integral_map_of_stronglyMeasurable
    (μ := (Measure.pi μ).prod (μ i))
    (measurable_of_finite (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2))
    (measurable_of_finite payoff).stronglyMeasurable
  rw [hmap] at hintegral
  exact hintegral.symm

/-- Two independent refreshed coordinates provide the local parent law.
The original arrays may still contain their previous values at those keys. -/
theorem finite_pi_integral_update_pair (i j : ι) (payoff : (∀ k, X k) → ℝ) :
    (∫ original, ∫ fresh : X i × X j,
      payoff (Function.update (Function.update original i fresh.1) j fresh.2)
        ∂(μ i).prod (μ j) ∂Measure.pi μ) =
      ∫ original, payoff original ∂Measure.pi μ := by
  have hinner original : (∫ fresh : X i × X j,
      payoff (Function.update (Function.update original i fresh.1) j fresh.2) ∂(μ i).prod (μ j)) =
      ∫ first, ∫ second, payoff (Function.update (Function.update original i first) j second) ∂μ j ∂μ i :=
    integral_prod _ (.of_finite)
  simp_rw [hinner]
  rw [finite_pi_integral_update μ i
    (fun original => ∫ second, payoff (Function.update original j second) ∂μ j)]
  exact finite_pi_integral_update μ j payoff

end FiniteProduct

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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


/-- Exact finite-product disintegration into an original global array and
fresh local parent arrays. The unused old values are integrated out. -/
theorem physicalProgramDrawLaw_refresh_integral
    (online : PhysicalOnlineKey source target U N P F A)
    (group : PhysicalGroupKey source target U N P F A thetaExponent)
    (payoff : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau → ℝ) :
    (∫ draw, ∫ fresh,
      payoff (physicalProgramRefresh source target U N P F A T thetaExponent H Q tau draw online group fresh)
      ∂(physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (.inl online)).prod
        (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (.inr group))
      ∂physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau) =
      ∫ draw, payoff draw ∂physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau := by
  classical
  exact finite_pi_integral_update_pair
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau)
    (.inl online) (.inr group) payoff


end GlobalLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramNodeRegret
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau
local notation "localLaw" =>
  Measure.prod (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inl onlineKey))
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inr groupKey))
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau

include hN hell hM hMeq hPeq hFeq hbeq hQeq hthetaeq hHeq hH hsize hP hF hA hseed hT
  hdelta hη hκ hκhalf hleaf hscale hcell hnonempty hspecified hget hb hquery hc htau hηrange herror bernstein

/-- The actual complete program has the node budget in its original
finite product law. The two selected arrays are independently refreshed,
and all complete child histories stay fixed. -/
theorem physicalProgram_global_node_regret_oai (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node.1) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    (∫ draw : Draw, (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta (choices draw)
        node.1 (t + 1) q : ℝ) - charge -
      physicalComparisonClipped source target U N P F A T delta (choices draw)
        node.1 node.2 comparison (t + 1))) ∂globalLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * c := by
  let c : ℝ := stateEditCost (physicalSource source node.1) target q
  let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
  let payoff : Draw → ℝ := fun draw => ∑ t ∈ range S,
    (max c (physicalRefinement source target U N P F A T delta (choices draw)
      node.1 (t + 1) q : ℝ) - charge -
      physicalComparisonClipped source target U N P F A T delta (choices draw)
        node.1 node.2 comparison (t + 1))
  change (∫ draw, payoff draw ∂globalLaw) ≤ physicalProgramNodeCoefficient N F η κ delta S H * c
  rw [← physicalProgramDrawLaw_refresh_integral source target U N P F A T thetaExponent H Q tau
    onlineKey groupKey payoff]
  have hlocal (draw : Draw) : (∫ fresh : Fresh, payoff (refresh draw onlineKey groupKey fresh) ∂localLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * c := by
    have hbound := physicalProgram_conditional_node_regret source target N hN hell hM hMeq hPeq hFeq
      eb hbeq hQeq hthetaeq hHeq hH U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
      node hleaf representative scale hscale cell cellIndex hcell hnonempty specified hspecified hget
      q hb hquery comparison hc htau hηrange herror bernstein draw S
    have hpayoff (fresh : Fresh) : payoff (refresh draw onlineKey groupKey fresh) =
        ∑ t ∈ range S, (max c
          (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
            node.1 (t + 1) q : ℝ) - charge -
          physicalComparisonClipped source target U N P F A T delta (choices draw)
            node.1 node.2 comparison (t + 1)) := by
      dsimp only [payoff]
      rw [physicalProgramRefresh_clipped source target U N P F A T thetaExponent H Q tau delta η κ
        node representative scale cellIndex draw fresh comparison]
    simp_rw [hpayoff]
    have hbudget := unskipped_expected_regret_budget source target N hN (by omega : 42 ≤ inputSmallLog N)
      hMeq hPeq (physicalSourceInterval source.length node.1) tau (F : ℚ)
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2)
      specified (Nat.cast_nonneg F) c hb η κ delta hη hκ S H
    apply hbound.trans
    simpa only [physicalProgramNodeCoefficient, Rat.cast_natCast] using hbudget
  have hmean := integral_mono (μ := globalLaw) (.of_finite) (.of_finite) hlocal
  simpa only [integral_const, probReal_univ, one_smul] using hmean

end Node

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgram_global_node_regret_oai.{u_1} := @OAI.EditApproximation.physicalProgram_global_node_regret_oai.{u_1}

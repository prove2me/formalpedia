-- Prove2me | solution 1 for OAI.EditApproximation.rationalPhysicalWarmup_cast
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:36.436253+00:00
-- url     : https://prove2.me/submissions/981d42e7-9113-47c9-86de-ebdfcdca13cc

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea004

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Rational execution of the Bellman and refinement operations

Every finite minimum, cone cost, warmup iteration, and refinement update
is computed in rational arithmetic. The real analysis used elsewhere is
the exact cast of these operations. An absent online candidate returns
the cone minimum, avoiding an extended-real value in the implementation.
-/

namespace EditApproximation





theorem rationalActionValue_cast {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (query : Parent) (action : RationalBellmanAction Parent Child M) :
    (rationalActionValue distance L child query action : ℝ) =
      bellmanActionValue (fun q r => (distance q r : ℝ)) (L : ℝ)
        (fun s => (child s : ℝ)) query action.toReal := by
  simp only [rationalActionValue, bellmanActionValue, RationalBellmanAction.toReal,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sum]

theorem rationalBellman_cast {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ) (query : Parent) :
    (rationalBellman fallback distance L actions child query : ℝ) =
      finiteBellman (fun q => (fallback q : ℝ)) (fun q r => (distance q r : ℝ)) (L : ℝ)
        (actions.map RationalBellmanAction.toReal) (fun s => (child s : ℝ)) query := by
  rw [rationalBellman, rationalMinimum_cast]
  unfold finiteBellman
  simp only [List.map_map, Function.comp_def, rationalActionValue_cast]

theorem rationalWarmup_cast {State : Type*}
    (operator : (State → ℚ) → State → ℚ) (realOperator : (State → ℝ) → State → ℝ)
    (initial : State → ℚ)
    (hoperator : ∀ value q, (operator value q : ℝ) = realOperator (fun s => (value s : ℝ)) q)
    (t : ℕ) (q : State) :
    (rationalWarmup operator initial t q : ℝ) = warmup realOperator (fun s => (initial s : ℝ)) t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [rationalWarmup, warmup, hoperator]
    congr 1
    funext s
    exact ih s



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRationalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



theorem rationalActualWideActions_toReal {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    (rationalActualWideActions (M := M) parent representatives P).map RationalBellmanAction.toReal =
      actualWideActions (M := M) parent representatives P := by
  simp only [rationalActualWideActions, actualWideActions, List.map_flatMap,
    List.map_map, Function.comp_def, RationalBellmanAction.toReal, Rat.cast_natCast]

theorem rationalPhysicalBellman_cast {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℚ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalBellman source target P L initial representatives value state : ℝ) =
      physicalBellman source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives
        (fun s => (value s : ℝ)) state := by
  classical
  unfold rationalPhysicalBellman physicalBellman
  dsimp only
  split_ifs
  · rfl
  · rw [rationalBellman_cast, rationalActualWideActions_toReal]
    simp only [actualWideBellman, Rat.cast_natCast]
  · rfl

theorem rationalPhysicalWarmup_cast_oai {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (t : ℕ) (state : PhysicalEntry M J target.length) :
    (rationalPhysicalWarmup source target P L initial representatives t state : ℝ) =
      physicalWarmup source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives t state :=
  rationalWarmup_cast _ _ _ (rationalPhysicalBellman_cast source target P L initial representatives) t state

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.rationalPhysicalWarmup_cast_oai.{u_1} := @OAI.EditApproximation.rationalPhysicalWarmup_cast_oai.{u_1}

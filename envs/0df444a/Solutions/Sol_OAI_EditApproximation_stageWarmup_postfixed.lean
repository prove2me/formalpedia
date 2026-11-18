-- Prove2me | solution 1 for OAI.EditApproximation.stageWarmup_postfixed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:38.455902+00:00
-- url     : https://prove2.me/submissions/4e598b2c-223b-4647-adcb-09265f58e3da

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmup_cast

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

theorem finiteMinimum_le_fallback (fallback : ℝ) (values : List ℝ) :
    finiteMinimum fallback values ≤ fallback := by
  induction values with
  | nil => rfl
  | cons v rest ih => exact (min_le_right _ _).trans ih

theorem finiteBellman_le_fallback {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ) (query : Parent) :
    finiteBellman fallback distance L actions child query ≤ fallback query :=
  finiteMinimum_le_fallback _ _

theorem finiteBellman_mono {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) {child child' : Child → ℝ}
    (hchild : child ≤ child') :
    finiteBellman fallback distance L actions child ≤
      finiteBellman fallback distance L actions child' := by
  intro query
  apply finiteMinimum_map_mono _ _ _ _ _ le_rfl
  intro action _
  exact add_le_add le_rfl (sum_le_sum fun i _ => hchild (action.childState i))

theorem warmup_nonincreasing {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (hmono : Monotone operator) (hfirst : operator initial ≤ initial) :
    ∀ t, warmup operator initial (t + 1) ≤ warmup operator initial t := by
  intro t
  induction t with
  | zero => exact hfirst
  | succ t ih => exact hmono ih

end EditApproximation

end OAI
end

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmup
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Warmup on physical node labels

The Bellman operator requests only physical children. Distinct child labels
are retained even at repeated cuts. Nodes at the last physical level, and
source intervals of width at most one, retain their initial value.
-/

namespace EditApproximation









theorem physicalBellman_monotone {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    Monotone (physicalBellman source target P L initial representatives) := by
  classical
  intro value value' hvalue state
  unfold physicalBellman
  dsimp only
  split_ifs
  · exact le_rfl
  · apply finiteBellman_mono
    intro is
    exact hvalue _
  · exact le_rfl

theorem physicalBellman_le_initial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) :
    physicalBellman source target P L initial representatives value ≤ initial := by
  classical
  intro state
  unfold physicalBellman
  dsimp only
  split_ifs
  · exact le_rfl
  · exact finiteBellman_le_fallback _ _ _ _ _ _
  · exact le_rfl

theorem physicalWarmup_nonincreasing {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ∀ t, physicalWarmup source target P L initial representatives (t + 1) ≤
      physicalWarmup source target P L initial representatives t :=
  warmup_nonincreasing _ _ (physicalBellman_monotone source target P L initial representatives)
    (physicalBellman_le_initial source target P L initial representatives initial)

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementInvariants
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic Bellman invariants of the complete physical recurrence. -/

namespace EditApproximation

theorem stageWarmup_postfixed_oai {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (state : PhysicalEntry M J target.length) :
    rationalPhysicalBellman source target P (128 * F) (stageInitial source target U N P F A)
        (stageRepresentatives source target U N P F A)
        (stageWarmup source target U N P F A T) state ≤
      stageWarmup source target U N P F A T state := by
  have h := physicalWarmup_nonincreasing source target P ((128 * F : ℚ) : ℝ)
    (fun s => (stageInitial source target U N P F A s : ℝ))
    (stageRepresentatives source target U N P F A) T state
  apply (Rat.cast_le (K := ℝ)).mp
  rw [rationalPhysicalBellman_cast]
  simpa only [stageWarmup, rationalPhysicalWarmup_cast, physicalWarmup, warmup] using h

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.stageWarmup_postfixed_oai.{u_1} := @OAI.EditApproximation.stageWarmup_postfixed_oai.{u_1}

-- Prove2me | solution 1 for OAI.EditApproximation.localScheduledSeedNext_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:28.121866+00:00
-- url     : https://prove2.me/submissions/aea49a73-612a-42d4-a333-114e30040808

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed

section
-- module Solutions.OAIQ361V3_EA.Compat
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct bounded-range enumeration of the cells meeting a query square. -/

namespace EditApproximation



theorem localCellCoordinates_complete (side : ℚ) (hside : 0 < side)
    (p radius r : ℕ) (hr : Nat.dist p r ≤ radius) :
    ⌊(r : ℚ) / side⌋₊ ∈ localCellCoordinates side p radius := by
  have hbounds : p - radius ≤ r ∧ r ≤ p + radius := by unfold Nat.dist at hr; omega
  have hlo := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (show ((p - radius : ℕ) : ℚ) ≤ r by exact_mod_cast hbounds.1) hside.le)
  have hhi := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (show (r : ℚ) ≤ (p + radius : ℕ) by exact_mod_cast hbounds.2) hside.le)
  unfold localCellCoordinates
  apply List.mem_range'.mpr
  refine ⟨⌊(r : ℚ) / side⌋₊ - ⌊((p - radius : ℕ) : ℚ) / side⌋₊, ?_, ?_⟩ <;> omega



theorem localTargetCells_complete {n : ℕ} (side : ℚ) (hside : 0 < side)
    (radius : ℕ) (q r : TargetInterval n)
    (hlo : Nat.dist q.lo r.lo ≤ radius) (hhi : Nat.dist q.hi r.hi ≤ radius) :
    targetCell side r ∈ localTargetCells side radius q := by
  apply List.mem_flatMap.mpr
  refine ⟨⌊(r.lo : ℚ) / side⌋₊, localCellCoordinates_complete side hside _ _ _ hlo, ?_⟩
  exact List.mem_map.mpr ⟨⌊(r.hi : ℚ) / side⌋₊, localCellCoordinates_complete side hside _ _ _ hhi, rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalWideStep
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One literal refinement update with finite selected-group cones and online action values. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_map_mono {ι : Type*} (indices : List ι)
    (fallback fallback' : ℚ) (value value' : ι → ℚ)
    (hfallback : fallback ≤ fallback') (hvalue : ∀ i ∈ indices, value i ≤ value' i) :
    rationalMinimum fallback (indices.map value) ≤ rationalMinimum fallback' (indices.map value') := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem rationalBellman_mono {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) {child child' : Child → ℚ}
    (hchild : child ≤ child') (q : Parent) :
    rationalBellman fallback distance L actions child q ≤ rationalBellman fallback distance L actions child' q := by
  apply rationalMinimum_map_mono _ _ _ _ _ le_rfl
  intro action _
  exact add_le_add le_rfl (sum_le_sum fun i _ => hchild (action.childState i))

theorem rationalBellman_le_action {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ)
    (q : Parent) (action : RationalBellmanAction Parent Child M) (haction : action ∈ actions) :
    rationalBellman fallback distance L actions child q ≤ rationalActionValue distance L child q action :=
  rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)



theorem rationalOnlineMinimum_lower (lower : ℚ) (values : List ℚ)
    (hvalues : ∀ v ∈ values, lower ≤ v) {online : ℚ}
    (honline : rationalOnlineMinimum values = some online) : lower ≤ online := by
  cases values with
  | nil => cases honline
  | cons first rest =>
    have heq : rationalMinimum first rest = online := Option.some.inj honline
    rw [← heq]
    exact (le_rationalMinimum_iff _ _ _).2
      ⟨hvalues first (by simp), fun v hv => hvalues v (by simp [hv])⟩

/-- Both lower candidates are genuine current-child wide Bellman cones.
The sampled choices enter only through literal membership in the wide list. -/
theorem rationalWideStep_bellman_sandwich {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ) (hmono : current ≤ old)
    (groups online : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (hgroups : ∀ action ∈ groups, action ∈ rationalActualWideActions parent representatives P)
    (honline : ∀ action ∈ online, action ∈ rationalActualWideActions parent representatives P)
    (q : TargetInterval ny) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent representatives P) current q ≤
      rationalWideStep parent representatives P initial L delta old current groups online q ∧
    rationalWideStep parent representatives P initial L delta old current groups online q ≤
      rationalBellman initial (fun q r => targetEndpointDistance q r) L
        (rationalActualWideActions parent representatives P) old q := by
  let actions := rationalActualWideActions (M := M) parent representatives P
  let distance := fun q r : TargetInterval ny => (targetEndpointDistance q r : ℚ)
  let lower := rationalBellman initial distance L actions current q
  let upper := rationalBellman initial distance L actions old q
  let cone := rationalWideStepCone parent representatives P initial L old current groups q
  have hcone : lower ≤ cone := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalBellman_mono initial distance L actions hmono q, ?_⟩
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    exact rationalBellman_le_action initial distance L actions current q action (hgroups action ha)
  have hupper : cone ≤ upper := rationalMinimum_le_fallback _ _
  have honlineLower : ∀ value ∈ online.map (rationalActionValue distance L current q), lower ≤ value := by
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    exact rationalBellman_le_action initial distance L actions current q action (honline action ha)
  change lower ≤ rationalRefinementUpdate delta cone
      (rationalOnlineMinimum (online.map (rationalActionValue distance L current q))) ∧
    rationalRefinementUpdate delta cone
      (rationalOnlineMinimum (online.map (rationalActionValue distance L current q))) ≤ upper
  cases hmin : rationalOnlineMinimum (online.map (rationalActionValue distance L current q)) with
  | none => exact ⟨hcone, hupper⟩
  | some value =>
    have hlower := rationalOnlineMinimum_lower lower _ honlineLower hmin
    exact ⟨le_min hcone (hlower.trans (le_max_right _ _)), (min_le_left _ _).trans hupper⟩

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





theorem physicalRefinement_succ {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    let children : PhysicalChildTables M target.length := fun i =>
      physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
    physicalRefinement source target U N P F A T delta choices node (t + 1) q =
      rationalWideStep (physicalSourceInterval source.length node)
        (stageRepresentatives source target U N P F A node) P
        (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
        (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
        (choices.groups node children (t + 1)) (choices.online node children (t + 1) q) q := by
  rw [physicalRefinement]
  rw [dite_eq_left hbelow, ite_eq_right hleaf]

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

theorem stageWarmup_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (t : ℕ) (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    stageWarmup source target U N P F A t (node, q) =
      stageInitial source target U N P F A (node, q) := by
  cases t with
  | zero => rfl
  | succ t =>
    change rationalPhysicalBellman source target P (128 * F) _ _ _ (node, q) = _
    unfold rationalPhysicalBellman
    dsimp only
    rcases hterminal with hlast | hleaf
    · rw [dite_eq_right hlast]
    · split_ifs <;> rfl

theorem physicalRefinement_at_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hterminal : ¬ node.1.val < J ∨ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stageInitial source target U N P F A (node, q) := by
  rw [physicalRefinement]
  rcases hterminal with hlast | hleaf
  · rw [dite_eq_right hlast]
  · split_ifs <;> rfl

theorem physicalRefinement_zero {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node 0 q =
      stageWarmup source target U N P F A T (node, q) := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf),
        stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
    · rw [physicalRefinement, dite_eq_left hbelow, ite_eq_right hleaf]
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow),
      stageWarmup_at_terminal _ _ _ _ _ _ _ _ node (Or.inl hbelow)]

/-- The full recurrence is postfixed for the current-child Bellman operator,
and each next value is at most the previous-child Bellman value. Selected
actions require only their literal wide-list membership certificates. -/
theorem physicalRefinement_bellman_invariants {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) :
    let value := fun t (s : PhysicalEntry M J target.length) =>
      physicalRefinement source target U N P F A T delta choices s.1 t s.2
    let bellman := rationalPhysicalBellman source target P (128 * F)
      (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
    ∀ t q, bellman (value t) (node, q) ≤ value t (node, q) ∧
      value (t + 1) (node, q) ≤ bellman (value t) (node, q) := by
  dsimp only
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · intro t q
      rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf),
        physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
      simp only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_left hleaf]
      exact ⟨le_rfl, le_rfl⟩
    · let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      have hchildren : ∀ t, (fun is : Fin M × TargetInterval target.length =>
          children is.1 (t + 1) is.2) ≤ fun is => children is.1 t is.2 := by
        intro t is
        have ih := physicalRefinement_bellman_invariants source target U N P F A T delta choices
          (physicalChild node hbelow is.1) t is.2
        exact ih.2.trans ih.1
      have hsandwich (t : ℕ) (q : TargetInterval target.length) :=
        rationalWideStep_bellman_sandwich (physicalSourceInterval source.length node)
          (stageRepresentatives source target U N P F A node) P
          (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
          (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
          (hchildren t) (choices.groups node children (t + 1)) (choices.online node children (t + 1) q)
          (choices.groups_mem node children (t + 1)) (choices.online_mem node children (t + 1) q) q
      intro t q
      constructor
      · cases t with
        | zero =>
          simp_rw [physicalRefinement_zero]
          exact stageWarmup_postfixed source target U N P F A T (node, q)
        | succ t =>
          rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
          simpa only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_right hleaf]
            using (hsandwich t q).1
      · rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
        simpa only [rationalPhysicalBellman, dite_eq_left hbelow, ite_eq_right hleaf]
          using (hsandwich t q).2
  · intro t q
    rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow),
      physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)]
    simp only [rationalPhysicalBellman, dite_eq_right hbelow]
    exact ⟨le_rfl, le_rfl⟩
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundsAllSeeds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

 theorem physicalRefinement_nonneg_all_seeds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal source target U N P F A T delta choices node (Or.inr hleaf)]
      exact stageInitial_nonneg_all_seeds source target U N P F A (node, q)
    · have hpost := (physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q).1
      have hnonneg : 0 ≤ rationalPhysicalBellman source target P (128 * F)
          (stageInitial source target U N P F A) (stageRepresentatives source target U N P F A)
          (fun state => physicalRefinement source target U N P F A T delta choices state.1 t state.2) (node, q) := by
        unfold rationalPhysicalBellman
        dsimp only
        rw [dite_eq_left hbelow, ite_eq_right hleaf]
        apply (le_rationalMinimum_iff _ _ _).2
        refine ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), ?_⟩
        intro v hv
        obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
        unfold rationalActionValue
        apply add_nonneg
        · exact add_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
            (rationalActualWideActions_connection_nonneg _ _ _ action ha)
        · apply sum_nonneg
          intro i _
          exact physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
            (physicalChild node hbelow (action.childState i).1) t (action.childState i).2
      exact hnonneg.trans hpost
  · rw [physicalRefinement_at_terminal source target U N P F A T delta choices node (Or.inl hbelow)]
    exact stageInitial_nonneg_all_seeds source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact candidate pruning uses value lower bounds, without an accuracy event. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_min_fallback (a b : ℚ) (values : List ℚ) :
    min a (rationalMinimum b values) = rationalMinimum (min a b) values := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
    simp only [rationalMinimum, ← ih]
    exact min_left_comm _ _ _

theorem rationalMinimum_local_complete_lt {ι : Type*} (complete nearby : List ι)
    (value : ι → ℚ) (fallback : ℚ)
    (hsubset : ∀ i ∈ nearby, i ∈ complete)
    (hcover : ∀ i ∈ complete, value i < fallback → i ∈ nearby) :
    rationalMinimum fallback (nearby.map value) = rationalMinimum fallback (complete.map value) := by
  apply le_antisymm
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    by_cases hvalue : value i < fallback
    · exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hcover i hi hvalue, rfl⟩)
    · exact (rationalMinimum_le_fallback _ _).trans (le_of_not_gt hvalue)
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hsubset i hi, rfl⟩)

theorem rationalMinimum_cons_fallback (fallback v : ℚ) (values : List ℚ) :
    rationalMinimum fallback (v :: values) = min fallback (rationalMinimum v values) := by
  change min v (rationalMinimum fallback values) = _
  rw [rationalMinimum_min_fallback, rationalMinimum_min_fallback, min_comm v fallback]

theorem rationalMinimum_map_max (lower fallback : ℚ) (values : List ℚ) :
    rationalMinimum (max lower fallback) (values.map (max lower)) =
      max lower (rationalMinimum fallback values) := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, rationalMinimum, ih, max_min_distrib_left]

theorem rationalRefinementUpdate_online_list (delta cone : ℚ) (values : List ℚ) :
    rationalRefinementUpdate delta cone (rationalOnlineMinimum values) =
      rationalMinimum cone (values.map (max (cone / (1 + delta)))) := by
  cases values with
  | nil => rfl
  | cons v rest =>
    simp only [rationalOnlineMinimum, rationalRefinementUpdate, List.map_cons,
      rationalMinimum_cons_fallback, rationalMinimum_map_max]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupCones
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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

/-- All improving complete cell cones occur in the bounded local cell
program. Identical cell keys use identical shared samples. -/
theorem localCellGroupMinimum_eq (q : TargetInterval target.length) (fallback : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F) (hfallback : fallback ≤ parentInitial q)
    (hcurrent : ∀ i r, 0 ≤ current i r)
    (hspatial : ∀ r, |parentInitial q - parentInitial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalMinimum fallback
        ((localCellGroupActions source target parent N P F exponent Q tau a parentInitial
          child initial current draw q).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => current is.1 is.2) q)) =
      rationalMinimum fallback
        ((completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
          child initial current draw).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => current is.1 is.2) q)) := by
  apply rationalMinimum_local_complete_lt
    _ _ _ fallback (localCellGroupActions_subset source target parent N P F exponent Q tau a
      parentInitial child initial current draw q)
  intro action haction hvalue
  have hwide := completeCellGroupActions_wide source target parent N P F exponent Q tau a
    parentInitial child initial current draw action haction
  have hcharge := rationalActionValue_pruned_lower (fun q r => targetEndpointDistance q r)
    (128 * (F : ℚ)) (fun is => current is.1 is.2) q action
    (128 * (F : ℚ) * targetEndpointDistance q action.center) le_rfl
    (rationalActualWideActions_connection_nonneg parent _ P action hwide) (fun i => hcurrent _ _)
  have hw : 0 < parentInitial q := by
    have hnonneg : (0 : ℚ) ≤ 128 * (F : ℚ) * targetEndpointDistance q action.center := by positivity
    exact hnonneg.trans_lt ((hcharge.trans_lt hvalue).trans_le hfallback)
  obtain ⟨b, hb, haction⟩ := List.mem_flatMap.mp haction
  obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp haction
  have hlocation := cellGroupAction_location source target parent N P F exponent Q tau a
    parentInitial child initial current draw b hb cell action hselected
  have hconditions := representativeList_conditions a parentInitial hlocation.1
  have hnumeric := refinement_cone_locality_numeric hw ha (show (1 : ℚ) ≤ F by exact_mod_cast hF)
    (Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q action.center)) (hspatial action.center)
    hconditions.2.2.2 le_rfl ((hcharge.trans hvalue.le).trans hfallback)
  have hdist : targetEndpointDistance q action.center ≤ ⌈parentInitial q⌉₊ := by
    exact_mod_cast hnumeric.2.2.trans (Nat.le_ceil _)
  have hbpos : 0 < b := by obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb; positivity
  have hcell := localTargetCells_complete (theta * b) (by positivity) ⌈parentInitial q⌉₊ q action.center
    (by unfold targetEndpointDistance at hdist; omega) (by unfold targetEndpointDistance at hdist; omega)
  rw [hlocation.2] at hcell
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨hb, decide_eq_true ⟨hnumeric.1, hnumeric.2.1⟩⟩, ?_⟩
  exact List.mem_filterMap.mpr ⟨cell, hcell, hselected⟩

end CellPrograms

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteKeyRestriction
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting independent finite key streams preserves their exact
product law. Unused keys need not be allocated by a lazy implementation. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_restrict_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key) :
    (Measure.pi mu).map (fun draw k => draw (key k)) =
      Measure.pi (fun k => mu (key k)) := by
  have hindependent : iIndepFun (fun i (draw : ∀ j, X j) => draw i) (Measure.pi mu) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hrestricted := hindependent.precomp hinjective
  have hmap := hrestricted.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (key k)).aemeasurable)
  simpa only [(measurePreserving_eval mu _).map_eq] using hmap

theorem finite_pi_restrict_image_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : κ → Type*} [∀ k, MeasurableSpace (Y k)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key)
    (image : ∀ k, X (key k) → Y k) (himage : ∀ k, Measurable (image k)) :
    (Measure.pi mu).map (fun draw k => image k (draw (key k))) =
      Measure.pi (fun k => (mu (key k)).map (image k)) := by
  have hrestrict := finite_pi_restrict_map mu key hinjective
  have hproject : Measurable (fun draw : ∀ i, X i => fun k => draw (key k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (key k))
  have htransform : Measurable (fun draw : ∀ k, X (key k) => fun k => image k (draw k)) :=
    Measurable.of_eval (fun k => (himage k).comp (measurable_pi_apply k))
  refine (Measure.map_map htransform hproject).symm.trans ?_
  rw [hrestrict]
  exact Measure.pi_map_pi (fun k => (himage k).aemeasurable)

theorem finite_uniform_array_cast (R n m : ℕ) [NeZero n] [NeZero m] (h : n = m) :
    (Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin n)).toMeasure)).map
      (fun draw t => Fin.cast h (draw t)) =
    Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin m)).toMeasure) := by
  subst m
  simp only [Fin.cast_refl, id_eq, Measure.map_id']

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineLocality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal query-filtered online loop has at most one candidate per scale. -/

namespace EditApproximation

open Finset

theorem makeTargetState_endpoints {n lo hi : ℕ} {q : TargetInterval n}
    (h : makeTargetState n lo hi = some q) : q.lo = lo ∧ q.hi = hi := by
  unfold makeTargetState at h
  split_ifs at h with hv
  · cases h
    exact ⟨rfl, rfl⟩

theorem targetStates_nodup (n : ℕ) : (targetStates n).Nodup := by
  unfold targetStates
  apply List.nodup_flatMap.mpr
  constructor
  · intro lo _
    apply (List.nodup_range (n := n + 1)).filterMap
    intro hi hi' q hq hq'
    have h := (makeTargetState_endpoints (Option.mem_def.mp hq)).2
    have h' := (makeTargetState_endpoints (Option.mem_def.mp hq')).2
    exact h.symm.trans h'
  · apply (List.nodup_range (n := n + 1)).imp
    intro lo lo' hne q hq hq'
    obtain ⟨hi, _, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨hi', _, hq'⟩ := List.mem_filterMap.mp hq'
    exact hne ((makeTargetState_endpoints hq).1.symm.trans (makeTargetState_endpoints hq').1)

theorem dyadicScales_nodup (N : ℕ) : (dyadicScales N).Nodup :=
  (List.nodup_range (n := Nat.log 2 N + 1)).map (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))

theorem representativeList_nodup {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) : (representativeList N P F a initial).Nodup := by
  unfold representativeList
  apply List.nodup_flatMap.mpr
  constructor
  · intro b _
    exact ((targetStates_nodup n).filter _).map (fun _ _ heq => congrArg Prod.snd heq)
  · apply (dyadicScales_nodup N).imp
    intro b b' hne pair hp hp'
    obtain ⟨r, _, heq⟩ := List.mem_map.mp hp
    obtain ⟨r', _, heq'⟩ := List.mem_map.mp hp'
    exact hne ((congrArg Prod.fst heq).trans (congrArg Prod.fst heq').symm)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalWideStep
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One concrete refinement entry, using direct local representative and
cell loops. Band data and previously gathered child tables are arguments;
no complete current-index child table is enumerated. -/

namespace EditApproximation

theorem rationalLocalWideStep_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hinitial : 0 ≤ parentInitial q) (hold : ∀ i r, 0 ≤ old i r) (hcurrent : ∀ i r, 0 ≤ current i r)
    (hspatial : ∀ r, |parentInitial q - parentInitial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
        childMass childInitial old current draw online q =
      rationalWideStep parent (representativeList N P F a parentInitial) P parentInitial (128 * F) delta
        (fun is => old is.1 is.2) (fun is => current is.1 is.2)
        (completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
          childMass childInitial current draw) online q := by
  have hbellman := localRefinementBellman_eq parent N P F a parentInitial
    (fun is => old is.1 is.2) q ha hF hinitial (fun is => hold is.1 is.2) hspatial
  have hgroups := localCellGroupMinimum_eq source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
    (rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
      (rationalActualWideActions parent (representativeList N P F a parentInitial) P)
      (fun is => old is.1 is.2) q) ha hF (rationalMinimum_le_fallback _ _) hcurrent hspatial
  unfold rationalLocalWideStep rationalWideStep rationalWideStepCone
  dsimp only
  rw [hbellman, hgroups]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset

theorem rationalRefinementUpdate_online_mem_ext {ι : Type*}
    (left right : List ι) (value : ι → ℚ) (delta cone : ℚ)
    (hmem : ∀ action, action ∈ left ↔ action ∈ right) :
    rationalRefinementUpdate delta cone (rationalOnlineMinimum (left.map value)) =
      rationalRefinementUpdate delta cone (rationalOnlineMinimum (right.map value)) := by
  simp only [rationalRefinementUpdate_online_list, List.map_map, Function.comp_def]
  apply rationalMinimum_local_complete right left
  · exact fun action ha => (hmem action).mp ha
  · exact fun action ha _ => (hmem action).mpr ha



theorem localOnlineCandidates_mem {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (action : PhysicalRationalAction M target.length) :
    action ∈ localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q ↔
    ∃ b, b ∈ dyadicQueryWindow N (parentInitial q) a F ∧
      (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a parentInitial ∧
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial
        children t (roundInterval (seedGridSpacing b P) q)
        (integer b (roundInterval (seedGridSpacing b P) q)) = some action := by
  unfold localOnlineCandidates
  constructor
  · intro ha
    obtain ⟨b, hb, hselected⟩ := List.mem_filterMap.mp ha
    dsimp only at hselected
    split_ifs at hselected with heligible
    refine ⟨b, hb, ?_, hselected⟩
    exact representativeList_mem a parentInitial _ (List.mem_filter.mp hb).1
      (roundInterval_on_grid _ q) heligible.1 heligible.2
  · rintro ⟨b, hb, hrep, hselected⟩
    have hc := representativeList_conditions a parentInitial hrep
    apply List.mem_filterMap.mpr
    refine ⟨b, hb, ?_⟩
    dsimp only
    rw [ite_eq_left hc.2.2.2]
    exact hselected

section Physical

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)

theorem keyedOnlineCandidate_eq_physical
    (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T exponent H tau node representative))) :
    keyedOnlineCandidate source target (physicalSourceInterval source.length node.1)
      P F exponent H ((stageRepresentatives source target U N P F A node.1).get representative).1
      tau eta kappa (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2) children t
      ((stageRepresentatives source target U N P F A node.1).get representative).2 integer.val =
    physicalProgramOnlineCandidate source target U N P F A T exponent H tau eta kappa
      node representative children t integer := by
  let G := keyedOnlineBandG source target (physicalSourceInterval source.length node.1)
    P exponent H ((stageRepresentatives source target U N P F A node.1).get representative).1 tau
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    ((stageRepresentatives source target U N P F A node.1).get representative).2
  have hG : 0 < G := keyedOnlineBandG_positive source target
    (physicalSourceInterval source.length node.1) P exponent H
    ((stageRepresentatives source target U N P F A node.1).get representative).1 tau
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    ((stageRepresentatives source target U N P F A node.1).get representative).2
  have haccept : boundedOnlineInteger (optimizerTriangularMass (G ^ 80))
      (optimizerTriangularMass_positive (G ^ 80) (pow_pos hG 80)) integer.val = integer := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt integer.isLt
  unfold keyedOnlineCandidate physicalProgramOnlineCandidate physicalBandOnlineCandidate
  dsimp only
  rw [haccept]
  dsimp only [physicalBandEnvelope, physicalProgramBandK, physicalProgramBandG,
    physicalBandActions, keyedOnlineBandG] at integer ⊢
  unfold physicalBandEnvelope
  dsimp only [physicalBandActions]
  congr 1
  funext hband
  split <;> simp_all only

end Physical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineEquality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof adapter couples the bounded online query loop to the original
finite product slots. The adapter is used only to compare laws: local
execution uses scale/center keys and never searches a complete table. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)

local notation "representatives" => stageRepresentatives source target U N P F A

theorem physicalRepresentativeFin_get (node : PhysicalNode M J)
    (br : ℕ × TargetInterval target.length) (hbr : br ∈ representatives node) :
    (representatives node).get (physicalRepresentativeFin source target U N P F A node br hbr) = br :=
  Classical.choose_spec (List.mem_iff_get.mp hbr)

omit [NeZero R] in
theorem physicalOnlineIntegersOfStreams_get (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (time : Fin R) :
    physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online node time
      ((representatives node.1).get representative).1 ((representatives node.1).get representative).2 =
      (online node representative time).val := by
  unfold physicalOnlineIntegersOfStreams
  rw [dite_eq_left (List.get_mem _ _)]
  have heq : physicalRepresentativeFin source target U N P F A node.1
      ((representatives node.1).get representative) (List.get_mem _ _) = representative := by
    apply (representativeList_nodup N P F _ _).injective_get
    exact physicalRepresentativeFin_get source target U N P F A node.1 _ _
  rw [heq]

theorem physicalLocalOnline_mem_iff
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalInternalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length) :
    action ∈ physicalLocalOnline source target U N P F exponent H T A tau eta kappa
        (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online)
        node.1 children t q ↔
      action ∈ physicalProgramOnline source target U N P F A T exponent H tau eta kappa
        online node.1 children t q := by
  have hmass : physicalLocalChildMass source target U N P F A T node.1 node.2 =
      physicalBandChildMassTable source target U N P F A T node.1 node.2 := by
    funext i r
    exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
      (physicalChild node.1 node.2 i, r)
  unfold physicalLocalOnline physicalProgramOnline
  rw [dite_eq_left node.2, dite_eq_left node.2]
  rw [localOnlineCandidates_mem]
  constructor
  · rintro ⟨b, hb, hrep, hselected⟩
    obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
    change (representatives node.1).get representative =
      (b, roundInterval (seedGridSpacing b P) q) at hget
    have hinteger := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau online
      node representative (Fin.ofNat R (t - 1))
    rw [hget] at hinteger
    rw [hmass, hinteger] at hselected
    have heq := keyedOnlineCandidate_eq_physical source target U N P F exponent H T A tau eta kappa
      node representative children (t - 1) (online node representative (Fin.ofNat R (t - 1)))
    rw [hget] at heq
    rw [heq] at hselected
    apply List.mem_filterMap.mpr
    refine ⟨representative, List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, hselected⟩
    apply decide_eq_true
    unfold physicalProgramOnlineGuard
    rw [hget]
    exact ⟨rfl, of_decide_eq_true (List.mem_filter.mp hb).2⟩
  · intro ha
    obtain ⟨representative, hrep, hselected⟩ := List.mem_filterMap.mp ha
    have hguard := of_decide_eq_true (List.mem_filter.mp hrep).2
    let br := (representatives node.1).get representative
    have hget : (representatives node.1).get representative =
        (br.1, roundInterval (seedGridSpacing br.1 P) q) := Prod.ext rfl hguard.1
    refine ⟨br.1, List.mem_filter.mpr ⟨?_, decide_eq_true hguard.2⟩, ?_, ?_⟩
    · exact representativeList_scale_mem _ _ (List.get_mem _ representative)
    · exact hget ▸ List.get_mem _ representative
    · have hinteger := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau online
        node representative (Fin.ofNat R (t - 1))
      rw [hget] at hinteger
      rw [hmass, hinteger]
      have heq := keyedOnlineCandidate_eq_physical source target U N P F exponent H T A tau eta kappa
        node representative children (t - 1) (online node representative (Fin.ofNat R (t - 1)))
      rw [hget] at heq
      exact heq.trans hselected

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

theorem physicalOnlineRawKey_injective :
    Function.Injective (physicalOnlineRawKey source target U N P F A) := by
  rintro ⟨node, representative⟩ ⟨node', representative'⟩ heq
  have hnode := congrArg Prod.fst heq
  change node = node' at hnode
  subst node'
  have hscale := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length =>
    (dyadicScales N).get key.2.1) heq
  have hcenter := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length => key.2.2) heq
  simp only [physicalOnlineRawKey, physicalScaleIndex_get] at hscale hcenter
  have hrep := (representativeList_nodup N P F _ _).injective_get (Prod.ext hscale hcenter)
  cases hrep
  rfl

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem list_eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] (items : List α) :
    items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons first rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, list_eraseDups_nodup _⟩
    intro hmem
    have hfalse := (List.mem_filter.mp (List.mem_eraseDups.mp hmem)).2
    simp at hfalse
termination_by items.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun item => !(item == first)) rest)



section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent : ℕ) (A : ℚ)

theorem physicalGroupRawKey_injective :
    Function.Injective (physicalGroupRawKey source target U N P F exponent A) := by
  rintro ⟨node, scale, cell⟩ ⟨node', scale', cell'⟩ heq
  have hn := congrArg Prod.fst heq
  change node = node' at hn
  subst node'
  have hs := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.1) heq
  change scale = scale' at hs
  subst scale'
  have hlo := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.1.val) heq
  have hhi := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.2.val) heq
  simp only [physicalGroupRawKey] at hlo hhi
  have hnodup : (physicalProgramCells source target U N P F A exponent node.1
      ((dyadicScales N).get scale)).Nodup := list_eraseDups_nodup _
  have hcell := hnodup.injective_get (Prod.ext hlo hhi)
  cases hcell
  rfl

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau : ℚ)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalLocalProgramOldKey_injective :
    Function.Injective (physicalLocalProgramOldKey source target U N P F A exponent) := by
  intro first second heq
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      exact congrArg Sum.inl
        (physicalOnlineRawKey_injective source target U N P F A (Sum.inl.inj heq))
    | inr second => exact False.elim (Sum.inl_ne_inr heq)
  | inr first =>
    cases second with
    | inl second => exact False.elim (Sum.inr_ne_inl heq)
    | inr second =>
      exact congrArg Sum.inr
        (physicalGroupRawKey_injective source target U N P F exponent A (Sum.inr.inj heq))

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

theorem physicalLocalProgramDrawLaw_map :
    (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau).map
      (physicalLocalProgramToComplete source target U N P F A T exponent H Q tau hsize hP hF hA hseed) =
    physicalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau := by
  have hmap := finite_pi_restrict_image_map
    (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau)
    (physicalLocalProgramOldKey source target U N P F A exponent)
    (physicalLocalProgramOldKey_injective source target U N P F A exponent)
    (physicalLocalProgramCoordinateImage source target U N P F A T exponent H Q tau hsize hP hF hA hseed)
    (fun _ => measurable_of_finite _)
  refine hmap.trans ?_
  unfold physicalProgramDrawLaw
  congr 1
  funext key
  cases key with
  | inl online =>
    exact finite_uniform_array_cast R _ _
      (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed online)
  | inr group => exact Measure.map_id

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite indexed group program has an equivalent cell-keyed
realization. Good initial seeds permit its whole cone to be evaluated
using only the directly enumerated query cells. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A : ℚ)

theorem physicalProgramCells_keyed (node : PhysicalNode M J) (b : ℕ) :
    physicalProgramCells source target U N P F A exponent node b =
      representativeCells N P F b (refinementFactor A F) ((2 : ℚ) ^ (-(exponent : ℤ)))
        (fun q => stageInitial source target U N P F A (node, q)) := rfl

theorem physicalProgramGroups_keyed (T : ℕ) (tau : ℚ) {R : ℕ} [NeZero R]
    (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (children : PhysicalChildTables M target.length) (t : ℕ) :
    physicalProgramGroups source target U N P F A T exponent Q tau
        (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw) node children t =
      completeCellGroupActions source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F)
        (fun q => stageInitial source target U N P F A (node, q))
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow)
        (fun i q => children i t q) (draw ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) := by
  unfold physicalProgramGroups
  rw [dite_eq_left hbelow]
  unfold completeCellGroupActions
  conv_rhs => rw [← List.map_get_finRange (dyadicScales N)]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro scale _
  rw [← physicalProgramCells_keyed source target U N P F exponent A node]
  conv_rhs => rw [← List.map_get_finRange (physicalProgramCells source target U N P F A exponent node
    ((dyadicScales N).get scale))]
  simp only [List.filterMap_map, Function.comp_def, physicalGroupStreamsOfKeys]

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRawGroupProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell draws are read by their bounded scale and endpoint keys.
No list of all representatives or cells is searched by the provider. -/

namespace EditApproximation

theorem physicalScaleIndex_of_get (N : ℕ) (scale : Fin (dyadicScales N).length) :
    physicalScaleIndex N ((dyadicScales N).get scale) (List.get_mem _ scale) = scale := by
  apply (dyadicScales_nodup N).injective_get
  exact physicalScaleIndex_get N _ _

theorem dependentKeyTransport {ι κ : Type*} (label : ι → κ) (family : κ → Type*)
    (value : ∀ index, family (label index)) (first second : ι)
    (heq : first = second) (hlabel : label first = label second) :
    Eq.mp (congrArg family hlabel) (value first) = value second := by
  subst second
  rfl

section Agreement

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A : ℚ)
  (draw : ∀ key : PhysicalLocalGroupKey M J N target.length exponent,
    PhysicalLocalGroupArray M J N target.length exponent F Q R key)

theorem physicalRawGroupDraws_get
    (key : PhysicalGroupKey source target U N P F A exponent) (time : Fin R) :
    physicalRawGroupDraws M J N target.length exponent F Q R draw key.1 time
        ((dyadicScales N).get key.2.1)
        ((physicalProgramCells source target U N P F A exponent key.1.1
          ((dyadicScales N).get key.2.1)).get key.2.2) =
      draw (physicalGroupRawKey source target U N P F exponent A key) time := by
  have hcell := physicalProgramCells_bounds source target U N P F exponent A key.1.1
    ((dyadicScales N).get key.2.1) (physicalGroupScale_positive source target U N P F exponent A key)
    _ (List.get_mem _ key.2.2)
  simp only [physicalRawGroupDraws, dite_eq_left (List.get_mem _ key.2.1), dite_eq_left hcell]
  exact dependentKeyTransport (fun scale => (dyadicScales N).get scale)
    (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
      (fun h => groupSampleCount M Q b (groupDyadicScaleAt M b F h)))
    (fun scale => draw (key.1, scale,
      ⟨_, Nat.lt_succ_of_le hcell.1⟩, ⟨_, Nat.lt_succ_of_le hcell.2⟩) time)
    _ key.2.1 (physicalScaleIndex_of_get N key.2.1)
    (physicalScaleIndex_get N _ (List.get_mem _ key.2.1))

theorem physicalGroupStreamsOfRaw :
    physicalGroupStreamsOfKeys source target U N P F exponent Q A
        (physicalRawGroupDraws M J N target.length exponent F Q R draw) =
      fun node scale cell => draw
        (physicalGroupRawKey source target U N P F exponent A ⟨node, scale, cell⟩) := by
  funext node scale cell time
  exact physicalRawGroupDraws_get source target U N P F exponent Q A draw ⟨node, scale, cell⟩ time

end Agreement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalRefinementEquality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On good seeds, the query-local recurrence equals the complete refinement recurrence. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q H T : ℕ) (A tau delta eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)
  (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)

local notation "provider" => physicalProgramOnline source target U N P F A T exponent H tau eta kappa online
local notation "choices" => physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa online
  (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw)
local notation "localDraw" => (fun node t => draw node (Fin.ofNat R (t - 1)))

theorem physicalLocalRefinement_keyed_eq
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T localDraw provider node t q =
      physicalRefinement source target U N P F A T delta choices node t q := by
  rw [physicalLocalRefinement, physicalRefinement]
  split_ifs with hbelow hleaf
  · rfl
  · have hchild (i : Fin M) : physicalLocalRefinement source target U N P F exponent Q A tau delta T
        localDraw provider (physicalChild node hbelow i) =
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i) := by
      funext s r
      exact physicalLocalRefinement_keyed_eq hsize hP hF hA hseed (physicalChild node hbelow i) s r
    dsimp only
    simp_rw [hchild]
    cases t with
    | zero => exact physicalLocalWarmup_eq source target U N P F A hsize hP hF hA hseed T (node, q)
    | succ t =>
      let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      have hmass : physicalLocalChildMass source target U N P F A T node hbelow =
          physicalBandChildMassTable source target U N P F A T node hbelow := by
        funext i r
        exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
          (physicalChild node hbelow i, r)
      have hfactor := refinementFactor_spec A F (by omega : 0 < F)
      have hspatial : ∀ r, |stageInitial source target U N P F A (node, q) -
          stageInitial source target U N P F A (node, r)| ≤ 32 * F * targetEndpointDistance q r := by
        intro r
        have hqr := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed node q r
        have hrq := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed node r q
        have hsym : targetEndpointDistance r q = targetEndpointDistance q r := by
          exact congrArg₂ (· + ·) (Nat.dist_comm _ _) (Nat.dist_comm _ _)
        rw [hsym] at hrq
        apply abs_le.mpr
        constructor <;> dsimp only [stageInitial] <;> linarith only [hqr, hrq]
      have hold (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i t r :=
        physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
          (physicalChild node hbelow i) t r
      have hcurrent (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i (t + 1) r :=
        physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
          (physicalChild node hbelow i) (t + 1) r
      have hstep := rationalLocalWideStep_eq source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (Fin.ofNat R t)) (provider node children (t + 1) q) q
        hfactor.1 hF (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hold hcurrent hspatial
      rw [hmass] at hstep
      have hkey := physicalProgramGroups_keyed source target U N P F exponent Q A T tau draw node hbelow children (t + 1)
      simp only [Nat.add_sub_cancel] at hkey
      unfold physicalBandChildInitial at hkey
      rw [← hkey] at hstep
      change rationalLocalWideStep source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (Fin.ofNat R t)) (provider node children (t + 1) q) q = _
      rw [hmass]
      exact hstep
  · rfl
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramEquality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete refinement is reproduced, on good incoming seeds, by
bounded cell and rounded-center loops with local warmup data throughout. -/

namespace EditApproximation

theorem physicalLocalRefinement_online_mem_congr {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (left right : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (hmem : ∀ node children t q action,
      action ∈ left node children t q ↔ action ∈ right node children t q)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw left node t q =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw right node t q := by
  rw [physicalLocalRefinement, physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · rfl
  · have hchild (i : Fin M) : physicalLocalRefinement source target U N P F exponent Q A tau delta T
        draw left (physicalChild node hbelow i) =
        physicalLocalRefinement source target U N P F exponent Q A tau delta T
          draw right (physicalChild node hbelow i) := by
      funext s r
      exact physicalLocalRefinement_online_mem_congr source target U N P F exponent Q A tau delta T
        draw left right hmem (physicalChild node hbelow i) s r
    dsimp only
    simp_rw [hchild]
    cases t with
    | zero => rfl
    | succ t =>
      unfold rationalLocalWideStep
      dsimp only
      apply rationalRefinementUpdate_online_mem_ext
      exact hmem _ _ _ _
  · rfl
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q H T : ℕ) (A tau delta eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)
  (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)

local notation "localDraw" => (fun node t => draw node (Fin.ofNat R (t - 1)))
local notation "localProvider" => physicalLocalOnline source target U N P F exponent H T A tau eta kappa
  (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online)
local notation "provider" => physicalProgramOnline source target U N P F A T exponent H tau eta kappa online
local notation "choices" => physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa online
  (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw)

theorem physicalLocalProgram_eq
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T localDraw localProvider node t q =
      physicalRefinement source target U N P F A T delta choices node t q := by
  have hmem : ∀ label children s r action,
      action ∈ localProvider label children s r ↔ action ∈ provider label children s r := by
    intro label children s r action
    by_cases hbelow : label.1.val < J
    · exact physicalLocalOnline_mem_iff source target U N P F exponent H T A tau eta kappa online
        hsize hP hF hA hseed ⟨label, hbelow⟩ children s r action
    · simp only [physicalLocalOnline, physicalProgramOnline, dite_eq_right hbelow, List.not_mem_nil]
  rw [physicalLocalRefinement_online_mem_congr source target U N P F exponent Q A tau delta T
    localDraw localProvider provider hmem node t q]
  exact physicalLocalRefinement_keyed_eq source target U N P F exponent Q H T A tau delta eta kappa
    online draw hsize hP hF hA hseed node t q

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRawOnlineProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local online provider reads a scale/center key directly; the
complete representative index identifies the corresponding action. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau eta kappa : ℚ)
  (draw : PhysicalLocalOnlineDraw source target U N P F A R T exponent H tau)

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

omit [NeZero R] in
theorem physicalRawOnlineIntegers_get (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
    (time : Fin R) :
    physicalRawOnlineIntegers source target U N P F A T exponent H tau draw node time
        ((stageRepresentatives source target U N P F A node.1).get representative).1
        ((stageRepresentatives source target U N P F A node.1).get representative).2 =
      (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
        hsize hP hF hA hseed node representative time).val := by
  unfold physicalRawOnlineIntegers physicalOnlineStreamsOfRaw
  rw [dite_eq_left (representativeList_scale_mem _ _ (List.get_mem _ representative))]
  exact (Fin.val_cast
    (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau
      hsize hP hF hA hseed ⟨node, representative⟩)
    (draw (physicalOnlineRawKey source target U N P F A ⟨node, representative⟩) time)).symm

theorem physicalRawOnline_eq_adapter :
    physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalRawOnlineIntegers source target U N P F A T exponent H tau draw) =
    physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau
        (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
          hsize hP hF hA hseed)) := by
  funext node children t q
  unfold physicalLocalOnline
  split_ifs with hbelow
  · apply localOnlineCandidates_integer_congr
    intro b _hb hrep
    obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
    change (stageRepresentatives source target U N P F A node).get representative =
      (b, roundInterval (seedGridSpacing b P) q) at hget
    have hraw := physicalRawOnlineIntegers_get source target U N P F A T exponent H tau draw
      hsize hP hF hA hseed ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1))
    have hold := physicalOnlineIntegersOfStreams_get source target U N P F exponent H T A tau
      (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
        hsize hP hF hA hseed) ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1))
    rw [hget] at hraw hold
    exact hraw.trans hold.symm
  · rfl

theorem physicalRawOnlineProgram_eq (Q : ℕ) (delta : ℚ)
    (groups : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T
      (fun label s => groups label (Fin.ofNat R (s - 1)))
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa
        (physicalRawOnlineIntegers source target U N P F A T exponent H tau draw)) node t q =
    physicalRefinement source target U N P F A T delta
      (physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa
        (physicalOnlineStreamsOfRaw source target U N P F A T exponent H tau draw
          hsize hP hF hA hseed)
        (physicalGroupStreamsOfKeys source target U N P F exponent Q A groups)) node t q := by
  rw [physicalRawOnline_eq_adapter source target U N P F A T exponent H tau eta kappa draw
    hsize hP hF hA hseed]
  exact physicalLocalProgram_eq source target U N P F exponent Q H T A tau delta eta kappa
    _ groups hsize hP hF hA hseed node t q

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalJointProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct evaluation from the bounded joint random source agrees with
complete refinement. All complete-table indexing occurs in the proof. -/

namespace EditApproximation

section Joint

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau)

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

theorem physicalLocalJointValue_eq (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    physicalLocalJointValue source target U N P F A T exponent H Q tau eta kappa delta draw node t q =
      physicalRefinement source target U N P F A T delta
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa
          (physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
            hsize hP hF hA hseed draw)) node t q := by
  unfold physicalLocalJointValue
  rw [physicalRawOnlineProgram_eq source target U N P F A T exponent H tau eta kappa
    (fun key => draw (.inl key)) hsize hP hF hA hseed]
  rw [physicalGroupStreamsOfRaw]
  rfl

end Joint

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalMedianDrawLaw
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local bounded-key random source implements the same whole-table
median pass as the complete program. Copies are independent, while all
entries within a copy retain their shared online and group draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Median

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (a S copies : ℕ)

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalLocalMedianUpdateTable_eq
    (draws : Fin copies → PhysicalLocalProgramDraw (R := R)
      source target U N P F A T exponent H Q tau) :
    physicalLocalMedianUpdateTable source target U N P F A T exponent H Q tau eta kappa delta
        a S copies draws =
      physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)
        (fun i => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
          hsize hP hF hA hseed (draws i)) := by
  funext state
  apply Fin.ext
  change min N (upperMedian (List.ofFn fun i : Fin copies =>
    ⌈(a : ℚ) * physicalLocalJointValue source target U N P F A T exponent H Q
      tau eta kappa delta (draws i) state.1 S state.2⌉₊)) = _
  apply congrArg (fun values : Fin copies → ℕ => min N (upperMedian (List.ofFn values)))
  funext i
  rw [physicalLocalJointValue_eq source target U N P F A T exponent H Q tau eta kappa delta
    (draws i) hsize hP hF hA hseed]
  rfl

omit [NeZero R] in
/-- The restriction to used keys preserves independence between complete
program copies, as well as the law of each copy. -/
theorem physicalLocalProgramCopyDrawLaw_map :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).map
      (fun draws i => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
        hsize hP hF hA hseed (draws i)) =
      Measure.pi (fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau) := by
  classical
  let : IsProbabilityMeasure (physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau) := by
    unfold physicalLocalProgramDrawLaw
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmap := physicalLocalProgramDrawLaw_map (R := R)
    source target U N P F A T exponent H Q tau hsize hP hF hA hseed
  have hcopies := Measure.pi_map_pi
    (μ := fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau)
    (f := fun _ => physicalLocalProgramToComplete source target U N P F A T exponent H Q tau
      hsize hP hF hA hseed)
    (fun _ => (measurable_of_finite _).aemeasurable)
  simpa only [hmap] using hcopies

include hsize hP hF hA hseed in
/-- Equality of the entire returned seed-table distribution. No independent
per-entry resampling is introduced by replacing complete copies with local
bounded-key copies. -/
theorem physicalLocalMedianUpdateTable_law :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).map
      (physicalLocalMedianUpdateTable source target U N P F A T exponent H Q tau eta kappa delta
        a S copies) =
      (Measure.pi fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau).map
      (physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)) := by
  classical
  rw [← physicalLocalProgramCopyDrawLaw_map source target U N P F A T exponent H Q tau copies
    hsize hP hF hA hseed]
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  congr 1
  funext draws
  exact physicalLocalMedianUpdateTable_eq source target U N P F A T exponent H Q tau eta kappa
    delta a S copies hsize hP hF hA hseed draws

include hsize hP hF hA hseed in
/-- Any whole-seed event, including the simultaneous good-seed event, has
the same probability for the actual local median pass. -/
theorem physicalLocalMedianUpdateTable_event
    (event : Set (ClampedPhysicalSeed M J target.length N)) :
    (Measure.pi fun _ : Fin copies => physicalLocalProgramDrawLaw (R := R)
      source target U N P F A T exponent H Q tau).real
      {draws | physicalLocalMedianUpdateTable source target U N P F A T exponent H Q
        tau eta kappa delta a S copies draws ∈ event} =
      (Measure.pi fun _ : Fin copies => physicalProgramDrawLaw (R := R)
        source target U N P F A T exponent H Q tau).real
      {draws | physicalMedianUpdateTable source target U N P F A T delta a S copies
        (physicalProgramDrawSelections source target U N P F A T exponent H Q tau eta kappa)
        draws ∈ event} := by
  classical
  have h := congrArg (fun law : Measure (ClampedPhysicalSeed M J target.length N) => law.real event)
    (physicalLocalMedianUpdateTable_law (R := R) source target U N P F A T exponent H Q tau eta kappa delta
      a S copies hsize hP hF hA hseed)
  rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite event).measurableSet,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite event).measurableSet] at h
  exact h

end Median

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.rationalParametersWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed schedule run with bounded local random keys. A whole incoming
seed chooses one fresh product of full-copy local streams. The failure
bound follows from the actual local median law, rather than a seed oracle. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hPeq hsize in
theorem localScheduledSeedNext_event_oai (pass : ℕ) (seed : Seed)
    (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed)
    (event : Set Seed) :
    (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | localScheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} =
    (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | scheduledSeedNext (R := R) source target N P T S H pass seed draw ∈ event} := by
  have hP : 66 ≤ P := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hA : (1 : ℚ) ≤ scheduledSeedFactor N pass := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  exact physicalLocalMedianUpdateTable_event (R := R) source target (clampedSeedNat seed)
    N P ell (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau eta kappa delta
    (scheduledSeedMultiplier N pass) S (H ^ 2) hsize hP hF hA hseed event

end Program

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.localScheduledSeedNext_event_oai.{u_1} := @OAI.EditApproximation.localScheduledSeedNext_event_oai.{u_1}

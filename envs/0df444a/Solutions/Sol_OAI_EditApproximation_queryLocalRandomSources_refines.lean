-- Prove2me | solution 1 for OAI.EditApproximation.queryLocalRandomSources_refines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:39.497199+00:00
-- url     : https://prove2.me/submissions/58667a7f-4070-42dd-851d-f0f9af3b30ea

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
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
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryGroupSelectWithWork_value
import Theorems.Thm_OAI_EditApproximation_queryRefinementGather_refines

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem rationalPowerWithWork_spec (r : ℚ) (n : ℕ) :
    rationalPowerWithWork r n = (r ^ n, n) := by
  induction n with
  | zero => simp [rationalPowerWithWork]
  | succ n ih => simp [rationalPowerWithWork, ih, pow_succ]

theorem rationalLogPartialWithWork_spec (b : ℚ) (K : ℕ) :
    rationalLogPartialWithWork b K =
      (∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1 : ℕ), K * K + 2 * K) := by
  induction K with
  | zero => simp [rationalLogPartialWithWork]
  | succ K ih =>
    simp only [rationalLogPartialWithWork, ih, rationalPowerWithWork_spec, sum_range_succ]
    congr 1
    ring

/-- The actual logarithm evaluator uses exactly a quadratic number of
rational arithmetic operations and returns the already verified value. -/
theorem rationalLogApproximationWithWork_spec (r : ℚ) (K : ℕ) :
    rationalLogApproximationWithWork r K =
      (rationalLogApproximation r K, K * K + 2 * K + 4) := by
  simp [rationalLogApproximationWithWork, rationalLogPartialWithWork_spec, rationalLogApproximation]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedNumerics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

theorem logarithmPartial_value (b : UnreducedRational) (K : ℕ) :
    (logarithmPartial b K).value =
      ∑ k ∈ range K, b.value ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  induction K with
  | zero => simp [logarithmPartial]
  | succ K ih => simp [logarithmPartial, ih, sum_range_succ]

@[simp] theorem logarithm_value (r : UnreducedRational) (K : ℕ) :
    (logarithm r K).value = rationalLogApproximation r.value K := by
  simp [logarithm, logarithmPartial_value, rationalLogApproximation]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActionVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual fixed-block action hull

Coordinates are precisely the child/state pairs occurring in a finite band.
Each action assigns its fixed rational child mass to one state per child.
This verifies the probability, coverage and block-mass hypotheses used by
the numerical optimizer and optimistic entropy regret.
-/

namespace EditApproximation

open Finset





theorem action_coordinate_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) {action : β → σ} (haction : action ∈ band) (child : β) :
    (child, action child) ∈ bandCoordinates band := by
  apply mem_biUnion.mpr
  exact ⟨action, haction, mem_image.mpr ⟨child, mem_univ _, rfl⟩⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_VectorOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialized rational optimizer iterates. Finite vectors store the
previous iterate and its gradient, and a scored scan stores the current
best score. Counters charge rational arithmetic, comparisons, array
accesses and array writes. Integer/rational bit costs are separate. -/

namespace EditApproximation

open Finset

theorem naturalPowerWithWork_spec (a k : ℕ) : naturalPowerWithWork a k = (a ^ k, k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [naturalPowerWithWork, ih, pow_succ]

theorem vectorDotListWithWork_spec {d : ℕ} (left right : Vector ℚ d) (indices : List (Fin d)) :
    vectorDotListWithWork left right indices =
      ((indices.map fun i => left.get i * right.get i).sum, 8 * indices.length) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [vectorDotListWithWork, ih, List.map_cons, List.sum_cons, List.length_cons]
    congr 1

theorem vectorDotWithWork_spec {d : ℕ} (left right : Vector ℚ d) :
    vectorDotWithWork left right = (∑ i : Fin d, left.get i * right.get i, 8 * d) := by
  simp only [vectorDotWithWork, vectorDotListWithWork_spec, List.length_finRange]
  congr 1

theorem rationalGradientCellWithWork_spec {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) :
    rationalGradientCellWithWork G linear point i =
      (rationalSmoothedGradient G linear.get point.get i, G ^ 120 + 2 * G ^ 60 + 121) := by
  simp only [rationalGradientCellWithWork, rationalPowerWithWork_spec, naturalPowerWithWork_spec,
    rationalLogApproximationWithWork_spec, rationalSmoothedGradient]
  congr 1
  rw [show (120 : ℕ) = 60 * 2 by rfl, pow_mul]
  ring

theorem vectorGradientWithWork_value {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) :
    (vectorGradientWithWork G linear point).1.get i =
      rationalSmoothedGradient G linear.get point.get i := by
  rw [vectorGradientWithWork, vectorMapWithWork_value, rationalGradientCellWithWork_spec]

theorem scoredArgmaxWithWork_value {α : Type*} (score : α → ℚ × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1) with
    | none => rfl
    | some best => simp only [Option.map_some]; split_ifs <;> rfl

theorem vectorMaximizerWithWork_value {d : ℕ} (gradient : Vector ℚ d)
    (vertices : List (Vector ℚ d)) :
    (vectorMaximizerWithWork gradient vertices).1.get =
      rationalLinearizationMaximizer univ (vertices.map Vector.get) gradient.get := by
  have hmap := argmax_map_commutes (fun vertex : Vector ℚ d => vertex.get)
    (fun vertex => ∑ i : Fin d, gradient.get i * vertex i) vertices
  simp only [vectorMaximizerWithWork, scoredArgmaxWithWork_value, vectorDotWithWork_spec,
    Option.map_map, Function.comp_def] at hmap ⊢
  unfold rationalLinearizationMaximizer
  rw [hmap]
  cases h : vertices.argmax (fun vertex => ∑ i : Fin d, gradient.get i * vertex.get i) with
  | none => funext i; exact Vector.getElem_replicate i.isLt
  | some selected => rfl

theorem materializedOptimizerWithWork_value {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G j : ℕ) :
    (materializedOptimizerWithWork vertices linear G j).1.get =
      finiteRationalOptimizer univ (vertices.map Vector.get) linear.get G j := by
  induction j with
  | zero =>
    cases vertices with
    | nil => funext i; exact Vector.getElem_replicate i.isLt
    | cons vertex rest => rfl
  | succ j ih =>
    funext i
    simp only [materializedOptimizerWithWork, vectorMapWithWork_value, finiteRationalOptimizer]
    rw [congrFun ih i, vectorMaximizerWithWork_value]
    congr 2
    congr 1
    funext k
    rw [vectorGradientWithWork_value, ih]

theorem materializedSelectionWithWork_value {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) :
    (materializedSelectionWithWork vertices linear G j).1 =
      (vertices.argmax fun vertex =>
        ∑ i : Fin d, rationalSmoothedGradient G linear.get
          (finiteRationalOptimizer univ ((vertices.map Prod.snd).map Vector.get) linear.get G j) i *
          vertex.2.get i).map Prod.fst := by
  simp only [materializedSelectionWithWork, scoredArgmaxWithWork_value,
    vectorDotWithWork_spec, Option.map_map, Function.comp_def]
  congr 2
  funext vertex
  apply sum_congr rfl
  intro i _
  rw [vectorGradientWithWork_value, materializedOptimizerWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedOptimizer
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.nat_representation _root_.OAI.EditApproximation.BinaryFraction.representation_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fraction-only implementation of the actual finite optimizer. None of
its arithmetic or score comparisons requires reduced rational numbers. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

theorem scoredArgmax_spec {α : Type*} (score : α → UnreducedRational) (values : List α) :
    scoredArgmax score values =
      (values.argmax (fun a => (score a).value)).map (fun a => (a, score a)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmax, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).value) with
    | none => rfl
    | some best => simp only [Option.map_some, lt_eq_true]; split_ifs <;> rfl

theorem gradient_value {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) (i : Fin d) :
    ((gradient G linear point).get i).value =
      rationalSmoothedGradient G (fun i => (linear.get i).value) (fun i => (point.get i).value) i := by
  simp [gradient, gradientCell, rationalSmoothedGradient, one_div]

theorem maximizer_value {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) :
    (fun i => ((maximizer gradient vertices).get i).value) =
      rationalLinearizationMaximizer univ
        (vertices.map fun vertex i => (vertex.get i).value) (fun i => (gradient.get i).value) := by
  have hmap := argmax_map_commutes (fun vertex : Vector UnreducedRational d => fun i => (vertex.get i).value)
    (fun vertex => ∑ i, (gradient.get i).value * vertex i) vertices
  simp only [maximizer, scoredArgmax_spec, dot_value, Option.map_map, Function.comp_def]
  unfold rationalLinearizationMaximizer
  rw [hmap]
  cases h : vertices.argmax (fun vertex => ∑ i, (gradient.get i).value * (vertex.get i).value) with
  | none => funext i; simp [value_zero]
  | some vertex => rfl

theorem finiteOptimizer_value {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K : ℕ) :
    (fun i => ((finiteOptimizer vertices linear G K).get i).value) =
      finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
        (fun i => (linear.get i).value) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil => funext i; simp [finiteOptimizer, finiteRationalOptimizer]
    | cons vertex rest => rfl
  | succ K ih =>
    funext i
    simp only [finiteOptimizer, vector_get_ofFn, value_add, value_mul, value_sub, value_one,
      optimizerStep_value, finiteRationalOptimizer]
    rw [congrFun ih i]
    have hm := maximizer_value (gradient G linear (finiteOptimizer vertices linear G K)) vertices
    have hg : (fun i => ((gradient G linear (finiteOptimizer vertices linear G K)).get i).value) =
        rationalSmoothedGradient G (fun i => (linear.get i).value)
          (finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
            (fun i => (linear.get i).value) G K) := by
      funext i
      rw [gradient_value]
      rw [ih]
    rw [hg] at hm
    rw [congrFun hm i]

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFractionWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Unreduced fractions stored as Boolean words. Every numerator operation
below runs the literal signed ripple/shift-add code; denominator products
run the literal Boolean multiplication routine. -/

namespace EditApproximation



namespace BinaryFraction







theorem neg_value (a : BinaryFraction) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawNumerics
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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



theorem powWithWork_representation (a : BinaryFraction) (k : ℕ) :
    (a.powWithWork k).1.representation = a.representation.pow k := by
  induction k with
  | zero => exact one_representation
  | succ k ih => simp only [powWithWork, canonicalMulWithWork_representation,
      UnreducedRational.pow, ih]



theorem logarithmPartialWithWork_representation (b : BinaryFraction) (k : ℕ) :
    (b.logarithmPartialWithWork k).1.representation = b.representation.logarithmPartial k := by
  induction k with
  | zero => exact zero_representation
  | succ k ih => simp only [logarithmPartialWithWork, canonicalAddWithWork_representation,
      divWithWork_representation, powWithWork_representation, nat_representation,
      UnreducedRational.logarithmPartial, ih]



theorem logarithmWithWork_representation (r : BinaryFraction) (k : ℕ) :
    (r.logarithmWithWork k).1.representation = r.representation.logarithm k := by
  simp only [logarithmWithWork, canonicalMulWithWork_representation,
    logarithmPartialWithWork_representation, divWithWork_representation,
    subWithWork_representation, canonicalAddWithWork_representation,
    nat_representation, one_representation, UnreducedRational.logarithm]



theorem gradientCellWithWork_representation {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) :
    (gradientCellWithWork G linear point i).1.representation =
      UnreducedRational.gradientCell G (linear.map representation) (point.map representation) i := by
  simp only [gradientCellWithWork, canonicalAddWithWork_representation,
    subWithWork_representation, logarithmWithWork_representation, neg_representation,
    one_representation, invWithWork_representation, powWithWork_representation,
    nat_representation, UnreducedRational.gradientCell, vector_map_get]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRawOptimizer
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete materialized entropy optimizer on Boolean fraction storage.
Every arithmetic operation invokes the counted Boolean implementation. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



theorem gradientWithWork_representation {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    (gradientWithWork G linear point).1.map representation =
      UnreducedRational.gradient G (linear.map representation) (point.map representation) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change ((gradientWithWork G linear point).1.get ⟨i, hi⟩).representation =
    (UnreducedRational.gradient G (linear.map representation) (point.map representation)).get ⟨i, hi⟩
  rw [gradientWithWork, vectorMapWithWork_value]
  simpa only [UnreducedRational.gradient, vector_get_ofFn] using
    gradientCellWithWork_representation G linear point ⟨i, hi⟩



theorem scoredArgmaxWithWork_value {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1.value)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1.value) with
    | none => rfl
    | some best => simp only [Option.map_some, ltWithWork_value]; split_ifs <;> rfl



theorem maximizerWithWork_representation {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    (maximizerWithWork gradient vertices).1.map representation =
      UnreducedRational.maximizer (gradient.map representation) (vertices.map fun v => v.map representation) := by
  have hscore (v : Vector BinaryFraction d) :
      (dotWithWork gradient v).1.value =
        (UnreducedRational.dot (gradient.map representation) (v.map representation)).value := by
    rw [← dotWithWork_representation, representation_value]
  have hmap := argmax_map_commutes (fun v : Vector BinaryFraction d => v.map representation)
    (fun v => (UnreducedRational.dot (gradient.map representation) v).value) vertices
  simp only [maximizerWithWork, scoredArgmaxWithWork_value, hscore, Option.map_map,
    Function.comp_def, UnreducedRational.maximizer, UnreducedRational.scoredArgmax_spec]
  rw [hmap]
  cases h : vertices.argmax (fun v =>
      (UnreducedRational.dot (gradient.map representation) (v.map representation)).value) with
  | none =>
    apply Vector.ext
    intro i hi
    simp [zero_representation]
  | some v => rfl



theorem optimizerUpdateWithWork_representation {d : ℕ} (j : ℕ)
    (previous selected : Vector BinaryFraction d) (i : Fin d) :
    ((optimizerUpdateWithWork j previous selected).1.get i).representation =
      ((UnreducedRational.one.sub (UnreducedRational.optimizerStep j)).mul
        (previous.get i).representation).add
      ((UnreducedRational.optimizerStep j).mul (selected.get i).representation) := by
  simp only [optimizerUpdateWithWork, vectorMapWithWork_value,
    canonicalAddWithWork_representation, canonicalMulWithWork_representation,
    subWithWork_representation, divWithWork_representation, nat_representation,
    one_representation, UnreducedRational.optimizerStep]



theorem finiteOptimizerWithWork_representation {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (finiteOptimizerWithWork vertices linear G K).1.map representation =
      UnreducedRational.finiteOptimizer (vertices.map fun v => v.map representation)
        (linear.map representation) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil =>
      apply Vector.ext
      intro i hi
      simp [finiteOptimizerWithWork, UnreducedRational.finiteOptimizer, zero_representation]
    | cons v vs => rfl
  | succ K ih =>
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    change (((optimizerUpdateWithWork K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear
        (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1).1.get ⟨i, hi⟩).representation) = _
    rw [optimizerUpdateWithWork_representation]
    have hg := gradientWithWork_representation G linear (finiteOptimizerWithWork vertices linear G K).1
    rw [ih] at hg
    have hm := maximizerWithWork_representation
      (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    rw [hg] at hm
    have hp := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) ih
    have hs := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) hm
    simpa only [UnreducedRational.finiteOptimizer, vector_map_get, Vector.getElem_ofFn] using
      congrArg₂ UnreducedRational.add
        (congrArg (UnreducedRational.mul (UnreducedRational.one.sub (UnreducedRational.optimizerStep K))) hp)
        (congrArg (UnreducedRational.mul (UnreducedRational.optimizerStep K)) hs)

theorem finiteOptimizerWithWork_value {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (fun i => ((finiteOptimizerWithWork vertices linear G K).1.get i).value) =
      finiteRationalOptimizer univ (vertices.map fun v i => (v.get i).value)
        (fun i => (linear.get i).value) G K := by
  have h := finiteOptimizerWithWork_representation vertices linear G K
  have hvalue := UnreducedRational.finiteOptimizer_value
    (vertices.map fun v => v.map representation) (linear.map representation) G K
  rw [← h] at hvalue
  simpa only [vector_map_get, representation_value, List.map_map, Function.comp_def] using hvalue

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryActionSelection
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The final Boolean maximization retains the actual action label. This
is the sampled atom of the optimizer, rather than its averaged vector. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem dotWithWork_value {d : ℕ} (left right : Vector BinaryFraction d) :
    (dotWithWork left right).1.value = ∑ i, (left.get i).value * (right.get i).value := by
  rw [← representation_value, dotWithWork_representation, UnreducedRational.dot_value]
  simp only [vector_map_get, representation_value]

theorem gradientWithWork_value {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) (i : Fin d) :
    ((gradientWithWork G linear point).1.get i).value =
      rationalSmoothedGradient G (fun j => (linear.get j).value) (fun j => (point.get j).value) i := by
  have h := congrArg (fun v : Vector UnreducedRational d => (v.get i).value)
    (gradientWithWork_representation G linear point)
  simp only [vector_map_get, representation_value, UnreducedRational.gradient_value] at h
  simpa only [vector_map_get, representation_value] using h



theorem selectionWithWork_value {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G j : ℕ) :
    (selectionWithWork vertices linear G j).1 =
      (materializedSelectionWithWork
        (vertices.map fun v => (v.1, v.2.map value)) (linear.map value) G j).1 := by
  rw [materializedSelectionWithWork_value, argmax_map_commutes]
  simp only [selectionWithWork, scoredArgmaxWithWork_value, Option.map_map, Function.comp_def]
  apply congrArg (fun score => (vertices.argmax score).map Prod.fst)
  funext vertex
  rw [dotWithWork_value]
  have hget (v : Vector BinaryFraction d) : (v.map value).get = fun i => (v.get i).value := by
    funext i
    exact vector_map_get value v i
  simp only [gradientWithWork_value, finiteOptimizerWithWork_value,
    List.map_map, vector_map_get, Function.comp_def, hget]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

theorem restrictOptimizerVector_get {ι : Type*} {d : ℕ} (coordinates : Vector ι d)
    (values : ι → ℚ) (i : Fin d) :
    (restrictOptimizerVector coordinates values).get i = values (coordinates.get i) :=
  vector_get_ofFn _ _

theorem coordinateVector_sum {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup) (f : ι → ℚ) :
    (∑ i : Fin d, f (coordinates.get i)) = ∑ c ∈ coordinates.toList.toFinset, f c := by
  rw [List.sum_toFinset f hnodup]
  have hcoordinates : coordinates.toList = List.ofFn coordinates.get := by
    rw [← Vector.toList_ofFn]
    congr 1
    exact (Vector.ofFn_getElem).symm
  rw [hcoordinates, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rationalLinearizationMaximizer_restrict {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) :
    rationalLinearizationMaximizer univ
      (vertices.map fun v => fun i => v (coordinates.get i))
      (fun i => gradient (coordinates.get i)) =
    fun i => rationalLinearizationMaximizer coordinates.toList.toFinset vertices gradient
      (coordinates.get i) := by
  have hsum (v : ι → ℚ) :
      (∑ i : Fin d, gradient (coordinates.get i) * v (coordinates.get i)) =
        ∑ c ∈ coordinates.toList.toFinset, gradient c * v c :=
    coordinateVector_sum coordinates hnodup (fun c => gradient c * v c)
  unfold rationalLinearizationMaximizer
  rw [argmax_map_commutes]
  simp only [hsum]
  cases h : vertices.argmax (fun v => ∑ c ∈ coordinates.toList.toFinset, gradient c * v c) with
  | none => rfl
  | some v => rfl

theorem finiteRationalOptimizer_restrict {ι : Type*} [DecidableEq ι] {d : ℕ}
    (coordinates : Vector ι d) (hnodup : coordinates.toList.Nodup)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer univ (vertices.map fun v => fun i => v (coordinates.get i))
        (fun i => linear (coordinates.get i)) G j =
      fun i => finiteRationalOptimizer coordinates.toList.toFinset vertices linear G j
        (coordinates.get i) := by
  induction j with
  | zero => cases vertices <;> rfl
  | succ j ih =>
    have hgradient :
        rationalSmoothedGradient G (fun i => linear (coordinates.get i))
          (finiteRationalOptimizer univ (vertices.map fun v => fun i => v (coordinates.get i))
            (fun i => linear (coordinates.get i)) G j) =
        fun i => rationalSmoothedGradient G linear
          (finiteRationalOptimizer coordinates.toList.toFinset vertices linear G j)
          (coordinates.get i) := by
      rw [ih]
      rfl
    funext i
    rw [finiteRationalOptimizer, finiteRationalOptimizer, hgradient,
      rationalLinearizationMaximizer_restrict coordinates hnodup]
    simp only [ih]

/-- Concrete ordered coordinates; no enumeration of the ambient state
type and no choice of an equivalence is used by the evaluator. -/


theorem listedBandCoordinates_nodup {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) : (listedBandCoordinates band).Nodup :=
  List.nodup_dedup _

theorem listedBandCoordinates_toFinset {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).toFinset = bandCoordinates band.toFinset := by
  ext coordinate
  constructor
  · intro hc
    obtain ⟨action, ha, hc⟩ := List.mem_flatMap.mp
      (List.mem_dedup.mp (List.mem_toFinset.mp hc))
    obtain ⟨child, hchild⟩ := List.mem_ofFn.mp hc
    rw [← hchild]
    exact action_coordinate_mem band.toFinset (List.mem_toFinset.mpr ha) child
  · intro hc
    obtain ⟨action, ha, hc⟩ := mem_biUnion.mp hc
    obtain ⟨child, _, heq⟩ := mem_image.mp hc
    apply List.mem_toFinset.mpr
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨action, List.mem_toFinset.mp ha, List.mem_ofFn.mpr ⟨child, heq⟩⟩

theorem listedBandCoordinateVector_toList {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinateVector band).toList = listedBandCoordinates band := by
  simp only [listedBandCoordinateVector, Vector.toList_ofFn, List.ofFn_get]

theorem listedBandCoordinates_length {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) :
    (listedBandCoordinates band).length = (bandCoordinates band.toFinset).card := by
  rw [← listedBandCoordinates_toFinset band,
    List.toFinset_card_of_nodup (listedBandCoordinates_nodup band)]

/-- Materializing coordinates and vertices preserves the actual action
label selected by the complete finite optimizer, including all ties. -/
theorem materializedBandActionWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (band : List (Fin M → σ)) (hband : band ≠ []) (mass : Fin M → ℚ)
    (linear : Fin M × σ → ℚ) (G j : ℕ) :
    (materializedBandActionWithWork band mass linear G j).1.getD (band.head hband) =
      finiteOptimizerAction band hband mass linear G j := by
  let coordinates := listedBandCoordinateVector band
  have hnodup : coordinates.toList.Nodup := by
    rw [show coordinates.toList = listedBandCoordinates band from
      listedBandCoordinateVector_toList band]
    exact listedBandCoordinates_nodup band
  have hcoordinates : coordinates.toList.toFinset = bandCoordinates band.toFinset := by
    rw [show coordinates.toList = listedBandCoordinates band from
      listedBandCoordinateVector_toList band, listedBandCoordinates_toFinset]
  have hvertexMaps :
      (((band.map fun action => (action, restrictOptimizerVector coordinates (actionVector mass action))).map
        Prod.snd).map Vector.get) =
      (band.map (actionVector mass)).map (fun v => fun i => v (coordinates.get i)) := by
    simp only [List.map_map]
    congr 1
    funext action i
    exact restrictOptimizerVector_get coordinates _ i
  have hlinear : (restrictOptimizerVector coordinates linear).get =
      fun i => linear (coordinates.get i) := by
    funext i
    exact restrictOptimizerVector_get coordinates linear i
  have hscore (action : Fin M → σ) :
      (∑ i : Fin (listedBandCoordinates band).length,
        rationalSmoothedGradient G (restrictOptimizerVector coordinates linear).get
          (finiteRationalOptimizer univ
            (((band.map fun action => (action, restrictOptimizerVector coordinates (actionVector mass action))).map
              Prod.snd).map Vector.get) (restrictOptimizerVector coordinates linear).get G j) i *
          (restrictOptimizerVector coordinates (actionVector mass action)).get i) =
        ∑ c ∈ bandCoordinates band.toFinset,
          rationalSmoothedGradient G linear
            (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass))
              linear G j) c * actionVector mass action c := by
    rw [hvertexMaps, hlinear, finiteRationalOptimizer_restrict coordinates hnodup]
    simp only [restrictOptimizerVector_get]
    change (∑ i, rationalSmoothedGradient G linear
      (finiteRationalOptimizer coordinates.toList.toFinset (band.map (actionVector mass)) linear G j)
      (coordinates.get i) * actionVector mass action (coordinates.get i)) = _
    have hs := coordinateVector_sum coordinates hnodup (fun c =>
      rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates.toList.toFinset (band.map (actionVector mass)) linear G j) c *
          actionVector mass action c)
    simpa only [hcoordinates] using hs
  unfold materializedBandActionWithWork
  rw [materializedSelectionWithWork_value, argmax_map_commutes]
  simp only [Function.comp_def, Option.map_map]
  rw [show (fun x : Fin M → σ => x) = id from rfl, Option.map_id]
  simp only [finiteOptimizerAction]
  apply congrArg (fun result : Option (Fin M → σ) => result.getD (band.head hband))
  apply congrArg (fun score : (Fin M → σ) → ℚ => band.argmax score)
  funext action
  exact hscore action

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wordInsertWithWork_value _root_.OAI.EditApproximation.wordLEWithWork_value _root_.OAI.EditApproximation.wordMinWithWork_value _root_.OAI.EditApproximation.wordSortWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Actual Boolean construction of the normalized band vertices.
The input masses are stored fractions; their sum and divisions use the
counted routines and no reduced-rational conversion is performed. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem bandCoordinateWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (action : Fin M → σ) (coordinate : Fin M × σ) :
    (bandCoordinateWithWork mass (bandMassTotalWithWork mass).1 action coordinate).1.value =
      actionVector (fun i => (mass.get i).value) action coordinate := by
  unfold bandCoordinateWithWork actionVector
  split_ifs
  · rw [← representation_value, divWithWork_representation,
      UnreducedRational.value_div, representation_value, representation_value,
      bandMassTotalWithWork_value]
  · simp [zero, value, SignedBinary.value, signedMagnitude, bitWordValue]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineInputs
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual optimistic linear objective constructed from stored Boolean
fractions, using counted sums, products and divisions. No reduced-rational
conversion is used between the table inputs and the optimizer. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

@[simp] theorem gainWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (s : ℕ) (i : β × σ) :
    (gainWithWork mass table s i).1.value =
      childGain (fun j => (mass j).value) (fun t j => (table t j).value) s i := by
  simp only [gainWithWork, divWithWork_value, neg_value, childGain]

theorem onlineLinearWithWork_value {β σ : Type*} (mass : β → BinaryFraction)
    (table : ℕ → β × σ → BinaryFraction) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) :
    (onlineLinearWithWork mass table eta kappa t i).1.value =
      rationalOnlineLinear eta.value kappa.value (childGain (fun j => (mass j).value)
        (fun s j => (table s j).value))
        (childDecrement (fun j => (mass j).value) (fun s j => (table s j).value)) t i := by
  simp only [onlineLinearWithWork, canonicalMulWithWork_value, canonicalAddWithWork_value,
    bandMassTotalWithWork_value, vectorMapWithWork_value, optimisticTermWithWork,
    coefficientWithWork_value, gainWithWork_value, decrementWithWork_value]
  unfold rationalOnlineLinear rationalOptimisticHistory
  congr 2
  exact Fin.sum_univ_eq_sum_range (fun s => childGain (fun j => (mass j).value)
    (fun s j => (table s j).value) s i + (1 - 2 * kappa.value) *
      childDecrement (fun j => (mass j).value) (fun s j => (table s j).value) s i) t

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandAction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Materialized Boolean vertices retain their band labels. The resulting
selected action, including every tie, is the action used by the online
sampler in the accuracy development. -/

namespace EditApproximation
namespace BinaryFraction

theorem labeledBandVerticesWithWork_values {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (band : List (Fin M → σ)) :
    (labeledBandVerticesWithWork coordinates mass band).1.map
        (fun pair => (pair.1, pair.2.map value)) =
      band.map (fun action => (action,
        restrictOptimizerVector coordinates (actionVector (fun j => (mass.get j).value) action))) := by
  simp only [labeledBandVerticesWithWork, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro action _
  apply Prod.ext
  · rfl
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change ((vectorMapWithWork (α := BinaryFraction) d _).1.get ⟨i, hi⟩).value =
    (restrictOptimizerVector coordinates (actionVector (fun j => (mass.get j).value) action)).get ⟨i, hi⟩
  rw [vectorMapWithWork_value, bandCoordinateWithWork_value, restrictOptimizerVector_get]

theorem preparedBandActionWithWork_value {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (hband : band ≠ []) (G j t : ℕ) :
    (preparedBandActionWithWork mass table eta kappa band G j t).1.getD (band.head hband) =
      finiteOptimizerAction band hband (fun i => (mass.get i).value)
        (rationalOnlineLinear eta.value kappa.value
          (childGain (fun i => (mass.get i).value) (fun s i => (table s i).value))
          (childDecrement (fun i => (mass.get i).value) (fun s i => (table s i).value)) t) G j := by
  let coordinates := listedBandCoordinateVector band
  let linear := rationalOnlineLinear eta.value kappa.value
    (childGain (fun i => (mass.get i).value) (fun s i => (table s i).value))
    (childDecrement (fun i => (mass.get i).value) (fun s i => (table s i).value)) t
  have hl : (vectorMapWithWork _ (fun i => onlineLinearWithWork
      (fun k => mass.get k) table eta kappa t (coordinates.get i))).1.map value =
        restrictOptimizerVector coordinates linear := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    change ((vectorMapWithWork (α := BinaryFraction) _ _).1.get ⟨i, hi⟩).value =
      (restrictOptimizerVector coordinates linear).get ⟨i, hi⟩
    rw [vectorMapWithWork_value, onlineLinearWithWork_value, restrictOptimizerVector_get]
  change (selectionWithWork (labeledBandVerticesWithWork coordinates mass band).1
    (vectorMapWithWork _ (fun i => onlineLinearWithWork
      (fun k => mass.get k) table eta kappa t (coordinates.get i))).1 G j).1.getD _ = _
  rw [selectionWithWork_value, labeledBandVerticesWithWork_values, hl]
  exact materializedBandActionWithWork_value band hband (fun i => (mass.get i).value) linear G j

theorem bandActionWithWork_value {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny))
    (hband : band ≠ []) (G j t : ℕ) (hb : 0 < b) :
    (bandActionWithWork b initial table eta kappa band G j t).1.getD (band.head hband) =
      finiteOptimizerAction band hband (bandChildEnvelope b band (fun i q => (initial i q).value))
        (rationalOnlineLinear eta.value kappa.value
          (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
            (fun s i => (table s i).value))
          (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
            (fun s i => (table s i).value)) t) G j := by
  change (preparedBandActionWithWork (envelopeVectorWithWork b band initial).1
    table eta kappa band G j t).1.getD _ = _
  rw [preparedBandActionWithWork_value]
  have hm : (fun i => ((envelopeVectorWithWork b band initial).1.get i).value) =
      bandChildEnvelope b band (fun i q => (initial i q).value) := by
    funext i
    exact envelopeVectorWithWork_value b band initial hb i
  rw [hm]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGroupKernel
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal group estimates on gathered stored fractions. Each child/scale
comparison is executed, the supplied draw indices are reused, and ordered
selection uses the same tie rule as the mathematical group program. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



@[simp] theorem selectGroupWithWork_value {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) :
    (selectGroupWithWork members hne estimate).1 =
      selectGroupMember members hne (fun member => (estimate member).1.value) := by
  simp only [selectGroupWithWork, scoredArgmaxWithWork_value, neg_value,
    Option.map_map, Function.comp_def, selectGroupMember]
  congr 1
  cases members.argmax (fun member => -(estimate member).1.value) <;> rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPhysicalContinuation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The local refinement return is computed by the binary-fraction
continuation. Wide actions are built from the emitted endpoint grids, and
their connection charges are evaluated before the two Bellman minima. -/

namespace EditApproximation
namespace BinaryFraction



theorem physicalContinuationWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (hP : 0 < P) :
    (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).1.value =
      rationalWideStep parent representatives P (fun _ => fallback.value) (128 * F) delta.value
        (fun s => (old s).value) (fun s => (current s).value)
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  simp only [physicalContinuationWithWork, localContinuationWithWork_value,
    wideActionsFromRepresentativesWithWork_decode M parent representatives P hP,
    endpointDistanceWithWork_value, canonicalMulWithWork_value, nat_value]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnline
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite uniform source integer is passed through the actual triangular
search and the actual stored-fraction optimizer. The returned zero-connection
physical action has exactly the online sampler's value, including ties. -/

namespace EditApproximation
namespace BinaryFraction

theorem sampledOnlineActionWithWork_value {ny M : ℕ} (center : TargetInterval ny) (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) (hb : 0 < b) :
    (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).1.decode =
      sharedBandRationalAction center
        (finiteOptimizerActionDraw band hne (bandChildEnvelope b band (fun i q => (initial i q).value))
          (rationalOnlineLinear eta.value kappa.value
            (childGain (bandChildEnvelope b band (fun i q => (initial i q).value))
              (fun s i => (table s i).value))
            (childDecrement (bandChildEnvelope b band (fun i q => (initial i q).value))
              (fun s i => (table s i).value)) t) G K integer) := by
  simp only [sampledOnlineActionWithWork, BinaryBellmanAction.decode,
    bandActionWithWork_value _ _ _ _ _ _ hne _ _ _ hb, triangularChoiceWithWork_value,
    finiteOptimizerActionDraw, sharedBandRationalAction]
  rw [← representation_value zero, zero_representation, UnreducedRational.value_zero]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryCoordinateAction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The prepared online action explicitly constructs its coordinate array
and compares stored endpoints when constructing each vertex. -/

namespace EditApproximation
namespace BinaryFraction



theorem countedBandCoordinateWithWork_eq {M n : ℕ} (mass : Vector BinaryFraction M)
    (total : BinaryFraction) (action : Fin M → TargetInterval n)
    (coordinate : Fin M × TargetInterval n) :
    (countedBandCoordinateWithWork mass total action coordinate).1 =
      (bandCoordinateWithWork mass total action coordinate).1 ∧
    (countedBandCoordinateWithWork mass total action coordinate).2 =
      (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).2 +
      (bandCoordinateWithWork mass total action coordinate).2 + 1 := by
  have ht : (coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).1 = true ↔
      coordinate.2 = action coordinate.1 := by
    rw [coordinateEqualWithWork_value]
    exact ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩
  unfold countedBandCoordinateWithWork bandCoordinateWithWork
  dsimp only
  by_cases h : coordinate.2 = action coordinate.1
  · simp only [ite_eq_left h, ite_eq_left (ht.mpr h), and_self]
  · simp only [ite_eq_right h, ite_eq_right (fun hp => h (ht.mp hp)), and_self]



@[simp] theorem countedBandVerticesWithWork_value {M n d : ℕ}
    (coordinates : Vector (Fin M × TargetInterval n) d)
    (mass : Vector BinaryFraction M) (band : List (Fin M → TargetInterval n)) :
    (countedBandVerticesWithWork coordinates mass band).1 =
      (labeledBandVerticesWithWork coordinates mass band).1 := by
  simp only [countedBandVerticesWithWork, labeledBandVerticesWithWork, List.map_map,
    Function.comp_def]
  apply List.map_congr_left
  intro action _
  apply congrArg (Prod.mk action)
  apply Vector.ext
  intro i hi
  change ((vectorMapWithWork d _).1.get ⟨i, hi⟩) = ((vectorMapWithWork d _).1.get ⟨i, hi⟩)
  rw [vectorMapWithWork_value, vectorMapWithWork_value]
  exact (countedBandCoordinateWithWork_eq _ _ _ _).1

@[simp] theorem countedPreparedActionWithWork_value {M n : ℕ}
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × TargetInterval n → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedPreparedActionWithWork mass table eta kappa band G j t).1 =
      (preparedBandActionWithWork mass table eta kappa band G j t).1 := by
  simp only [countedPreparedActionWithWork, coordinateVectorWithWork_value,
    countedBandVerticesWithWork_value, preparedBandActionWithWork]

@[simp] theorem countedBandActionWithWork_value {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (G j t : ℕ) :
    (countedBandActionWithWork b initial table eta kappa band G j t).1 =
      (bandActionWithWork b initial table eta kappa band G j t).1 := by
  simp only [countedBandActionWithWork, countedPreparedActionWithWork_value, bandActionWithWork]

@[simp] theorem countedSampledOnlineWithWork_value {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    (countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).1 =
      (sampledOnlineActionWithWork center b initial table eta kappa band hne G K t integer).1 := by
  simp only [countedSampledOnlineWithWork, countedBandActionWithWork_value, sampledOnlineActionWithWork]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Callback work is retained when a finite loop is supplied with a
costed reader. These lemmas compare the literal loop counters, so a
lookup cannot disappear when its returned word is passed to arithmetic. -/

namespace EditApproximation

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem arithmeticFlatMapWithWork_factor {α β : Type*} (read plain : α → List β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hvalue : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hcost : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticFlatMapWithWork read xs).1 = (arithmeticFlatMapWithWork plain xs).1 ∧
      (arithmeticFlatMapWithWork read xs).2 ≤ (arithmeticFlatMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticFlatMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hv := hvalue x List.mem_cons_self
    have hc := hcost x List.mem_cons_self
    have ht := ih (fun y hy => hvalue y (List.mem_cons_of_mem _ hy))
      (fun y hy => hcost y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticFlatMapWithWork, hv, ht.1]
    · simp only [arithmeticFlatMapWithWork, hv]
      have hl : (plain x).1.length ≤ (plain x).1.length * K := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (plain x).1.length hK
      nlinarith only [hc, ht.2, hl, hK]

theorem filterWithWork_length_le_cost {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    xs.length ≤ (filterWithWork test xs).2 := by
  induction xs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons x xs ih => simp only [List.length_cons, filterWithWork]; omega

theorem filterWithWork_add_read {α : Type*} (test : α → Bool × ℕ)
    (readCost : α → ℕ) (xs : List α) (R : ℕ) (hR : ∀ x ∈ xs, readCost x ≤ R) :
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).1 =
      (filterWithWork test xs).1 ∧
    (filterWithWork (fun x => ((test x).1, (test x).2 + readCost x)) xs).2 ≤
      (filterWithWork test xs).2 * (R + 1) := by
  have h := filterWithWork_extra (fun x => ((test x).1, (test x).2 + readCost x))
    test readCost xs (fun _ _ => rfl) (fun _ _ => le_rfl)
  have hs := sum_map_le_length_mul xs readCost R hR
  have hl := filterWithWork_length_le_cost test xs
  refine ⟨h.1, ?_⟩
  nlinarith only [h.2, hs, hl]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReads
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online objective construction charges every historical table read,
including repeated uses in gain and decrement terms. -/

namespace EditApproximation
namespace BinaryFraction





theorem optimisticTermReadWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (R : ℕ) (hs : (read s i).2 ≤ R) (hs' : (read (s + 1) i).2 ≤ R) :
    (optimisticTermReadWithWork mass read coefficient s i).2 ≤
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).2 + 3 * R := by
  simp only [optimisticTermReadWithWork, optimisticTermWithWork, gainReadWithWork,
    decrementReadWithWork, gainWithWork, decrementWithWork]
  omega



theorem onlineLinearReadWithWork_eq_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).1 =
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).1 ∧
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 + (3 * t + 1) * R := by
  have ht := vectorMapWithWork_extra t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermWithWork mass (fun t j => (read t j).1) (coefficientWithWork kappa).1 s.val i)
    (3 * R) (fun _ => rfl) (fun s => optimisticTermReadWithWork_cost mass read _ s.val i R
      (hr _ (by omega)) (hr _ (by omega)))
  have hcur := hr t (by omega)
  unfold onlineLinearReadWithWork onlineLinearWithWork
  dsimp only
  rw [ht.1]
  refine ⟨rfl, ?_⟩
  simp only [gainReadWithWork, gainWithWork]
  nlinarith only [ht.2, hcur]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandActionReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual labelled online action, with charged initial and history reads. -/

namespace EditApproximation
namespace BinaryFraction




theorem countedPreparedActionReadWithWork_eq_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).1 =
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).2)
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value]
  rw [hl.1]
  exact ⟨rfl, by omega⟩



theorem countedBandActionReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).1 =
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hm := envelopeVectorReadWithWork_eq_cost b band initial C hi
  have hs := countedPreparedActionReadWithWork_eq_cost
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read
    eta kappa band G j t R hr
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hm.1]
  exact ⟨hs.1, by omega⟩



theorem countedSampledOnlineReadWithWork_eq_cost {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R C : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).1 =
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).1 ∧
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hs := countedBandActionReadWithWork_eq_cost b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R C hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  rw [hs.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBellmanReads
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Bellman action evaluation with literal finite-table reader calls.
Child words are gathered once, then Boolean arithmetic
operates on that stored list. Reader scans are part of the returned cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem bellmanActionReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) :
    (bellmanActionReadWithWork distance L read query action).1 =
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).1 := by
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]

theorem bellmanActionReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) (R : ℕ)
    (hread : ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanActionReadWithWork distance L read query action).2 ≤
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).2 + M * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun i => read (action.childState i))
    (List.finRange M) R (fun i _ => hread i)
  simp only [List.length_finRange] at h
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]
  omega



theorem bellmanReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (bellmanReadWithWork distance L fallback read query actions).1 =
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).1 := by
  simp only [bellmanReadWithWork, bellmanWithWork, arithmeticMapWithWork_value,
    bellmanActionReadWithWork_eq]

theorem bellmanReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (hread : ∀ action ∈ actions, ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanReadWithWork distance L fallback read query actions).2 ≤
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).2 +
        actions.length * (M * (R + 3)) := by
  have h := arithmeticMapWithWork_extra
    (bellmanActionReadWithWork distance L read query)
    (bellmanActionWithWork distance L (fun s => (read s).1) query)
    (fun _ => M * (R + 3)) actions
    (fun action _ => bellmanActionReadWithWork_eq distance L read query action)
    (fun action ha => bellmanActionReadWithWork_cost distance L read query action R (hread action ha))
  have hs : (actions.map (fun _ => M * (R + 3))).sum = actions.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold bellmanReadWithWork bellmanWithWork
  dsimp only
  rw [h.1]
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryContinuationReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Both Bellman minima and the online score list execute their table
lookups before evaluating the final stored-fraction decrement. -/

namespace EditApproximation
namespace BinaryFraction



theorem localContinuationReadWithWork_eq_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction × ℕ) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (localContinuationReadWithWork distance L delta fallback old current query wide groups online).1 =
      (localContinuationWithWork distance L delta fallback (fun s => (old s).1)
        (fun s => (current s).1) query wide groups online).1 ∧
    (localContinuationReadWithWork distance L delta fallback old current query wide groups online).2 ≤
      (localContinuationWithWork distance L delta fallback (fun s => (old s).1)
        (fun s => (current s).1) query wide groups online).2 +
        (wide.length + groups.length + online.length) * (M * (R + 3)) := by
  have hwv := bellmanReadWithWork_eq distance L fallback old query wide
  have hwc := bellmanReadWithWork_cost distance L fallback old query wide R (fun _ _ _ => ho _)
  have hgv := bellmanReadWithWork_eq distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups
  have hgc := bellmanReadWithWork_cost distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups R
    (fun _ _ _ => hn _)
  have hs := arithmeticMapWithWork_extra
    (bellmanActionReadWithWork distance L current query)
    (bellmanActionWithWork distance L (fun s => (current s).1) query)
    (fun _ => M * (R + 3)) online
    (fun a _ => bellmanActionReadWithWork_eq distance L current query a)
    (fun a _ => bellmanActionReadWithWork_cost distance L current query a R (fun _ => hn _))
  have hsum : (online.map (fun _ => M * (R + 3))).sum = online.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hsum] at hs
  unfold localContinuationReadWithWork localContinuationWithWork
  dsimp only
  rw [hwv, hgv, hs.1]
  exact ⟨rfl, by nlinarith only [hwc, hgc, hs.2]⟩



theorem physicalContinuationReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (R : ℕ) (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).1 =
      (physicalContinuationWithWork parent representatives P F delta fallback
        (fun s => (old s).1) (fun s => (current s).1) groups online query).1 ∧
    (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).2 ≤
      (physicalContinuationWithWork parent representatives P F delta fallback
        (fun s => (old s).1) (fun s => (current s).1) groups online query).2 +
      ((wideActionsFromRepresentativesWithWork M parent representatives P).1.length +
        groups.length + online.length) * (M * (R + 3)) := by
  have h := localContinuationReadWithWork_eq_cost endpointDistanceWithWork
    (canonicalMulWithWork (nat 128) (nat F)).1 delta fallback old current query
    (wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online R ho hn
  unfold physicalContinuationReadWithWork physicalContinuationWithWork
  dsimp only
  exact ⟨h.1, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryGatheredValues
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
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

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnline
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The keyed online branch executes the actual endpoint grids before
its guard and optimizer. The original finite source range is preserved. -/

namespace EditApproximation
namespace BinaryFraction

private theorem preparedOnlineBandReference_congr {M n : ℕ} (center : TargetInterval n)
    (b G G' : ℕ) (hG : 0 < G) (hG' : 0 < G') (heq : G = G')
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band band' : List (Fin M → TargetInterval n)) (hband : band = band')
    (hne : band ≠ []) (hne' : band' ≠ []) (t integer : ℕ) :
    preparedOnlineBandReference center b G hG initial table eta kappa band hne t integer =
      preparedOnlineBandReference center b G' hG' initial table eta kappa band' hne' t integer := by
  cases heq
  cases hband
  rfl

theorem preparedOnlineWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    ((preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa child initial table
      t center integer).1.map BinaryBellmanAction.decode) =
      keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (fun i s q => (table s (i, q)).value) t center integer := by
  have hband := preparedRepresentativeWithWork_value source target parent center b P hP tau (inversePowerTwo exponent) child
  simp only [inversePowerTwo_value] at hband
  have hG : (onlineIndexSetupWithWork H (preparedRepresentativeWithWork parent center
      (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) child).1).1 =
      keyedOnlineBandG source target parent P exponent H b tau.value (fun i q => (child i q).value) center := by
    rw [onlineIndexSetupWithWork_value, listedBandCoordinates_length, hband]
    rfl
  have hGpos : 0 < (onlineIndexSetupWithWork H (preparedRepresentativeWithWork parent center
      (parent.hi - parent.lo) b P tau (inversePowerTwo exponent) child).1).1 := by
    rw [onlineIndexSetupWithWork_value]
    omega
  have hGpos' : 0 < keyedOnlineBandG source target parent P exponent H b tau.value
      (fun i q => (child i q).value) center := by
    rw [← hG]
    exact hGpos
  have htest := preparedUnskippedCandidateWithWork_value source target parent b P exponent hb hP tau (nat F) child initial center
  unfold preparedOnlineWithWork
  dsimp only
  split_ifs with hempty hactive
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) = [] := hband.symm.trans hempty
    simp only [Option.map_none, keyedOnlineCandidate, dite_eq_left he]
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) ≠ [] :=
      fun hz => hempty (hband.trans hz)
    rw [htest] at hactive
    rw [congrArg (fun f : ℚ => (testUnskippedBand source target parent b P exponent tau.value f
      (fun i q => (child i q).value) (fun i q => (initial i q).value) center).isSome) (nat_value F)] at hactive
    unfold keyedOnlineCandidate
    simp only [dite_eq_right he]
    cases ht : testUnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center with
    | none =>
      have hf : (none : Option (UnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value))).isSome = true := by
        simpa only [← ht] using hactive
      cases hf
    | some member =>
      simp only [Option.map_some, countedSampledOnlineWithWork_value,
        sampledOnlineActionWithWork_value _ _ _ _ _ _ _ _ _ _ _ _ hb,
        reduceOnlineIntegerWithWork_value]
      apply congrArg some
      exact preparedOnlineBandReference_congr center b _ _ hGpos hGpos' hG initial table eta kappa _ _ hband hempty he t integer
  · have he : representativeBandActions source target parent center b P tau.value
        ((2 : ℚ) ^ (-(exponent : ℤ))) (fun i q => (child i q).value) ≠ [] :=
      fun hz => hempty (hband.trans hz)
    rw [htest] at hactive
    rw [congrArg (fun f : ℚ => (testUnskippedBand source target parent b P exponent tau.value f
      (fun i q => (child i q).value) (fun i q => (initial i q).value) center).isSome) (nat_value F)] at hactive
    unfold keyedOnlineCandidate
    simp only [dite_eq_right he, Option.map_none]
    cases ht : testUnskippedBand source target parent b P exponent tau.value (F : ℚ)
        (fun i q => (child i q).value) (fun i q => (initial i q).value) center with
    | none => rfl
    | some member =>
      apply False.elim
      apply hactive
      rw [ht]
      rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedLocalOnline
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One rounded center is queried at each retained dyadic scale. Both
eligibility and the complete online optimizer are charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedLocalOnlineScaleWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    ((preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa parentInitial
      child initial table t integer query).1.map BinaryBellmanAction.decode) =
      (let b := 2 ^ e
       let r := roundInterval (seedGridSpacing b P) query
       if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧
           (parentInitial r).value ≤ 8 * F * b then
         keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
           (fun i q => (child i q).value) (fun i q => (initial i q).value)
           (fun i s q => (table s (i, q)).value) t r (integer b r)
       else none) := by
  unfold preparedLocalOnlineScaleWithWork
  simp only [roundStateWithWork_value, seedGridSpacingWithWork_value _ _ hP]
  by_cases h : (centerEligibilityWithWork (2 ^ e) F a
      (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query))).1 = true
  · have hp := (centerEligibilityWithWork_value _ _ _ _).mp h
    rw [ite_eq_left h, ite_eq_left hp]
    exact preparedOnlineWithWork_value source target parent P F exponent H (2 ^ e) (Nat.two_pow_pos e) hP
        tau eta kappa child initial table t (roundInterval (seedGridSpacing (2 ^ e) P) query)
        (integer (2 ^ e) (roundInterval (seedGridSpacing (2 ^ e) P) query))
  · have hp : ¬ (((2 ^ e : ℕ) : ℚ) / (4 * a.value) ≤
        (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query)).value ∧
        (parentInitial (roundInterval (seedGridSpacing (2 ^ e) P) query)).value ≤ 8 * F * (2 ^ e : ℕ)) :=
      fun hx => h ((centerEligibilityWithWork_value _ _ _ _).mpr hx)
    rw [ite_eq_right h, ite_eq_right hp]
    rfl

theorem preparedLocalOnlineActionsWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length) :
    ((preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa parentInitial
      child initial table t integer query).1.map BinaryBellmanAction.decode) =
      localOnlineCandidates source target parent N P F exponent H tau.value a.value eta.value kappa.value
        (fun r => (parentInitial r).value) (fun i r => (child i r).value)
        (fun i r => (initial i r).value) (fun i s r => (table s (i, r)).value) t integer query := by
  unfold preparedLocalOnlineActionsWithWork
  simp only [filterMapWithWork_value, List.map_filterMap]
  trans (queryExponentsWithWork N F a (parentInitial query)).1.filterMap (fun e =>
    let b := 2 ^ e
    let r := roundInterval (seedGridSpacing b P) query
    if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧ (parentInitial r).value ≤ 8 * F * b then
      keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
        (fun i q => (child i q).value) (fun i q => (initial i q).value)
        (fun i s q => (table s (i, q)).value) t r (integer b r)
    else none)
  · apply List.filterMap_congr
    intro e _
    exact preparedLocalOnlineScaleWithWork_value source target parent P F exponent H e hP tau a eta kappa
      parentInitial child initial table t integer query
  · trans ((queryExponentsWithWork N F a (parentInitial query)).1.map (fun e => 2 ^ e)).filterMap
      (fun b =>
        let r := roundInterval (seedGridSpacing b P) query
        if (b : ℚ) / (4 * a.value) ≤ (parentInitial r).value ∧ (parentInitial r).value ≤ 8 * F * b then
          keyedOnlineCandidate source target parent P F exponent H b tau.value eta.value kappa.value
            (fun i q => (child i q).value) (fun i q => (initial i q).value)
            (fun i s q => (table s (i, q)).value) t r (integer b r)
        else none)
    · rw [List.filterMap_map]
      rfl
    · rw [queryExponentsWithWork_value]
      rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedUnskippedReadWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).1 =
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).1 := by
  have hband := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband]
  split_ifs with hempty hguard
  · rfl
  · rfl
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hplain (hg.symm.trans hguard))
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hguard (hg.trans hplain))
  · rfl


theorem preparedUnskippedReadWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 +
      representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband.1]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi
    simp only [hg.1]
    split_ifs <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

private theorem preparedOnlineReadCore_compare {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (B C E : ℕ) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 + B)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 + C)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).1 = (plainSample plain.1 hne G draw).1 ∧
      (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 + E) :
    (preparedOnlineReadCore H integer band guard sample).1 =
      (preparedOnlineReadCore H integer plain plainGuard plainSample).1 ∧
    (preparedOnlineReadCore H integer band guard sample).2 ≤
      (preparedOnlineReadCore H integer plain plainGuard plainSample).2 + (B + C + E) := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold preparedOnlineReadCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · exact ⟨rfl, by omega⟩
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    exact ⟨congrArg some hsample.1, by omega⟩
  · exact ⟨rfl, by omega⟩

theorem preparedOnlineReadWithWork_eq_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).1 =
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).1 ∧
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 +
      preparedOnlineReadExtra M parent center b P exponent R t tau (fun i q => (child i q).1) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) child R hc
  have hguard := preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have hguardCost := preparedUnskippedReadWithWork_cost source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have h := preparedOnlineReadCore_compare H integer
    (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) child)
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) (fun i q => (child i q).1))
    ((preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center).1.isSome,
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).2)
    ((preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1) center).1.isSome,
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1) center).2)
    (fun xs hxs G draw => countedSampledOnlineReadWithWork center b initial table eta kappa
      xs hxs G (G ^ 80) t draw)
    (fun xs hxs G draw => countedSampledOnlineWithWork center b
      (fun i q => (initial i q).1) (fun s i => (table s i).1) eta kappa xs hxs G (G ^ 80) t draw)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      2 * (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3))))
    (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3)) +
      (listedBandCoordinates (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1).length * ((3 * t + 1) * R))
    hband.1 hband.2 (congrArg Option.isSome hguard) (by omega)
    (fun hne G draw => by
      simpa only [Nat.add_assoc] using countedSampledOnlineReadWithWork_eq_cost center b initial table eta kappa
        _ hne G (G ^ 80) t R R draw hi (fun s hs i => ht s hs _))
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> first
  | rfl
  | (dsimp only [preparedOnlineReadExtra, preparedOnlineWithWork, preparedOnlineReadCore]; ring)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineSource
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online candidate selection charges the finite source-buffer decoder
at the point where its integer is consumed. Ineligible centers do not
read a random coordinate. -/

namespace EditApproximation.BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineScaleSourceWithWork_value (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 := by
  unfold preparedLocalOnlineScaleSourceWithWork preparedLocalOnlineScaleReadWithWork
  dsimp only
  split_ifs <;> rfl

theorem preparedLocalOnlineActionsSourceWithWork_value (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 := by
  simp only [preparedLocalOnlineActionsSourceWithWork, preparedLocalOnlineActionsReadWithWork,
    filterMapWithWork_value, preparedLocalOnlineScaleSourceWithWork_value]

end Local
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalReadValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Value preservation of local data readers does not require a chosen
work cap for arbitrary answer tables. Finite bounds used below exist only
inside these proofs and are never constructed by the algorithm. -/

namespace EditApproximation.BinaryFraction

private theorem finite_work_bound {ι : Type*} [Fintype ι] (work : ι → ℕ) :
    ∃ R, ∀ i, work i ≤ R := by
  classical
  exact ⟨∑ i, work i, fun i => Finset.single_le_sum (f := work) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

private theorem preparedOnlineReadWithWork_cap_irrel (b : ℕ) (hb : 0 < b)
    (R' : ℕ) (hc' : ∀ i q, (child i q).2 ≤ R') (hi' : ∀ i q, (initial i q).2 ≤ R')
    (center : TargetInterval target.length) (sample : ℕ) :
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample =
    preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R' hc' hi' t center sample := by
  rfl

theorem preparedOnlineReadWithWork_value_only (b : ℕ) (hb : 0 < b)
    (center : TargetInterval target.length) (sample : ℕ) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center sample).1 =
    (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
      (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t center sample).1 := by
  classical
  obtain ⟨S, hs⟩ := finite_work_bound (fun si : Fin (t + 2) × (Fin M × TargetInterval target.length) =>
    (table si.1.val si.2).2)
  let R' := max R S
  have hc' : ∀ i q, (child i q).2 ≤ R' := fun i q => (hc i q).trans (Nat.le_max_left _ _)
  have hi' : ∀ i q, (initial i q).2 ≤ R' := fun i q => (hi i q).trans (Nat.le_max_left _ _)
  rw [preparedOnlineReadWithWork_cap_irrel source target parent P F exponent H hP
    tau eta kappa child initial table R hc hi t b hb R' hc' hi' center sample]
  exact (preparedOnlineReadWithWork_eq_cost source target parent P F exponent H b hb hP
    tau eta kappa child initial table R' hc' hi' t center sample (fun s hst iq =>
      (hs (⟨s, by omega⟩, iq)).trans (Nat.le_max_right R S))).1

theorem preparedLocalOnlineScaleReadWithWork_value_only (e : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · exact preparedOnlineReadWithWork_value_only source target parent P F exponent H hP
      tau eta kappa child initial table R hc hi t (2 ^ e) (Nat.two_pow_pos e) _ _
  · rfl

theorem preparedLocalOnlineActionsReadWithWork_value_only (N : ℕ) (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  simp only [preparedLocalOnlineActionsReadWithWork, preparedLocalOnlineActionsWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro e _
  exact preparedLocalOnlineScaleReadWithWork_value_only source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial table R hc hi t integer e query
end Online
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryRepresentativeReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Query-local representative construction reads its finite initial
table explicitly. Each center lookup is charged before testing it. -/

namespace EditApproximation
namespace BinaryFraction



theorem representativeScaleReadWithWork_eq_cost {n : ℕ} (P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (radius : List Bool)
    (query : TargetInterval n) (e R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (representativeScaleReadWithWork P F a read radius query e).1 =
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).1 ∧
    (representativeScaleReadWithWork P F a read radius query e).2 ≤
      (representativeScalePlainWithWork P F a (fun r => (read r).1) radius query e).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) (bitWordValue radius) query.lo query.hi
  have h := filterWithWork_add_read (fun r => centerEligibilityWithWork (2 ^ e) F a (read r).1)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simp only [representativeScaleReadWithWork, representativeScalePlainWithWork, spacing, points, h.1]
  · unfold representativeScaleReadWithWork representativeScalePlainWithWork
    change spacing.2 + points.2 + _ + _ + e + 5 ≤ (spacing.2 + points.2 + _ + _ + e + 5) * _
    rw [h.1]
    nlinarith only [h.2]



theorem localRepresentativeReadWithWork_eq_cost {n : ℕ} (N P F : ℕ) (a : BinaryFraction)
    (read : TargetInterval n → BinaryFraction × ℕ) (query : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (read r).2 ≤ R) :
    (localRepresentativeReadWithWork N P F a read query).1 =
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).1 ∧
    (localRepresentativeReadWithWork N P F a read query).2 ≤
      (localRepresentativesWithWork N P F a (fun r => (read r).1) query).2 * (R + 2) := by
  let scales := queryExponentsWithWork N F a (read query).1
  let radius := naturalCeilingWithWork (read query).1
  let plain := representativeScalePlainWithWork P F a (fun r => (read r).1) radius.1 query
  let withRead := representativeScaleReadWithWork P F a read radius.1 query
  have h := arithmeticFlatMapWithWork_factor withRead plain scales.1 (R + 1) (by omega)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).1)
    (fun e _ => (representativeScaleReadWithWork_eq_cost P F a read radius.1 query e R hR).2)
  have hquery := hR query
  constructor
  · exact h.1
  · change (read query).2 + scales.2 + radius.2 +
      (arithmeticFlatMapWithWork withRead scales.1).2 + 3 ≤
      (scales.2 + radius.2 + (arithmeticFlatMapWithWork plain scales.1).2 + 3) * (R + 2)
    nlinarith only [h.2, hquery]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalSourceValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local source-port values for arbitrary gathered answer lists.
No cost bound on unqueried coordinates enters these identities. -/

namespace EditApproximation

namespace BinaryFraction

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineActionsSourceWithWork_semantic_value (N : ℕ)
    (query : TargetInterval target.length) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t (fun b q => (integer b q).1) query).1 :=
  (preparedLocalOnlineActionsSourceWithWork_value source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t integer N query).trans
  (preparedLocalOnlineActionsReadWithWork_value_only source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query)
end Online

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



theorem Refines.bind {ι α β : Type*} {relation : α → ℚ → Prop}
    {nextRelation : β → ℚ → Prop} {program : BitQuery ι α} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (next : α → BitQuery ι β) (expectedNext : ℚ → FiniteQuery ι)
    (hn : ∀ a v, relation a v → Refines nextRelation (next a) (expectedNext v)) :
    Refines nextRelation (program.bind next) (FiniteQuery.bind expected expectedNext) := by
  induction h with
  | done h => exact hn _ _ h
  | read key continuation expected h ih => exact .read key _ _ ih
  | charge steps h ih => exact .charge steps ih



theorem Refines.collect {ι κ β : Type*} {relation : β → ℚ → Prop}
    (reader : κ → BitQuery ι BinaryFraction) (expectedReader : κ → FiniteQuery ι)
    (hr : ∀ key, Refines (fun word value => word.value = value) (reader key) (expectedReader key))
    (inputs : List κ) (next : List BinaryFraction → BitQuery ι β)
    (expectedNext : List ℚ → FiniteQuery ι)
    (hn : ∀ words, Refines relation (next words) (expectedNext (words.map BinaryFraction.value))) :
    Refines relation (BitQuery.collect reader inputs next)
      (FiniteQuery.collect expectedReader inputs expectedNext) := by
  induction inputs generalizing next expectedNext with
  | nil => exact hn []
  | cons key inputs ih =>
    apply (hr key).bind
    intro word value hv
    subst value
    apply Refines.charge
    apply ih
    intro words
    exact hn (word :: words)

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSamples
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Group sample coordinates are enumerated from the computed dyadic
scale array and binary sample counts. Equalities used in index casts are
proofs only; the loop bounds are the values just computed. -/

namespace EditApproximation



namespace BinaryFraction



theorem queryGroupKeySamplesWithWork_value (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF cell).1 =
      groupScalarKeys M F Q [(2 ^ eb, cell)] := by
  simp only [queryGroupKeySamplesWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, queryFinRange_value, groupScalarKeys,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySourceBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedBandActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedBandVerticesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedPreparedActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedSampledOnlineWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
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



theorem queryGroupDrawReadWithWork_value {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) :
    (queryGroupDrawReadWithWork keys values b cell scale sample).1 =
      groupDrawFromValues keys (values.map value) b cell scale sample := by
  apply Fin.ext
  simp only [queryGroupDrawReadWithWork,
    (binaryNaturalDivModWithWork_spec _ M (NeZero.pos M)).2,
    naturalFloorWithWork_value, gatheredWordLookupWithWork_value _ queryGroupKeyEqualWithWork_value,
    groupDrawFromValues, Fin.val_ofNat]



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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedBandActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedBandVerticesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedPreparedActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.countedSampledOnlineWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGroupSources
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Complete scalar-source key generation uses the original dyadic
query window, cell order, scale order, and sample order. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryGroupSourceKeysWithWork_value {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : BinaryFraction)
    (q : TargetInterval n) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a value q).1 =
      groupScalarKeys M F Q (localGroupQueryKeys N F exponent a.value (fun _ => value.value) q) := by
  simp only [queryGroupSourceKeysWithWork, arithmeticFlatMapWithWork_value,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value, queryGroupKeySamplesWithWork_value]
  conv_rhs => unfold localGroupQueryKeys
  rw [← queryExponentsWithWork_value N F a value]
  simp only [groupScalarKeys, List.flatMap_map, List.flatMap_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction



theorem queryGroupSourceGather_refines {ι β : Type*} {n : ℕ} {relation : β → ℚ → Prop}
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (expectedReader : GroupScalarKey M F Q → FiniteQuery ι)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (GroupScalarKey M F Q) → List ℚ → FiniteQuery ι)
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (reader key) (expectedReader key))
    (hn : ∀ words,
      let keys := groupScalarKeys M F Q
        (localGroupQueryKeys N F exponent a.value (fun r => (initial r).1.value) q)
      BitQuery.Refines relation (next keys words) (expectedNext keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next)
      (let keys := groupScalarKeys M F Q
        (localGroupQueryKeys N F exponent a.value (fun r => (initial r).1.value) q)
       FiniteQuery.collect expectedReader keys (expectedNext keys)) := by
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect reader _ _) _
  rw [BinaryFraction.queryGroupSourceKeysWithWork_value]
  exact BitQuery.Refines.collect reader expectedReader hr _ _ _ hn

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSelectors
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete selectors of the adaptive local program. Source and table
lookups are evaluated by their counted finite-buffer routines. Their value
identities hold even for arbitrary gathered answer lists. -/

namespace EditApproximation
namespace BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

theorem queryOnlineSelectWithWork_value (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    ((queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q).1.map BinaryBellmanAction.decode) =
      localOnlineCandidates source target parent N P F exponent H tau.value a.value eta.value kappa.value
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (fun i s r => finiteAnswerTable keys (words.map value) (i, s, r))
        (t - 1) (fun b r => (integer b r).1) q := by
  unfold queryOnlineSelectWithWork
  rw [preparedLocalOnlineActionsSourceWithWork_semantic_value]
  rw [preparedLocalOnlineActionsWithWork_value]
  simp only [queryHistoryReadWithWork_value]

end Selectors
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementFinish
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The final local continuation consumes the two gathered data buffers.
It recomputes the local representative list with counted initial reads and
runs the Boolean Bellman/online minima on the already selected actions. -/

namespace EditApproximation
namespace BinaryFraction

section Finish
variable {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ)
  (a delta : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
  (t : ℕ) (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
  (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
  (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
  (query : TargetInterval ny)



theorem queryRefinementFinishWithWork_value (hP : 0 < P)
    (R : ℕ) (hp : ∀ r, (initial r).2 ≤ R)
    (he : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ R)
    (hc : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).2 ≤ R) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords
      groups online currentKeys currentWords query).1.value =
      rationalWideStep parent
        (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) query)
        P (fun _ => (initial query).1.value) (128 * F) delta.value
        (fun input => finiteAnswerTable earlierKeys (earlierWords.map value) (input.1, t - 1, input.2))
        (finiteAnswerTable currentKeys (currentWords.map value))
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  have hr := (localRepresentativeReadWithWork_eq_cost N P F a initial query R hp).1
  have hv := (physicalContinuationReadWithWork_eq_cost parent
    (localRepresentativeReadWithWork N P F a initial query).1 P F delta (initial query).1
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork currentKeys currentWords input.1 input.2)
    groups online query R he (fun input => hc input.1 input.2)).1
  simp only [queryRefinementFinishWithWork]
  rw [hv, hr, physicalContinuationWithWork_value parent
    (localRepresentativesWithWork N P F a (fun r => (initial r).1) query).1 P F delta
    (initial query).1 (fun input => (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork currentKeys currentWords input.1 input.2).1)
    groups online query hP]
  simp only [localRepresentativesWithWork_value N P F hP a (fun r => (initial r).1) query,
    queryHistoryReadWithWork_value, queryChildReadWithWork_value]


theorem queryRefinementFinishWithWork_value_only (hP : 0 < P) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords
      groups online currentKeys currentWords query).1.value =
      rationalWideStep parent
        (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) query)
        P (fun _ => (initial query).1.value) (128 * F) delta.value
        (fun input => finiteAnswerTable earlierKeys (earlierWords.map value) (input.1, t - 1, input.2))
        (finiteAnswerTable currentKeys (currentWords.map value))
        (groups.map BinaryBellmanAction.decode) (online.map BinaryBellmanAction.decode) query := by
  classical
  let p := ∑ r, (initial r).2
  let e := ∑ input : Fin M × TargetInterval ny,
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2
  let c := ∑ input : Fin M × TargetInterval ny,
    (queryChildReadWithWork currentKeys currentWords input.1 input.2).2
  apply queryRefinementFinishWithWork_value parent N P F a delta initial t earlierKeys earlierWords
    groups online currentKeys currentWords query hP (p + e + c)
  · intro r
    have h : (initial r).2 ≤ p := Finset.single_le_sum (f := fun r => (initial r).2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  · intro input
    have h : (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ e :=
      Finset.single_le_sum (f := fun input =>
        (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ input)
    omega
  · intro i r
    have h : (queryChildReadWithWork currentKeys currentWords i r).2 ≤ c :=
      Finset.single_le_sum (f := fun input : Fin M × TargetInterval ny =>
        (queryChildReadWithWork currentKeys currentWords input.1 input.2).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, r))
    omega

end Finish
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalRefinement
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete charged local refinement request: earlier history, shared
samples, selected current inputs and the final binary continuation. -/

namespace EditApproximation

section Local
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

theorem queryLocalRefinement_refines
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent)
      (localRefinementStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) (fun b cell scale sample => (draw b cell scale sample).1)
        (fun b r => (integer b r).1) q expectedEarlier expectedCurrent) := by
  classical
  let Rp := ∑ r, (parentInitial r).2
  have hp : ∀ r, (parentInitial r).2 ≤ Rp := fun r =>
    Finset.single_le_sum (f := fun r => (parentInitial r).2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  unfold queryLocalRefinement localRefinementStepQuery
  apply queryRefinementGather_refines (expectedEarlier := expectedEarlier)
    (expectedCurrent := expectedCurrent)
    (expectedOnline := fun keys words => localOnlineCandidates source target parent N P F exponent H
      tau.value a.value eta.value kappa.value (fun r => (parentInitial r).1.value)
      (fun i r => (child i r).1.value) (fun i r => (initial i r).1.value)
      (fun i s r => finiteAnswerTable keys words (i, s, r)) (t - 1)
      (fun b r => (integer b r).1) q)
    (expectedSelected := fun keys words => localCellGroupActions source target parent N P F exponent Q
      tau.value a.value (fun r => (parentInitial r).1.value)
      (fun i r => (child i r).1.value) (fun i r => (initial i r).1.value)
      (fun i r => finiteAnswerTable keys words (i, r))
      (fun b cell scale sample => (draw b cell scale sample).1) q)
    (expectedNext := fun earlierKeys earlierWords groups online currentKeys currentWords =>
      .done (rationalRefinementUpdate delta.value
        (rationalMinimum
          (rationalBellman (fun r => (parentInitial r).1.value)
            (fun q r => targetEndpointDistance q r) (128 * F)
            (rationalActualWideActions parent
              (localRefinementRepresentatives N P F a.value (fun r => (parentInitial r).1.value) q) P)
            (fun input => finiteAnswerTable earlierKeys earlierWords (input.1, t - 1, input.2)) q)
          (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (finiteAnswerTable currentKeys currentWords) q)))
        (rationalOnlineMinimum (online.map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (finiteAnswerTable currentKeys currentWords) q)))))
    (R := Rp) (hR := hp) (he := he) (hc := hr)
  · intro keys words
    exact BinaryFraction.queryOnlineSelectWithWork_value source target parent N P F exponent H hP
      tau a eta kappa parentInitial child initial R hc hi t integer keys words q
  · intro keys words
    exact BinaryFraction.queryGroupSelectWithWork_value source target parent N P F exponent Q eM eF
      hP hM hF tau a parentInitial child initial R hc hi draw keys words q
  · intro earlierKeys earlierWords groups online currentKeys currentWords
    apply BitQuery.Refines.charge
    apply BitQuery.Refines.done
    simpa only [rationalWideStep, rationalWideStepCone, rationalBellman] using
      BinaryFraction.queryRefinementFinishWithWork_value_only parent N P F a delta parentInitial
        t earlierKeys earlierWords groups online currentKeys currentWords q hP

end Local
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOnlineSources
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An online random-source range is computed from the gathered mass
words before the source is requested. Band construction, dimension,
eighty-fold power, and triangular mass are all charged. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryOnlineRangeWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H : ℕ) (hP : 0 < P)
    (tau : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (key : ℕ × TargetInterval target.length) (R : ℕ) (hR : ∀ i r, (child i r).2 ≤ R) :
    (queryOnlineRangeWithWork parent P exponent H tau child key).1 =
      keyedOnlineSourceRange source target parent P exponent H tau.value
        (fun i r => (child i r).1.value) key := by
  have hb := (preparedRepresentativeReadWithWork_eq_cost parent key.2
    (parent.hi - parent.lo) key.1 P tau (inversePowerTwo exponent) child R hR).1
  simp only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value, hb,
    triangularMassWithWork_value, bitPowerWithWork_value, bitWordValue_bits,
    onlineIndexSetupWithWork_value, listedBandCoordinates_length,
    preparedRepresentativeWithWork_value source target parent key.2 key.1 P hP,
    inversePowerTwo_value, keyedOnlineSourceRange, keyedOnlineBandG]

end BinaryFraction



theorem queryOnlineSourceGather_refines {ι β α : Type*} (source target : List α) {M : ℕ}
    {relation : β → ℚ → Prop} (parent : TargetInterval source.length)
    (N P F exponent H : ℕ) (hP : 0 < P) (tau a : BinaryFraction)
    (initial : TargetInterval target.length → BinaryFraction × ℕ)
    (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (q : TargetInterval target.length) (R : ℕ) (hR : ∀ i r, (child i r).2 ≤ R)
    (reader : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
    (expectedReader : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (next : List (ℕ × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (ℕ × TargetInterval target.length) → List ℚ → FiniteQuery ι)
    (hr : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (reader key range) (expectedReader key range))
    (hn : ∀ words,
      let keys := localOnlineSourceKeys N P F a.value (fun r => (initial r).1.value) q
      BitQuery.Refines relation (next keys words) (expectedNext keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next)
      (let keys := localOnlineSourceKeys N P F a.value (fun r => (initial r).1.value) q
       FiniteQuery.collect (fun key => expectedReader key
          (keyedOnlineSourceRange source target parent P exponent H tau.value
            (fun i r => (child i r).1.value) key)) keys (expectedNext keys)) := by
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect _ _ _) _
  rw [BinaryFraction.queryOnlineKeysWithWork_value]
  apply BitQuery.Refines.collect
  · intro key
    change BitQuery.Refines _ (.charge _ _) _
    apply BitQuery.Refines.charge
    rw [BinaryFraction.queryOnlineRangeWithWork_value source target parent P exponent H hP tau child key R hR]
    exact hr key _
  · exact hn

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalSources
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Random words are gathered before the adaptive local selectors run.
The online sampling range is computed from the gathered mass words. -/

namespace EditApproximation

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

theorem queryLocalRandomSources_refines_oai
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial child initial R hc hi q
        readGroup readInteger readEarlier readCurrent)
      (localRandomSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) q
        expectedGroup expectedInteger expectedEarlier expectedCurrent) := by
  unfold queryLocalRandomSources localRandomSourceStepQuery
  apply queryGroupSourceGather_refines M N F Q exponent eM eF hM hF a parentInitial q readGroup
    expectedGroup (expectedNext := fun keys values =>
      localOnlineSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) (groupDrawFromValues keys values)
        q expectedInteger expectedEarlier expectedCurrent) (hr := hg)
  intro groupWords
  let groupKeys := groupScalarKeys M F Q
    (localGroupQueryKeys N F exponent a.value (fun r => (parentInitial r).1.value) q)
  unfold localOnlineSourceStepQuery
  apply queryOnlineSourceGather_refines source target parent N P F exponent H hP tau a
    parentInitial child q R hc readInteger expectedInteger
    (expectedNext := fun keys values =>
      localRefinementStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (groupDrawFromValues groupKeys (groupWords.map BinaryFraction.value))
        (fun b r => ⌊finiteAnswerTable keys values (b, r)⌋₊) q expectedEarlier expectedCurrent)
    (hr := hz)
  intro onlineWords
  let onlineKeys := localOnlineSourceKeys N P F a.value (fun r => (parentInitial r).1.value) q
  have h := queryLocalRefinement_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial child initial R hc hi
    (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
    (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords)
    q readEarlier readCurrent expectedEarlier expectedCurrent he hr
  simpa only [BinaryFraction.queryGroupDrawReadWithWork_value,
    BinaryFraction.queryOnlineIntegerReadWithWork_value] using h

end Sources
end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.queryLocalRandomSources_refines_oai.{u_1, u_2} := @OAI.EditApproximation.queryLocalRandomSources_refines_oai.{u_1, u_2}

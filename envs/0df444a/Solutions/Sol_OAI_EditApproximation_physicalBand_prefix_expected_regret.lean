-- Prove2me | solution 1 for OAI.EditApproximation.physicalBand_prefix_expected_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:29.317765+00:00
-- url     : https://prove2.me/submissions/337221c5-d700-446d-bc22-4dfa8878571b

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_list_band_computed_entropy_regret
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds
import Theorems.Thm_OAI_EditApproximation_rationalPhysicalWarmup_cast
import Theorems.Thm_OAI_EditApproximation_stageWarmup_postfixed

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_Numerics
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.triangularChoiceWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

theorem optimizerMixtureWeight_update_old (K j : ℕ) (hK : 0 < K) :
    (1 - 2 / ((K : ℚ) + 2)) * optimizerMixtureWeight K j =
      optimizerMixtureWeight (K + 1) j := by
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  ring

theorem optimizerMixtureWeight_update_new (K : ℕ) :
    2 / ((K : ℚ) + 2) = optimizerMixtureWeight (K + 1) K := by
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  ring

/-- After the first update, the initial vertex has weight zero. The
remaining iterates are exactly the explicit rational triangular mixture
used by the fair-bit sampler in Section 9. -/
theorem rationalOptimizerIterate_eq_mixture {ι : Type*}
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ) (K : ℕ) (i : ι) :
    rationalOptimizerIterate initial selected (K + 1) i =
      ∑ j ∈ range (K + 1), optimizerMixtureWeight (K + 1) j * selected j i := by
  induction K with
  | zero => norm_num [rationalOptimizerIterate, optimizerMixtureWeight]
  | succ K ih =>
    rw [rationalOptimizerIterate]
    dsimp only
    rw [ih, mul_sum]
    conv_rhs => rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro j hj
      rw [← mul_assoc, optimizerMixtureWeight_update_old (K + 1) j (by omega)]
    · rw [optimizerMixtureWeight_update_new]

/-- Counting the fair uniform integer sampler gives exactly the stored
mixture weights, including repeated selected vertices. -/
theorem optimizerSampler_block_weight (K j : ℕ) (hK : 0 < K) :
    ((j + 1 : ℕ) : ℚ) / optimizerTriangularMass K = optimizerMixtureWeight K j := by
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  have hmass : 2 * (optimizerTriangularMass K : ℚ) = (K : ℚ) * ((K : ℚ) + 1) := by
    exact_mod_cast optimizerTriangularMass_twice K
  have hmasspos : 0 < (optimizerTriangularMass K : ℚ) := by nlinarith
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  nlinarith

theorem finiteRationalOptimizer_eq_iterate {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer coordinates vertices linear G j =
      rationalOptimizerIterate (vertices.headD (fun _ => 0))
        (finiteOptimizerSelection coordinates vertices linear G) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext i
    simp only [finiteRationalOptimizer, rationalOptimizerIterate]
    change (1 - 2 / ((j : ℚ) + 2)) * finiteRationalOptimizer coordinates vertices linear G j i +
        2 / ((j : ℚ) + 2) * finiteOptimizerSelection coordinates vertices linear G j i = _
    rw [ih]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActionVectors
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem actionVector_inner_product {β σ : Type*} [Fintype β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (gain : β × σ → ℝ)
    {action : β → σ} (haction : action ∈ band) :
    (∑ coordinate ∈ bandCoordinates band, gain coordinate * (actionVector mass action coordinate : ℝ)) =
      ∑ child, gain (child, action child) * (mass child / (∑ i, mass i) : ℚ) := by
  have hsubset : (univ.image fun child => (child, action child)) ⊆ bandCoordinates band := by
    intro coordinate hc
    obtain ⟨child, _, rfl⟩ := mem_image.mp hc
    exact action_coordinate_mem band haction child
  have hsum : (∑ coordinate ∈ bandCoordinates band,
      gain coordinate * (actionVector mass action coordinate : ℝ)) =
        ∑ coordinate ∈ univ.image (fun child => (child, action child)),
          gain coordinate * (actionVector mass action coordinate : ℝ) := by
    symm
    apply sum_subset hsubset
    intro coordinate _ hnot
    have hne : coordinate.2 ≠ action coordinate.1 := by
      intro heq
      exact hnot (mem_image.mpr ⟨coordinate.1, mem_univ _, Prod.ext rfl heq.symm⟩)
    simp only [actionVector, ite_eq_right hne, Rat.cast_zero, mul_zero]
  rw [hsum, sum_image]
  · simp only [actionVector, ite_true, if_true]
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

/-- The coordinate normalization translates entropy gains exactly into
the unnormalized costs of a band action. -/
theorem actionVector_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child) (cost : β × σ → ℝ)
    {action : β → σ} (haction : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ coordinate ∈ bandCoordinates band,
        (-cost coordinate / (mass coordinate.1 : ℝ)) * (actionVector mass action coordinate : ℝ)) =
          ∑ child, cost (child, action child) := by
  rw [actionVector_inner_product band mass _ haction, mul_sum]
  apply sum_congr rfl
  intro child _
  have hmass : (mass child : ℝ) ≠ 0 := by exact_mod_cast (hpos child).ne'
  have htotal : ((∑ child, mass child : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (sum_pos (fun child _ => hpos child) univ_nonempty).ne'
  rw [Rat.cast_div]
  field_simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem finiteBellman_spatial {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ)
    (hL : 0 ≤ L) (query query' : Parent)
    (hfallback : fallback query ≤ fallback query' + L * distance query query')
    (htriangle : ∀ center, distance query center ≤ distance query' center + distance query query') :
    finiteBellman fallback distance L actions child query ≤
      finiteBellman fallback distance L actions child query' + L * distance query query' := by
  apply finiteMinimum_map_spatial _ _ _ _ _ _ hfallback
  intro action _
  have hdist := mul_le_mul_of_nonneg_left (htriangle action.center) hL
  dsimp [bellmanActionValue]
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prefix costs used by the predicted bands

A prefix is a restriction of an enumerated wide action. The last jump is
evaluated at the proposed real shift. Taking the minimum over the actual
finite list, with its first member duplicated as the fallback, gives the
exact prefix minimum and its 1-Lipschitz property.
-/

namespace EditApproximation

open Finset

theorem realConnectionBudget_finish_lipschitz {n : ℕ} (start : ℝ)
    (states : List (TargetInterval n)) (finish finish' : ℝ) :
    |realConnectionBudget start states finish - realConnectionBudget start states finish'| ≤
      |finish - finish'| := by
  induction states generalizing start with
  | nil =>
    have h := abs_abs_sub_abs_le_abs_sub (start - finish) (start - finish')
    have heq : start - finish - (start - finish') = -(finish - finish') := by ring
    simpa only [realConnectionBudget, heq, abs_neg] using h
  | cons state rest ih =>
    have heq : realConnectionBudget start (state :: rest) finish -
        realConnectionBudget start (state :: rest) finish' =
        realConnectionBudget state.hi rest finish - realConnectionBudget state.hi rest finish' := by
      simp only [realConnectionBudget]
      ring
    rw [heq]
    exact ih state.hi

theorem widePrefixCost_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixCost parent r states child j p - widePrefixCost parent r states child j p'| ≤
      |p - p'| := by
  have h := realConnectionBudget_finish_lipschitz (r.lo : ℝ) ((List.ofFn states).take j)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p')
  have heq : ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p) -
      ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p') = p - p' := by ring
  simpa only [widePrefixCost, add_sub_add_right_eq_sub, heq] using h

theorem widePrefixMinimum_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixMinimum parent r actions hnonempty child j p -
      widePrefixMinimum parent r actions hnonempty child j p'| ≤ |p - p'| := by
  have hforward (p p' : ℝ) : widePrefixMinimum parent r actions hnonempty child j p ≤
      widePrefixMinimum parent r actions hnonempty child j p' + |p - p'| := by
    apply finiteMinimum_map_spatial
    · have h := widePrefixCost_lipschitz parent r (actions.head hnonempty) child j p p'
      linarith [(abs_le.mp h).2]
    · intro action ha
      have h := widePrefixCost_lipschitz parent r action child j p p'
      linarith [(abs_le.mp h).2]
  exact abs_le.mpr ⟨by have h := hforward p' p; rw [abs_sub_comm p' p] at h; linarith,
    by linarith [hforward p p']⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

theorem triangularChoice_fiber_card (K : ℕ) (j : Fin K) :
    Fintype.card {integer : Fin (optimizerTriangularMass K) // triangularChoice K integer = j} = j.val + 1 := by
  have hcard := Fintype.card_congr (triangularChoiceFiberEquiv K j.val j.isLt)
  simpa only [Fin.ext_iff, Fintype.card_fin] using hcard

/-- Exact coordinate mean of the sampler, including repeated selected
actions, equals the actual rational optimizer iterate. -/
theorem triangularChoice_coordinate_mean {ι : Type*} (initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (K : ℕ) (hK : 0 < K) (i : ι) :
    (∑ integer : Fin (optimizerTriangularMass K), selected (triangularChoice K integer).val i) /
        optimizerTriangularMass K = rationalOptimizerIterate initial selected K i := by
  classical
  have hsum : (∑ integer : Fin (optimizerTriangularMass K), selected (triangularChoice K integer).val i) =
      ∑ j : Fin K, ((j.val + 1 : ℕ) : ℚ) * selected j.val i := by
    rw [← Fintype.sum_fiberwise' (triangularChoice K) (fun j => selected j.val i)]
    apply sum_congr rfl
    intro j hj
    rw [sum_const, card_univ, triangularChoice_fiber_card, nsmul_eq_mul]
  have hmixture := rationalOptimizerIterate_eq_mixture initial selected (K - 1) i
  rw [Nat.sub_add_cancel (show 1 ≤ K by omega)] at hmixture
  rw [hsum, sum_div, hmixture, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  rw [← optimizerSampler_block_weight K j.val hK]
  ring

/-- The exactly sampled action has the mean computed by the finite
rational optimizer, with no distinction assumption on its selections. -/
theorem finiteRationalOptimizer_sampler_mean {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G K : ℕ) (hK : 0 < K) (i : ι) :
    (∑ integer : Fin (optimizerTriangularMass K),
      finiteOptimizerSelection coordinates vertices linear G (triangularChoice K integer).val i) /
        optimizerTriangularMass K = finiteRationalOptimizer coordinates vertices linear G K i := by
  rw [finiteRationalOptimizer_eq_iterate]
  exact triangularChoice_coordinate_mean _ _ K hK i

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual comparison prefixes in the finite wide action family

The cut is the start of the remaining comparator suffix, or the parent's
end when that suffix is empty. Splitting at this cut preserves the literal
connection budget. Splicing any enumerated prefix to the comparator suffix
remains an enumerated wide action.
-/

namespace EditApproximation

open Finset

theorem connectionPrefixBoundary_ofFn {n M : ℕ} (states : Fin M → TargetInterval n)
    (finish : ℕ) (j : Fin M) :
    connectionPrefixBoundary (List.ofFn states) finish j.val = (states j).lo := by
  simp only [connectionPrefixBoundary, List.head?_drop, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.map_some, Option.getD_some]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bands
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Predicted-band geometry

The prefix-cost predictor is 1-Lipschitz, while its velocity has a strict
margin below one. This gives narrow bands without a convexity assumption
on the set of allowed endpoints (Sections 5 and 6 of the manuscript).
-/

namespace EditApproximation

theorem predicted_band_diameter {prefixCost : ℝ → ℝ}
    {origin velocity margin width p q : ℝ}
    (hmargin : 0 < margin) (hvelocity : |velocity| ≤ 1 - margin)
    (hLipschitz : |prefixCost p - prefixCost q| ≤ |p - q|)
    (hp : inPredictedBand prefixCost origin velocity margin width p)
    (hq : inPredictedBand prefixCost origin velocity margin width q) :
    |p - q| ≤ 2 * width := by
  have hid : p - q =
      (p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q) +
        velocity * (prefixCost p - prefixCost q) := by ring
  have htri := (abs_add_le
    ((p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q))
    (velocity * (prefixCost p - prefixCost q))).trans
      (add_le_add (abs_sub _ _) le_rfl)
  rw [← hid, abs_mul] at htri
  have hprod := mul_le_mul hvelocity hLipschitz (abs_nonneg _)
    ((abs_nonneg velocity).trans hvelocity)
  change |p - origin - velocity * prefixCost p| ≤ margin * width at hp
  change |q - origin - velocity * prefixCost q| ≤ margin * width at hq
  have hscaled : margin * |p - q| ≤ margin * (2 * width) := by nlinarith
  exact le_of_mul_le_mul_left hscaled hmargin

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalPrefix
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution and exact real casts of the finite band predictor. -/

namespace EditApproximation

open Finset



theorem rationalConnectionBudget_cast {n : ℕ} (start finish : ℚ) (states : List (TargetInterval n)) :
    (rationalConnectionBudget start states finish : ℝ) = realConnectionBudget start states finish := by
  induction states generalizing start with
  | nil => simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_abs, Rat.cast_sub]
  | cons state rest ih =>
    simp only [rationalConnectionBudget, realConnectionBudget, Rat.cast_add, Rat.cast_abs,
      Rat.cast_sub, Rat.cast_natCast, ih]



theorem rationalWidePrefixCost_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixCost parent r states child j p : ℝ) =
      widePrefixCost parent r states (fun i s => (child i s : ℝ)) j p := by
  simp only [rationalWidePrefixCost, widePrefixCost, Rat.cast_add, Rat.cast_sum,
    rationalConnectionBudget_cast, Rat.cast_natCast]
  congr 1
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp



theorem rationalWidePrefixMinimum_cast {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ) :
    (rationalWidePrefixMinimum parent r actions hnonempty child j p : ℝ) =
      widePrefixMinimum parent r actions hnonempty (fun i s => (child i s : ℝ)) j p := by
  rw [rationalWidePrefixMinimum, rationalMinimum_cast]
  simp only [widePrefixMinimum, rationalWidePrefixCost_cast, List.map_map, Function.comp_def]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBands
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The literal finite predicted band

The band is a rationally decidable filter of the enumerated wide actions.
Its internal-cut diameter follows from the actual finite prefix predictor,
without assuming a predictor Lipschitz contract.
-/

namespace EditApproximation









theorem computedBand_cut_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau)
    (child : Fin M → TargetInterval ny → ℚ) (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (j : Fin M) (hj : 0 < j.val) :
    (Nat.dist (states j).lo (states' j).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
  obtain ⟨hnonempty, hmem, hvelocity, hpredicate⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hmem', hvelocity', hpredicate'⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  let predictor := fun p : ℝ => widePrefixMinimum parent r (wideActionList M parent r b P)
    hnonempty (fun i s => (child i s : ℝ)) j.val p
  have hvelocityR : |(velocity : ℝ)| ≤ 1 - (tau : ℝ) := by exact_mod_cast hvelocity
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau
  have hband (s : Fin M → TargetInterval ny)
      (hs : bandActionPredicate parent r b tau theta velocity (wideActionList M parent r b P) hnonempty child s) :
      inPredictedBand predictor ((r.lo : ℝ) - parent.lo) velocity tau
        ((theta : ℝ) * b / M) (bandCutShift parent s j) := by
    have h := hs.2.2 j hj
    have hR : ((|bandCutShift parent s j - ((r.lo : ℚ) - parent.lo) - velocity *
          rationalWidePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j.val
            (bandCutShift parent s j)| : ℚ) : ℝ) ≤ ((tau * theta * b / M : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      rationalWidePrefixMinimum_cast] at hR
    simpa only [inPredictedBand, predictor, mul_assoc, mul_div_assoc] using hR
  have hdiam := predicted_band_diameter htauR hvelocityR
    (widePrefixMinimum_lipschitz parent r (wideActionList M parent r b P) hnonempty
      (fun i s => (child i s : ℝ)) j.val _ _)
    (hband states hpredicate) (hband states' hpredicate')
  have hpoint : ((bandCutShift parent states j : ℚ) : ℝ) -
      ((bandCutShift parent states' j : ℚ) : ℝ) = (states j).lo - ((states' j).lo : ℝ) := by
    simp only [bandCutShift, Rat.cast_sub, Rat.cast_natCast]
    ring
  rw [hpoint, natural_distance_cast] at hdiam
  simpa only [mul_div_assoc, mul_assoc] using hdiam

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal band endpoint geometry and rounding guards

The full child endpoint diameter follows from the computed internal cuts
and zero connection, including the two outside endpoints.
-/

namespace EditApproximation

open Finset

theorem connectionBudget_zero_head {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0) :
    (states.head?.map TargetInterval.lo).getD start = start := by
  cases states with
  | nil => rfl
  | cons state rest =>
    have hdistance : Nat.dist start state.lo = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    exact (Nat.eq_of_dist_eq_zero hdistance).symm

/-- Each actual right endpoint is the next actual left endpoint, or the
parent's end when this is the last child. -/
theorem connectionBudget_zero_right {n : ℕ} (states : List (TargetInterval n))
    (start finish : ℕ) (hzero : connectionBudget start states finish = 0)
    (i : ℕ) (hi : i < states.length) :
    states[i].hi = connectionPrefixBoundary states finish (i + 1) := by
  induction states generalizing start i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons state rest ih =>
    have htail : connectionBudget state.hi rest finish = 0 := by
      change Nat.dist start state.lo + connectionBudget state.hi rest finish = 0 at hzero
      omega
    cases i with
    | zero =>
      cases rest with
      | nil =>
        exact Nat.eq_of_dist_eq_zero htail
      | cons next rest =>
        have hdistance : Nat.dist state.hi next.lo = 0 := by
          change Nat.dist state.hi next.lo + connectionBudget next.hi rest finish = 0 at htail
          omega
        exact Nat.eq_of_dist_eq_zero hdistance
    | succ i =>
      have hprev := ih state.hi htail i (by simp only [List.length_cons] at hi; omega)
      simpa only [List.getElem_cons_succ, connectionPrefixBoundary, List.drop_succ_cons] using hprev

theorem zero_connection_left_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) (hi : i.val = 0) : (states i).lo = r.lo := by
  have hhead := connectionBudget_zero_head (List.ofFn states) r.lo r.hi hzero
  have hM : 0 < M := by have := i.isLt; omega
  simp only [List.head?_eq_getElem?, List.getElem?_ofFn, dite_eq_left hM,
    Option.map_some, Option.getD_some] at hhead
  have hequal : (⟨0, hM⟩ : Fin M) = i := Fin.ext hi.symm
  rw [hequal] at hhead
  exact hhead

theorem zero_connection_right_endpoint {n M : ℕ} (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (hzero : endpointActionConnection r states = 0)
    (i : Fin M) :
    (states i).hi = connectionPrefixBoundary (List.ofFn states) r.hi (i.val + 1) := by
  have h := connectionBudget_zero_right (List.ofFn states) r.lo r.hi hzero i.val
    (by simp only [List.length_ofFn]; exact i.isLt)
  rw [List.getElem_ofFn] at h
  exact h

/-- Full endpoint distance, including first/last endpoints, for every two
members of the literal computed band. -/
theorem computedBand_child_endpoint_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child : Fin M → TargetInterval ny → ℚ)
    (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (i : Fin M) :
    (targetEndpointDistance (states i) (states' i) : ℝ) ≤ 4 * (theta : ℝ) * b / M := by
  have hthetaR : (0 : ℝ) ≤ theta := by exact_mod_cast htheta
  have hthetaBound : 0 ≤ 2 * (theta : ℝ) * b / M := by positivity
  obtain ⟨hnonempty, hwide, hv, hpredicate⟩ := computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hwide', hv', hpredicate'⟩ := computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  have hlo : (Nat.dist (states i).lo (states' i).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    by_cases hi : 0 < i.val
    · exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates' i hi
    · have hi0 : i.val = 0 := by omega
      rw [zero_connection_left_endpoint r states hpredicate.1 i hi0,
        zero_connection_left_endpoint r states' hpredicate'.1 i hi0, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  have hhi : (Nat.dist (states i).hi (states' i).hi : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
    rw [zero_connection_right_endpoint r states hpredicate.1 i,
      zero_connection_right_endpoint r states' hpredicate'.1 i]
    by_cases hnext : i.val + 1 < M
    · rw [connectionPrefixBoundary_ofFn states r.hi ⟨i.val + 1, hnext⟩,
        connectionPrefixBoundary_ofFn states' r.hi ⟨i.val + 1, hnext⟩]
      exact computedBand_cut_diameter parent r b P tau theta velocity htau child states states' hstates hstates'
        ⟨i.val + 1, hnext⟩ (by change 0 < i.val + 1; omega)
    · have hdrop : M ≤ i.val + 1 := by omega
      simp only [connectionPrefixBoundary, List.drop_eq_nil_iff.mpr
        (show (List.ofFn states).length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.drop_eq_nil_iff.mpr
        (show (List.ofFn states').length ≤ i.val + 1 by simpa only [List.length_ofFn] using hdrop),
        List.head?_nil, Option.map_none, Option.getD_none, Nat.dist_self, Nat.cast_zero]
      exact hthetaBound
  unfold targetEndpointDistance
  push_cast
  convert add_le_add hlo hhi using 1
  all_goals try with_reducible_and_instances rfl
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandEnvelopes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual dyadic child envelopes

The maximum scans the actual finite band. The dyadic ceiling uses the
computable integer upper logarithm of a positive rational, including values
below one.
-/

namespace EditApproximation

open Finset



theorem le_rationalMaximum_member (fallback : ℚ) (values : List ℚ) (value : ℚ)
    (hvalue : value ∈ values) : value ≤ rationalMaximum fallback values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons head rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact le_max_left _ _
    · exact (ih hrest).trans (le_max_right _ _)



/-- Zero is a harmless duplicated fallback under the initial table lower
invariant. The positive b/M floor ensures that the ceiling input is positive. -/


theorem bandChildEnvelope_lower {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (b : ℚ) / M ≤ bandChildEnvelope b band initial i ∧
      ∀ action ∈ band, initial i (action i) ≤ bandChildEnvelope b band initial i := by
  have hceil := Int.self_le_zpow_clog (R := ℚ) (by decide : 1 < 2)
    (max ((b : ℚ) / M) (rationalMaximum 0 (band.map fun action => initial i (action i))))
  refine ⟨(le_max_left _ _).trans hceil, ?_⟩
  intro action ha
  exact (le_rationalMaximum_member 0 _ _ (List.mem_map.mpr ⟨action, ha, rfl⟩)).trans
    ((le_max_right _ _).trans hceil)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Actual rounded band actions pass the finite guards

Each child uses its own envelope-derived integer spacing. The action is
rounded with literal integer division; wide-grid, radius and imbalance
claims are proved for these returned states.
-/

namespace EditApproximation

open Finset





theorem bandChildEnvelope_pos {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    0 < bandChildEnvelope b band initial i := by
  unfold bandChildEnvelope rationalDyadicCeiling
  positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChildIncrements
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Normalized increments of the actual child tables

The entropy hypotheses follow from monotonicity, bounds by the fixed child
mass, and spatial regularity. The table indices here start at zero, so the
gain at index `t` uses the table before update `t+1`.
-/

namespace EditApproximation

open Finset





theorem childDecrement_telescope {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (S : ℕ) (i : β × σ) :
    (∑ t ∈ range S, childDecrement mass table t i) =
      (table 0 i - table S i) / mass i.1 := by
  induction S with
  | zero => simp [childDecrement]
  | succ S ih =>
    rw [sum_range_succ, ih]
    unfold childDecrement
    ring

theorem childDecrement_nonneg {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (t : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hmono : table (t + 1) i ≤ table t i) :
    (0 : ℝ) ≤ childDecrement mass table t i := by
  exact_mod_cast div_nonneg (sub_nonneg.mpr hmono) hmass.le

theorem childDecrement_total_le {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (S : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hzero : 0 ≤ table S i) (hupper : table 0 i ≤ mass i.1) :
    (∑ t ∈ range S, (childDecrement mass table t i : ℝ)) ≤ 1 := by
  have htotal : (∑ t ∈ range S, childDecrement mass table t i) ≤ 1 := by
    rw [childDecrement_telescope]
    apply (div_le_one₀ hmass).2
    linarith
  exact_mod_cast htotal

theorem childGain_decrement_identity {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ) (i : β × σ) :
    childGain mass table t i + (1 - κ) * childDecrement mass table t i =
      -(κ * table t i + (1 - κ) * table (t + 1) i) / mass i.1 := by
  unfold childGain childDecrement
  ring

theorem childGain_decrement_bounds {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hκ : 0 ≤ κ) (hκone : κ ≤ 1)
    (hold : 0 ≤ table t i ∧ table t i ≤ mass i.1)
    (hnew : 0 ≤ table (t + 1) i ∧ table (t + 1) i ≤ mass i.1) :
    -1 ≤ (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i ∧
      (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i ≤ 0 := by
  have hweighted0 : 0 ≤ κ * table t i + (1 - κ) * table (t + 1) i :=
    add_nonneg (mul_nonneg hκ hold.1) (mul_nonneg (by linarith) hnew.1)
  have hweighted1 : κ * table t i + (1 - κ) * table (t + 1) i ≤ mass i.1 := by
    have ha := mul_le_mul_of_nonneg_left hold.2 hκ
    have hb := mul_le_mul_of_nonneg_left hnew.2 (by linarith : 0 ≤ 1 - κ)
    nlinarith
  have hbounds : -1 ≤ childGain mass table t i + (1 - κ) * childDecrement mass table t i ∧
      childGain mass table t i + (1 - κ) * childDecrement mass table t i ≤ 0 := by
    rw [childGain_decrement_identity]
    constructor
    · apply (le_div_iff₀ hmass).2
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hweighted0) hmass.le
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

theorem multiplicative_spatial_absolute {x y mass δ charge : ℝ}
    (hδ : 0 ≤ δ) (hx : x ≤ mass) (hy : y ≤ mass)
    (hxy : x ≤ (1 + δ) * y + charge) (hyx : y ≤ (1 + δ) * x + charge) :
    |x - y| ≤ δ * mass + charge := by
  have hxm := mul_le_mul_of_nonneg_left hx hδ
  have hym := mul_le_mul_of_nonneg_left hy hδ
  apply abs_le.mpr
  constructor <;> nlinarith

theorem normalized_decrement_range {old new old' new' mass δ spatial : ℝ}
    (hmass : 0 < mass)
    (hold : |old - old'| ≤ δ * mass + spatial)
    (hnew : |new - new'| ≤ δ * mass + spatial) :
    |(old - new) / mass - (old' - new') / mass| ≤ 2 * δ + 2 * spatial / mass := by
  have hid : (old - new) / mass - (old' - new') / mass =
      ((old - old') - (new - new')) / mass := by ring
  rw [hid, abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).2
  have htriangle := (abs_sub _ _).trans (add_le_add hold hnew)
  have hcancel : (2 * δ + 2 * spatial / mass) * mass = 2 * δ * mass + 2 * spatial := by
    field_simp
  rw [hcancel]
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OnlineActionDraw
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite rational optimizer samples actual band actions, retaining their labels through ties. -/

namespace EditApproximation

open Finset

theorem finiteOptimizerActionDraw_mean {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K) (coordinate : β × σ) :
    (∑ integer : Fin (optimizerTriangularMass K),
      actionVector mass (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate) /
        optimizerTriangularMass K =
      finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G K coordinate := by
  have hselected (integer : Fin (optimizerTriangularMass K)) :
      actionVector mass (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate =
        finiteOptimizerSelection (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G
          (triangularChoice K integer).val coordinate :=
    congrFun (finiteOptimizerAction_spec band hband mass linear G (triangularChoice K integer).val).2 coordinate
  simp_rw [hselected]
  exact finiteRationalOptimizer_sampler_mean _ _ linear G K hK coordinate

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_SampledRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact sampled action costs

The sampler's finite law translates the computed rational vector into its
expected linear cost. Correlation with a group-estimation failure is not
excluded or needed in this identity.
-/

namespace EditApproximation

open Finset

theorem uniformMean_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω => a * f ω) = a * uniformMean f := by
  simp only [uniformMean, ← mul_sum, mul_div_assoc]

theorem uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by
  simp only [uniformMean, sum_const, card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ a hcard

theorem actionVector_child_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ)
    {action : β → σ} (ha : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ i ∈ bandCoordinates band,
        ((childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i) *
          (actionVector mass action i : ℝ)) =
      (∑ child, (table (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (table t (child, action child) : ℝ)) -
          ∑ child, (table (t + 1) (child, action child) : ℝ)) := by
  have hidentity := actionVector_cost_identity band mass hpos
    (fun i => (κ : ℝ) * table t i + (1 - (κ : ℝ)) * table (t + 1) i) ha
  have hgain i : (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i =
      -((κ : ℝ) * table t i + (1 - (κ : ℝ)) * table (t + 1) i) / (mass i.1 : ℝ) := by
    have hid := childGain_decrement_identity mass table κ t i
    exact_mod_cast hid
  simp_rw [hgain]
  rw [hidentity]
  simp only [sum_add_distrib, ← mul_sum]
  ring

theorem actionVector_comparator_cost_identity {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (t : ℕ)
    {action : β → σ} (ha : action ∈ band) :
    -((∑ child, mass child : ℚ) : ℝ) *
      (∑ i ∈ bandCoordinates band,
        ((childGain mass table t i : ℝ) + childDecrement mass table t i) *
          (actionVector mass action i : ℝ)) =
      ∑ child, (table (t + 1) (child, action child) : ℝ) := by
  simpa only [Rat.cast_zero, sub_zero, one_mul, zero_mul, add_zero] using
    actionVector_child_cost_identity band mass hpos table 0 t ha

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ListBandRegret
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regret and sampling for the literal finite band list

The numerical optimizer and exact sampler keep the same listed vertex
order. Passing to the finite set is used only for coordinate support and
convex-hull facts, never to reorder the executable optimizer.
-/

namespace EditApproximation

open Finset

theorem finiteOptimizerActionDraw_linear_mean {β σ : Type*} [Fintype β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K)
    (payoff : β × σ → ℝ) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      ∑ coordinate ∈ bandCoordinates band.toFinset,
        payoff coordinate * (actionVector mass
          (finiteOptimizerActionDraw band hband mass linear G K integer) coordinate : ℝ)) =
      ∑ coordinate ∈ bandCoordinates band.toFinset,
        payoff coordinate * (finiteRationalOptimizer (bandCoordinates band.toFinset)
          (band.map (actionVector mass)) linear G K coordinate : ℝ) := by
  unfold uniformMean
  rw [Fintype.card_fin, sum_comm, sum_div]
  apply sum_congr rfl
  intro coordinate hc
  rw [← mul_sum, mul_div_assoc]
  congr 1
  exact_mod_cast finiteOptimizerActionDraw_mean band hband mass linear G K hK coordinate

/-- Exact expected weighted child cost of the returned optimizer action. -/
theorem finiteOptimizerActionDraw_child_cost_mean {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ)
    (linear : β × σ → ℚ) (G K : ℕ) (hK : 0 < K) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := finiteOptimizerActionDraw band hband mass linear G K integer
      (∑ child, (table (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (table t (child, action child) : ℝ)) -
          ∑ child, (table (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates band.toFinset,
          ((childGain mass table t coordinate : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t coordinate) *
            (finiteRationalOptimizer (bandCoordinates band.toFinset)
              (band.map (actionVector mass)) linear G K coordinate : ℝ) := by
  have hpoint (integer : Fin (optimizerTriangularMass K)) := actionVector_child_cost_identity
    band.toFinset mass hpos table κ t (List.mem_toFinset.mpr
      (finiteOptimizerActionDraw_mem band hband mass linear G K integer))
  simp_rw [← hpoint]
  rw [uniformMean_mul, finiteOptimizerActionDraw_linear_mean band hband mass linear G K hK]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalWideSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial bounds for a literal rational refinement update. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_map_spatial {ι : Type*} (indices : List ι)
    (fallback fallback' charge : ℚ) (value value' : ι → ℚ)
    (hfallback : fallback ≤ fallback' + charge)
    (hvalue : ∀ i ∈ indices, value i ≤ value' i + charge) :
    rationalMinimum fallback (indices.map value) ≤
      rationalMinimum fallback' (indices.map value') + charge := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    change min (value i) (rationalMinimum fallback (rest.map value)) ≤
      min (value' i) (rationalMinimum fallback' (rest.map value')) + charge
    rw [← min_add_add_right]
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem rationalActionValue_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (L : ℚ) (hL : 0 ≤ L) (child : Child → ℚ)
    (q q' : TargetInterval ny) (action : RationalBellmanAction (TargetInterval ny) Child M) :
    rationalActionValue (fun q r => targetEndpointDistance q r) L child q action ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L child q' action +
        L * targetEndpointDistance q q' := by
  have htriangle : (targetEndpointDistance q action.center : ℚ) ≤
      targetEndpointDistance q' action.center + targetEndpointDistance q q' := by
    exact_mod_cast targetEndpointDistance_triangle q q' action.center
  have h := mul_le_mul_of_nonneg_left htriangle hL
  dsimp only [rationalActionValue]
  linarith only [h]

theorem rationalBellman_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (actions : List (RationalBellmanAction (TargetInterval ny) Child M)) (child : Child → ℚ)
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q ≤
      rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _ hinit
  intro action _
  exact rationalActionValue_spatial L hL child q q' action

theorem rationalWideStepCone_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalWideStepCone parent representatives P initial L old current groups q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _
    (rationalBellman_spatial initial L hL _ old q q' hinit)
  intro action _
  exact rationalActionValue_spatial L hL current q q' action

theorem rationalRefinementUpdate_le_cone (delta cone : ℚ) (online : Option ℚ) :
    rationalRefinementUpdate delta cone online ≤ cone := by
  cases online with
  | none => exact le_rfl
  | some value => exact min_le_left _ _

theorem rationalRefinementUpdate_div_lower (delta cone : ℚ) (online : Option ℚ)
    (hdelta : 0 ≤ delta) (hcone : 0 ≤ cone) :
    cone / (1 + delta) ≤ rationalRefinementUpdate delta cone online := by
  have hdiv : cone / (1 + delta) ≤ cone := div_le_self hcone (by linarith)
  cases online with
  | none => exact hdiv
  | some value => exact le_min hdiv (le_max_left _ _)

theorem rationalWideStep_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ) (hL : 0 ≤ L) (hdelta : 0 ≤ delta)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (online : TargetInterval ny → List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q')
    (hcone : 0 ≤ rationalWideStepCone parent representatives P initial L old current groups q') :
    rationalWideStep parent representatives P initial L delta old current groups (online q) q ≤
      (1 + delta) * rationalWideStep parent representatives P initial L delta old current groups (online q') q' +
        L * targetEndpointDistance q q' := by
  have hu := rationalRefinementUpdate_le_cone delta
    (rationalWideStepCone parent representatives P initial L old current groups q)
    (rationalOnlineMinimum ((online q).map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)))
  have hs := rationalWideStepCone_spatial parent representatives P initial L hL old current groups q q' hinit
  have hl := rationalRefinementUpdate_div_lower delta
    (rationalWideStepCone parent representatives P initial L old current groups q')
    (rationalOnlineMinimum ((online q').map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q')))
    hdelta hcone
  have hd : (0 : ℚ) < 1 + delta := by linarith
  have hl' := (div_le_iff₀ hd).mp hl
  change _ ≤ (1 + delta) * _ + _
  dsimp only [rationalWideStep] at *
  nlinarith only [hu, hs, hl']

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

theorem physicalRefinement_nonincreasing {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node (t + 1) q ≤
      physicalRefinement source target U N P F A T delta choices node t q := by
  have h := physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q
  exact h.2.trans h.1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial regularity of the actual local initial table and physical warmup. -/

namespace EditApproximation

theorem physicalBellman_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (q q' : TargetInterval target.length) :
    physicalBellman source target P L initial representatives value (node, q) ≤
      physicalBellman source target P L initial representatives value (node, q') +
        L * targetEndpointDistance q q' := by
  classical
  unfold physicalBellman
  dsimp only
  split_ifs with hbelow hleaf
  · exact hinit node q q'
  · exact finiteBellman_spatial (fun s => initial (node, s))
      (fun s t => targetEndpointDistance s t) L
      (actualWideActions (physicalSourceInterval source.length node) (representatives node) P)
      (fun is => value (physicalChild node hbelow is.1, is.2)) hL q q' (hinit node q q')
      (fun center => by exact_mod_cast targetEndpointDistance_triangle q q' center)
  · exact hinit node q q'

theorem physicalWarmup_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (t : ℕ) (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    physicalWarmup source target P L initial representatives t (node, q) ≤
      physicalWarmup source target P L initial representatives t (node, q') +
        L * targetEndpointDistance q q' := by
  cases t with
  | zero => exact hinit node q q'
  | succ t => exact physicalBellman_spatial source target P L hL initial representatives hinit _ node q q'

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementSpatial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity, exact zero states and spatial regularity of the full stage. -/

namespace EditApproximation

theorem stageInitial_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    stageInitial source target U N P F A (node, q) ≤
      stageInitial source target U N P F A (node, q') + (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hfactor := refinementFactor_spec A F (by omega)
  have h32 := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node q q'
  have hcharge : (32 * F : ℚ) * targetEndpointDistance q q' ≤
      (128 * F : ℚ) * targetEndpointDistance q q' := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by norm_num : (32 : ℚ) ≤ 128) (Nat.cast_nonneg F)
  change physicalInitialTable source target U N P F A (refinementFactor A F) (node, q) ≤
    physicalInitialTable source target U N P F A (refinementFactor A F) (node, q') +
      (128 * F : ℚ) * targetEndpointDistance q q'
  exact le_trans h32 (add_le_add_right hcharge
    (physicalInitialTable source target U N P F A (refinementFactor A F) (node, q')))

theorem physicalRefinement_nonneg {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  have h := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q).1
  have hzero : 0 ≤ physicalLower source target (refinementFactor A F : ℝ) (node, q) :=
    (abs_nonneg _).trans (le_max_right _ _)
  exact (Rat.cast_nonneg (K := ℝ)).mp (hzero.trans h)

theorem physicalRefinement_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ) (hdelta : 0 ≤ delta)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q q' : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q ≤
      (1 + delta) * physicalRefinement source target U N P F A T delta choices node t q' +
        (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hL : (0 : ℚ) ≤ 128 * F := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hinit (node : PhysicalNode M J) (r r' : TargetInterval target.length) :
      stageInitial source target U N P F A (node, r) ≤
        stageInitial source target U N P F A (node, r') + (128 * F : ℚ) * targetEndpointDistance r r' := by
    exact stageInitial_spatial source target U N P F A hsize hP hF hA hseed node r r'
  have hnonneg := physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q'
  have hmul := mul_nonneg hdelta hnonneg
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)] at hmul ⊢
      rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
      nlinarith only [hinit node q q', hmul]
    · cases t with
      | zero =>
        rw [physicalRefinement_zero] at hmul ⊢
        rw [physicalRefinement_zero]
        have hinitR (n : PhysicalNode M J) (r r' : TargetInterval target.length) :
            (stageInitial source target U N P F A (n, r) : ℝ) ≤
              (stageInitial source target U N P F A (n, r') : ℝ) +
                ((128 * F : ℚ) : ℝ) * targetEndpointDistance r r' := by
          exact_mod_cast hinit n r r'
        have hw := physicalWarmup_spatial source target P ((128 * F : ℚ) : ℝ)
          ((Rat.cast_nonneg (K := ℝ)).mpr hL)
          (fun s => (stageInitial source target U N P F A s : ℝ))
          (stageRepresentatives source target U N P F A) hinitR T node q q'
        have hwQ : stageWarmup source target U N P F A T (node, q) ≤
            stageWarmup source target U N P F A T (node, q') +
              (128 * F : ℚ) * targetEndpointDistance q q' := by
          apply (Rat.cast_le (K := ℝ)).mp
          simpa only [stageWarmup, rationalPhysicalWarmup_cast, Rat.cast_add, Rat.cast_mul,
            Rat.cast_natCast] using hw
        nlinarith only [hwQ, hmul]
      | succ t =>
        let children : PhysicalChildTables M target.length := fun i =>
          physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
        have hcone : 0 ≤ rationalWideStepCone (physicalSourceInterval source.length node)
            (stageRepresentatives source target U N P F A node) P
            (fun r => stageInitial source target U N P F A (node, r)) (128 * F)
            (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
            (choices.groups node children (t + 1)) q' := by
          rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf] at hnonneg
          exact hnonneg.trans (rationalRefinementUpdate_le_cone _ _ _)
        rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf,
          physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
        exact rationalWideStep_spatial _ _ P _ (128 * F) delta hL hdelta _ _ _
          (choices.online node children (t + 1)) q q' (hinit node q q') hcone
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)] at hmul ⊢
    rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)]
    nlinarith only [hinit node q q', hmul]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset

theorem bandCoordinate_restriction {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (coordinate : β × σ)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    ∃ action ∈ band, action coordinate.1 = coordinate.2 := by
  obtain ⟨action, haction, hcoordinate⟩ := mem_biUnion.mp hcoordinate
  obtain ⟨child, _, hequal⟩ := mem_image.mp hcoordinate
  cases hequal
  exact ⟨action, List.mem_toFinset.mp haction, rfl⟩

theorem representativeBandActions_diameter {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child : Fin M → TargetInterval target.length → ℚ)
    (first second : Fin M → TargetInterval target.length)
    (hfirst : first ∈ representativeBandActions source target parent r b P tau theta child)
    (hsecond : second ∈ representativeBandActions source target parent r b P tau theta child) (i : Fin M) :
    (targetEndpointDistance (first i) (second i) : ℝ) ≤ 4 * (theta : ℝ) * b / M := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at hfirst
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at hfirst hsecond
      exact computedBand_child_endpoint_diameter parent r b P tau theta _ htau htheta child
        first second hfirst hsecond i
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at hfirst


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

variable (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "initial" => physicalBandChildInitial source target U N P F A node hbelow
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

theorem physicalBandEnvelope_pos (i : Fin M) : 0 < mass i :=
  bandChildEnvelope_pos b band initial i

theorem physicalBandHistory_nonincreasing (t : ℕ) (coordinate : Fin M × TargetInterval target.length) :
    history (t + 1) coordinate ≤ history t coordinate :=
  physicalRefinement_nonincreasing source target U N P F A T delta choices
    (physicalChild node hbelow coordinate.1) t coordinate.2

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
 theorem physicalBandHistory_bounds (t : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    0 ≤ history t coordinate ∧ history t coordinate ≤ mass coordinate.1 := by
  obtain ⟨action, haction, hequal⟩ := bandCoordinate_restriction band coordinate hcoordinate
  have hstage := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices (physicalChild node hbelow coordinate.1) t coordinate.2
  have hupper := (bandChildEnvelope_lower b band initial coordinate.1).2 action haction
  change initial coordinate.1 (action coordinate.1) ≤ mass coordinate.1 at hupper
  rw [hequal] at hupper
  exact ⟨physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices (physicalChild node hbelow coordinate.1) t coordinate.2,
    (hstage.2.1.trans (hstage.2.2.1.trans hstage.2.2.2.1)).trans hupper⟩

theorem physicalBand_coordinate_distance (htau : 0 < tau)
    (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    (targetEndpointDistance first.2 second.2 : ℝ) ≤ 4 * (theta : ℝ) * (mass first.1 : ℝ) := by
  obtain ⟨action, haction, hactionState⟩ := bandCoordinate_restriction band first hfirst
  obtain ⟨action', haction', hactionState'⟩ := bandCoordinate_restriction band second hsecond
  rw [← hsame] at hactionState'
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hdiameter := representativeBandActions_diameter source target
    (physicalSourceInterval source.length node) r b P tau theta htau htheta
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    action action' haction haction' first.1
  rw [hactionState, hactionState'] at hdiameter
  have hfloorQ : (b : ℚ) / M ≤ mass first.1 := (bandChildEnvelope_lower b band initial first.1).1
  have hfloor : (b : ℝ) / M ≤ (mass first.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hfloorQ
  have hweighted := mul_le_mul_of_nonneg_left hfloor
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ((Rat.cast_nonneg (K := ℝ)).mpr htheta))
  simp only [Rat.cast_zpow] at hdiameter hweighted ⊢
  calc
    _ ≤ 4 * (theta : ℝ) * ((b : ℝ) / M) := by simpa only [mul_div_assoc] using hdiameter
    _ ≤ _ := hweighted

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_decrement_total (S : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    (∑ t ∈ range S, (childDecrement mass history t coordinate : ℝ)) ≤ 1 := by
  exact childDecrement_total_le mass history S coordinate
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT S coordinate hcoordinate).1
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT 0 coordinate hcoordinate).2


include hM hsize hP hF hA hseed hT in
 theorem physicalBandHistory_absolute (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (t : ℕ) (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    |(history t first : ℝ) - (history t second : ℝ)| ≤
      (delta : ℝ) * (mass first.1 : ℝ) +
        4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) * (mass first.1 : ℝ) := by
  have hfirstBounds := physicalBandHistory_bounds source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT t first hfirst
  have hsecondBounds := physicalBandHistory_bounds source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT t second hsecond
  have hmassSame : mass second.1 = mass first.1 := congrArg (fun child => mass child) hsame.symm
  rw [hmassSame] at hsecondBounds
  have hforward : history t first ≤ (1 + delta) * history t second +
      (128 * F : ℚ) * targetEndpointDistance first.2 second.2 := by
    simpa only [physicalBandHistory, hsame] using physicalRefinement_spatial source target hM U N P F A
      hsize hP hF hA hseed T hT delta hdelta choices (physicalChild node hbelow first.1) t first.2 second.2
  have hbackward : history t second ≤ (1 + delta) * history t first +
      (128 * F : ℚ) * targetEndpointDistance second.2 first.2 := by
    simpa only [physicalBandHistory, hsame] using physicalRefinement_spatial source target hM U N P F A
      hsize hP hF hA hseed T hT delta hdelta choices (physicalChild node hbelow second.1) t second.2 first.2
  have hsym : targetEndpointDistance second.2 first.2 = targetEndpointDistance first.2 second.2 := by
    unfold targetEndpointDistance
    rw [Nat.dist_comm second.2.lo, Nat.dist_comm second.2.hi]
  rw [hsym] at hbackward
  have hforwardR : (history t first : ℝ) ≤ (1 + (delta : ℝ)) * (history t second : ℝ) +
      ((128 * F : ℚ) : ℝ) * targetEndpointDistance first.2 second.2 := by exact_mod_cast hforward
  have hbackwardR : (history t second : ℝ) ≤ (1 + (delta : ℝ)) * (history t first : ℝ) +
      ((128 * F : ℚ) : ℝ) * targetEndpointDistance first.2 second.2 := by exact_mod_cast hbackward
  have habsolute := multiplicative_spatial_absolute
    ((Rat.cast_nonneg (K := ℝ)).mpr hdelta)
    ((Rat.cast_le (K := ℝ)).mpr hfirstBounds.2) ((Rat.cast_le (K := ℝ)).mpr hsecondBounds.2)
    hforwardR hbackwardR
  have hdiameter := physicalBand_coordinate_distance source target U N P F A T node hbelow
    b thetaExponent tau r htau first second hfirst hsecond hsame
  have hL : (0 : ℝ) ≤ ((128 * F : ℚ) : ℝ) := by positivity
  have hcharge := mul_le_mul_of_nonneg_left hdiameter hL
  nlinarith only [habsolute, hcharge]

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_decrement_range (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (t : ℕ) (first second : Fin M × TargetInterval target.length)
    (hfirst : first ∈ bandCoordinates (band).toFinset) (hsecond : second ∈ bandCoordinates (band).toFinset)
    (hsame : first.1 = second.1) :
    |(childDecrement mass history t first : ℝ) - (childDecrement mass history t second : ℝ)| ≤
      2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) := by
  have hmass : (0 : ℝ) < (mass first.1 : ℝ) :=
    (Rat.cast_pos (K := ℝ)).mpr (physicalBandEnvelope_pos source target U N P F A T node hbelow
      b thetaExponent tau r first.1)
  have hold := physicalBandHistory_absolute source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta t first second hfirst hsecond hsame
  have hnew := physicalBandHistory_absolute source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta (t + 1) first second hfirst hsecond hsame
  have hrange := normalized_decrement_range hmass hold hnew
  have hcancel : 2 * (4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) * (mass first.1 : ℝ)) /
      (mass first.1 : ℝ) = 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ) := by
    calc
      _ = 2 * (4 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) *
          ((mass first.1 : ℝ) / (mass first.1 : ℝ)) := by ring
      _ = _ := by rw [div_self hmass.ne']; ring
  rw [hcancel] at hrange
  simp only [childDecrement, Rat.cast_div, Rat.cast_sub, ← hsame]
  exact hrange

include hM hsize hP hF hA hseed hT in
 theorem physicalBand_gain_bounds (κ : ℚ) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (t : ℕ) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates (band).toFinset) :
    -1 ≤ (childGain mass history t coordinate : ℝ) +
        (1 - (κ : ℝ)) * childDecrement mass history t coordinate ∧
      (childGain mass history t coordinate : ℝ) +
        (1 - (κ : ℝ)) * childDecrement mass history t coordinate ≤ 0 := by
  exact childGain_decrement_bounds mass history κ t coordinate
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
    hκ (by linarith only [hκhalf])
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT t coordinate hcoordinate)
    (physicalBandHistory_bounds source target U N P F A T delta choices node hbelow b thetaExponent tau r
      hM hsize hP hF hA hseed hT (t + 1) coordinate hcoordinate)


include hM in
/-- Exact conditional mean: only the current finite integer draw is averaged. -/
theorem physicalBandOnlineDraw_child_cost_mean (hband : band ≠ []) (η κ : ℚ)
    (G K t : ℕ) (hK : 0 < K) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates (band).toFinset,
          ((childGain mass history t coordinate : ℝ) +
            (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
              (finiteRationalOptimizer (bandCoordinates (band).toFinset)
                ((band).map (actionVector mass))
                (rationalOnlineLinear η κ (childGain mass history) (childDecrement mass history) t)
                G K coordinate : ℝ) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact finiteOptimizerActionDraw_child_cost_mean band hband mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    history κ t _ G K hK

include hM in
 theorem physicalBandOnlineDraw_computed_mean (hband : band ≠ []) (η κ : ℚ)
    (G K H t : ℕ) (hG : G = H + (bandCoordinates (band).toFinset).card + 2)
    (hK : K = G ^ 80) (hH : 4 ≤ H) :
    uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ))) =
      -((∑ child, mass child : ℚ) : ℝ) *
        ∑ coordinate ∈ bandCoordinates (band).toFinset,
          ((childGain mass history t coordinate : ℝ) +
            (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
              (computedOnlineVector (bandCoordinates (band).toFinset)
                ((band).map (actionVector mass)) η κ
                (childGain mass history) (childDecrement mass history) H t coordinate : ℝ) := by
  have hGpos : 0 < G := by omega
  have hKpos : 0 < K := by rw [hK]; exact pow_pos hGpos 80
  have hmean := physicalBandOnlineDraw_child_cost_mean source target U N P F A T delta choices
    node hbelow b thetaExponent tau r hM hband η κ G K t hKpos
  simpa only [computedOnlineVector, ← hG, ← hK] using hmean

include hM hsize hP hF hA hseed hT in
/-- The regret hypotheses are proved from the actual physical recurrence. -/
theorem physicalBand_computed_entropy_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (S H : ℕ) (η κ : ℚ) {comparison : Fin M → TargetInterval target.length}
    (hc : comparison ∈ band) (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) :
    (∑ t ∈ range S, ∑ coordinate ∈ bandCoordinates (band).toFinset,
        ((childGain mass history t coordinate : ℝ) + childDecrement mass history t coordinate) *
          (actionVector mass comparison coordinate : ℝ)) -
        Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) - 2 * (κ : ℝ) -
          (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ coordinate ∈ bandCoordinates (band).toFinset,
        ((childGain mass history t coordinate : ℝ) +
          (1 - (κ : ℝ)) * childDecrement mass history t coordinate) *
            (computedOnlineVector (bandCoordinates (band).toFinset)
              ((band).map (actionVector mass)) η κ
              (childGain mass history) (childDecrement mass history) H t coordinate : ℝ) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hband : band ≠ [] := List.ne_nil_of_mem hc
  apply list_band_computed_entropy_regret band hband mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    S H η κ _ (childGain mass history) (childDecrement mass history) hc hH hη hκ hκhalf hηrange
  · intro t _ coordinate _
    exact childDecrement_nonneg mass history t coordinate
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r coordinate.1)
      (physicalBandHistory_nonincreasing source target U N P F A T delta choices node hbelow t coordinate)
  · intro t _ first hfirst second hsecond hsame
    exact physicalBand_decrement_range source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta t first second hfirst hsecond hsame
  · intro coordinate hcoordinate
    exact physicalBand_decrement_total source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT S coordinate hcoordinate
  · intro t _ coordinate hcoordinate
    exact physicalBand_gain_bounds source target U N P F A T delta choices node hbelow
      b thetaExponent tau r hM hsize hP hF hA hseed hT κ hκ hκhalf t coordinate hcoordinate

include hM hsize hP hF hA hseed hT in
/-- Expected weighted cost regret of the returned physical-band action. -/
theorem physicalBandOnlineDraw_cost_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (S H G K : ℕ) (η κ : ℚ)
    (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
    {comparison : Fin M → TargetInterval target.length} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) :
    (∑ t ∈ range S, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      let action := physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
        b thetaExponent tau r hband η κ G K t integer
      (∑ child, (history (t + 1) (child, action child) : ℝ)) +
        (κ : ℝ) * ((∑ child, (history t (child, action child) : ℝ)) -
          ∑ child, (history (t + 1) (child, action child) : ℝ)))) ≤
      (∑ t ∈ range S, ∑ child, (history (t + 1) (child, comparison child) : ℝ)) +
        ((∑ child, mass child : ℚ) : ℝ) *
          (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
            (S : ℝ) / (H : ℝ) ^ 3) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hregret := physicalBand_computed_entropy_regret source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta S H η κ hc hH hη hκ hκhalf hηrange
  have hmass : (0 : ℝ) ≤ ((∑ child, mass child : ℚ) : ℝ) := by
    exact (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun child _ =>
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r child).le)
  have hscaled := mul_le_mul_of_nonpos_left hregret (neg_nonpos.mpr hmass)
  have hmean t := physicalBandOnlineDraw_computed_mean source target U N P F A T delta choices
    node hbelow b thetaExponent tau r hM hband η κ G K H t hG hK hH
  simp_rw [hmean]
  rw [← mul_sum]
  have hcomparison t := actionVector_comparator_cost_identity (band).toFinset mass
    (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r)
    history t (List.mem_toFinset.mpr hc)
  have hcomparisonSum := congrArg (fun value : ℕ → ℝ => ∑ t ∈ range S, value t) (funext hcomparison)
  rw [← mul_sum] at hcomparisonSum
  nlinarith only [hscaled, hcomparisonSum]


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalExpectedRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional prefix regret from the exact physical-band sampler. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem uniformMean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω => f ω - g ω) = uniformMean f - uniformMean g := by
  simp only [uniformMean, sum_sub_distrib, sub_div]

theorem sampledPrefixRegret_child_identity {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ)
    (clipped : ℕ → ℝ) (sample : ℕ → β → σ) (t : ℕ) :
    sampledPrefixRegret charge κ table clipped sample t =
      (∑ child, table (t + 1) (child, sample t child)) +
        κ * ((∑ child, table t (child, sample t child)) -
          ∑ child, table (t + 1) (child, sample t child)) - clipped (t + 1) := by
  unfold sampledPrefixRegret bandActionCost
  ring

section PhysicalPrefix

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
/-- Every deterministic prefix uses the same actual computed online mixtures.
Clipping comparison children only decreases the prefix regret. -/
theorem physicalBand_prefix_expected_regret_oai (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (C S H G K : ℕ) (hCS : C ≤ S) (η κ : ℚ)
    (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) (charge : ℝ) :
    (∑ t ∈ range C, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      sampledPrefixRegret charge (κ : ℝ) (fun t coordinate => (history t coordinate : ℝ))
        (physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison)
        (fun j => physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
          b thetaExponent tau r hband η κ G K j integer) t)) ≤
      ((∑ child, mass child : ℚ) : ℝ) *
        (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) := by
  have hGpos : 0 < G := by omega
  have hKpos : 0 < K := by rw [hK]; exact pow_pos hGpos 80
  let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hKpos)⟩
  have hcost := physicalBandOnlineDraw_cost_regret source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta hband C H G K η κ hG hK
    hc hH hη hκ hκhalf hηrange
  have hcomparison : (∑ t ∈ range C, ∑ child, (history (t + 1) (child, comparison child) : ℝ)) ≤
      ∑ t ∈ range C,
        physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison (t + 1) := by
    apply sum_le_sum
    intro t _
    exact sum_le_sum fun i _ => le_max_right _ _
  have hmass : (0 : ℝ) ≤ ((∑ child, mass child : ℚ) : ℝ) :=
    (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun i _ =>
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r i).le)
  have hprefix : (C : ℝ) / (H : ℝ) ^ 3 ≤ (S : ℝ) / (H : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hCS) (pow_nonneg (Nat.cast_nonneg H) 3)
  have hbudget := mul_le_mul_of_nonneg_left hprefix hmass
  simp_rw [sampledPrefixRegret_child_identity, uniformMean_sub, uniformMean_const]
  rw [sum_sub_distrib]
  nlinarith only [hcost, hcomparison, hbudget]

end PhysicalPrefix


end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalBand_prefix_expected_regret_oai.{u_1} := @OAI.EditApproximation.physicalBand_prefix_expected_regret_oai.{u_1}

-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgram_comparison_node_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:44:22.522066+00:00
-- url     : https://prove2.me/submissions/c3b84e66-19c3-410b-9412-cfcb6fc87ff3

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
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computed_comparison_band_mem
import Theorems.Thm_OAI_EditApproximation_physicalProgram_global_node_regret
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_zero_cost
import Theorems.Thm_OAI_EditApproximation_stageComparison_positive_movement
import Theorems.Thm_OAI_EditApproximation_stageWarmupMass_child_lower
import Theorems.Thm_OAI_EditApproximation_stageWarmup_invariants

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite representative list and the actual rounded comparison representative. -/

namespace EditApproximation

theorem rounded_comparison_representative {α : Type*} (source target : List α)
    (N P F : ℕ) (a : ℚ) (hP : 4 ≤ P) (hF : 0 ≤ (F : ℚ)) (ha : 0 < a)
    (initial : TargetInterval target.length → ℚ)
    (hlower : ∀ r, (stateEditCost source target r : ℚ) / a ≤ initial r)
    (hupper : ∀ r, initial r ≤ 2 * F * stateEditCost source target r)
    (q : TargetInterval target.length) (hc : 0 < stateEditCost source target q)
    (hN : stateEditCost source target q ≤ N) :
    let b := 2 ^ Nat.log 2 (stateEditCost source target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a initial := by
  dsimp only
  let b := 2 ^ Nat.log 2 (stateEditCost source target q)
  let r := roundInterval (seedGridSpacing b P) q
  have hscale := cost_dyadicScale _ N hc hN
  have hscaleLower : (b : ℚ) ≤ stateEditCost source target q := by exact_mod_cast hscale.2.1
  have hscaleUpper : (stateEditCost source target q : ℚ) < 2 * b := by exact_mod_cast hscale.2.2
  have he := rounded_seedGrid_error b P (by omega) q
  have he0 : (0 : ℚ) ≤ targetEndpointDistance q r := Nat.cast_nonneg _
  have hPr : (4 : ℚ) ≤ P := by exact_mod_cast hP
  have hsmall : (targetEndpointDistance q r : ℚ) ≤ b / 2 := by nlinarith only [he, he0, hPr]
  have hdist := abs_le.mp (stateEditCost_distance_abs source target q r)
  have hcrlo : (b : ℚ) / 4 ≤ stateEditCost source target r := by linarith only [hdist.1, hdist.2, hsmall, hscaleLower]
  have hcrhi : (stateEditCost source target r : ℚ) ≤ 4 * b := by
    have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
    linarith only [hdist.1, hdist.2, hsmall, hscaleUpper, hb0]
  apply representativeList_mem a initial r hscale.1 (roundInterval_on_grid _ q)
  · have hdiv := div_le_div_of_nonneg_right hcrlo ha.le
    have hid : (b : ℚ) / 4 / a = b / (4 * a) := by ring
    rw [hid] at hdiv
    exact hdiv.trans (hlower r)
  · have hmul := mul_le_mul_of_nonneg_left hcrhi (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hF)
    exact (hupper r).trans (by nlinarith only [hmul])

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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



theorem rationalMaximum_le (fallback upper : ℚ) (values : List ℚ)
    (hfallback : fallback ≤ upper) (hvalues : ∀ value ∈ values, value ≤ upper) :
    rationalMaximum fallback values ≤ upper := by
  induction values with
  | nil => exact hfallback
  | cons value rest ih =>
    exact max_le (hvalues value (by simp)) (ih (fun value hv => hvalues value (by simp [hv])))

theorem le_rationalMaximum_member (fallback : ℚ) (values : List ℚ) (value : ℚ)
    (hvalue : value ∈ values) : value ≤ rationalMaximum fallback values := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons head rest ih =>
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact le_max_left _ _
    · exact (ih hrest).trans (le_max_right _ _)



theorem rationalDyadicCeiling_bounds (value : ℚ) (hvalue : 0 < value) :
    value ≤ rationalDyadicCeiling value ∧ rationalDyadicCeiling value < 2 * value := by
  constructor
  · exact Int.self_le_zpow_clog (by decide : 1 < 2) value
  · have h := mul_lt_mul_of_pos_right
      (Int.zpow_pred_clog_lt_self (by decide : 1 < 2) hvalue) (by norm_num : (0 : ℚ) < 2)
    change (2 : ℚ) ^ (Int.clog 2 value - 1) * 2 < value * 2 at h
    have hexponent : Int.clog 2 value - 1 + 1 = Int.clog 2 value := by omega
    rw [← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0), hexponent] at h
    simpa only [rationalDyadicCeiling, mul_comm] using h

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

/-- Every finite envelope is bounded using the actual computed-band
endpoint diameter and the initial table's spatial inequality. -/
theorem bandChildEnvelope_upper {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hb : 0 < b) (hM : 0 < M)
    (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (comparison : Fin M → TargetInterval ny)
    (hcomparison : comparison ∈ computedBandActions parent r b P tau theta velocity child)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hinitial : ∀ i, 0 ≤ initial i (comparison i))
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    bandChildEnvelope b (computedBandActions parent r b P tau theta velocity child) initial i ≤
      2 * ((b : ℚ) / M) + 2 * initial i (comparison i) + 8 * L0 * theta * b / M := by
  let band := computedBandActions parent r b P tau theta velocity child
  let delta : ℚ := 4 * theta * b / M
  let upper := initial i (comparison i) + L0 * delta
  have hdelta : 0 ≤ delta := by dsimp only [delta] <;> positivity
  have hupper : 0 ≤ upper := add_nonneg (hinitial i) (mul_nonneg hL0 hdelta)
  have hmembers : ∀ value ∈ band.map (fun action => initial i (action i)), value ≤ upper := by
    intro value hvalue
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
    have hdistReal := computedBand_child_endpoint_diameter parent r b P tau theta velocity htau htheta
      child action comparison ha hcomparison i
    have hdist : (targetEndpointDistance (action i) (comparison i) : ℚ) ≤ delta := by exact_mod_cast hdistReal
    exact (hspatial i (action i) (comparison i)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist hL0))
  have hmaximum := rationalMaximum_le 0 upper _ hupper hmembers
  have hfloor : (0 : ℚ) < (b : ℚ) / M := div_pos (by exact_mod_cast hb) (by exact_mod_cast hM)
  have hpositive := hfloor.trans_le (le_max_left ((b : ℚ) / M)
    (rationalMaximum 0 (band.map fun action => initial i (action i))))
  have hceil := (rationalDyadicCeiling_bounds _ hpositive).2.le
  have hmaxUpper : max ((b : ℚ) / M)
      (rationalMaximum 0 (band.map fun action => initial i (action i))) ≤ (b : ℚ) / M + upper := by
    apply max_le
    · exact le_add_of_nonneg_right hupper
    · exact hmaximum.trans (le_add_of_nonneg_left hfloor.le)
  apply hceil.trans
  have hmul := mul_le_mul_of_nonneg_left hmaxUpper (by norm_num : (0 : ℚ) ≤ 2)
  dsimp only [upper, delta] at hmul
  convert hmul using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The actual sum guard follows from the concrete envelopes, the initial
cone bounds at the comparison child states, and their actual edit costs. -/
theorem bandChildEnvelope_sum_guard {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (hb : 0 < b) (hM : 0 < M)
    (tau theta velocity : ℚ) (htau : 0 < tau) (htheta : 0 ≤ theta)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ computedBandActions parent r b P tau theta velocity child)
    (L0 F : ℚ) (hL0 : 0 ≤ L0) (hF : 1 ≤ F) (hsmall : L0 * theta ≤ 1)
    (hinitial : ∀ i, 0 ≤ initial i (comparison i))
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (hinitialUpper : ∀ i, initial i (comparison i) ≤ 2 * F * (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℚ))
    (hcomparisonCost : (∑ i : Fin M, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℚ)) ≤ 4 * b) :
    (∑ i : Fin M, bandChildEnvelope b
      (computedBandActions parent r b P tau theta velocity child) initial i) ≤ 64 * F * b := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hpoint := fun i => bandChildEnvelope_upper parent r b P hb hM tau theta velocity htau htheta
    child initial comparison hcomparison L0 hL0 hinitial hspatial i
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hpoint i)
  have hequal : (∑ i : Fin M, (2 * ((b : ℚ) / M) + 2 * initial i (comparison i) +
      8 * L0 * theta * b / M)) = 2 * b + 2 * (∑ i : Fin M, initial i (comparison i)) +
        8 * L0 * theta * b := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const,
      card_univ, Fintype.card_fin, ← mul_sum]
    simp only [nsmul_eq_mul]
    field_simp [hMr.ne']
  rw [hequal] at hsum
  have hinitSum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hinitialUpper i)
  rw [← mul_sum] at hinitSum
  have hFpos : 0 ≤ 2 * F := by linarith
  have hcost := mul_le_mul_of_nonneg_left hcomparisonCost hFpos
  have hsmallb := mul_le_mul_of_nonneg_right hsmall (show (0 : ℚ) ≤ b by positivity)
  have hFb := mul_le_mul_of_nonneg_right hF (show (0 : ℚ) ≤ b by positivity)
  nlinarith only [hsum, hinitSum, hcost, hsmallb, hFb]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRounding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer rounding spacings from the dyadic band envelopes

Taking the nonnegative part of the dyadic product exponent computes the
integer spacing max(1, theta*h). The resulting spacing preserves the wide
grid by actual divisibility of powers of two.
-/

namespace EditApproximation

open Finset





/-- Actual division rounding moves each endpoint by at most the scaled
child envelope, including the special spacing-one case. -/
theorem gridRound_scaled_error (spacing position : ℕ) (scaled : ℚ)
    (hspacing : (spacing : ℚ) = max 1 scaled) (hscaled : 0 ≤ scaled) :
    (Nat.dist position (gridRound spacing position) : ℚ) ≤ scaled := by
  have hpos : 0 < spacing := by
    have hone : (1 : ℚ) ≤ spacing := by rw [hspacing]; exact le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hone)
  by_cases hone : spacing = 1
  · simp only [hone, gridRound_one, Nat.dist_self, Nat.cast_zero]
    exact hscaled
  · have htwo : 1 < spacing := by omega
    have htwoR : (1 : ℚ) < spacing := by exact_mod_cast htwo
    have hscale : 1 < scaled := by
      by_contra hnot
      have hle : scaled ≤ 1 := le_of_not_gt hnot
      rw [max_eq_left hle] at hspacing
      linarith only [hspacing, htwoR]
    have hequal : (spacing : ℚ) = scaled := hspacing.trans (max_eq_right hscale.le)
    have herr : (Nat.dist position (gridRound spacing position) : ℚ) < spacing := by
      exact_mod_cast gridRound_error_lt spacing position hpos
    exact herr.le.trans_eq hequal

theorem dyadic_dvd_of_le {small large : ℕ}
    (hsmall : ∃ e : ℕ, small = 2 ^ e) (hlarge : ∃ e : ℕ, large = 2 ^ e)
    (hle : small ≤ large) : small ∣ large := by
  obtain ⟨s, rfl⟩ := hsmall
  obtain ⟨l, rfl⟩ := hlarge
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle)

theorem seedGridSpacing_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    ∃ e : ℕ, seedGridSpacing b P = 2 ^ e := by
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨p, rfl⟩ := hP
  by_cases horder : p ≤ s
  · refine ⟨s - p, ?_⟩
    rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow]
  · refine ⟨0, ?_⟩
    have hlt : 2 ^ s < 2 ^ p := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    simp only [seedGridSpacing, Nat.div_eq_of_lt hlt, max_eq_left (by decide : 0 ≤ 1), pow_zero]

/-- The envelope floor and the numerical theta*P ≥ M ensure that the
actual rounded integer spacing is a multiple of the actual wide grid. -/
theorem bandRoundSpacing_wide_grid {ny M b P : ℕ} (thetaExponent : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M)
    (hM : 0 < M) (hPpos : 0 < P)
    (hbPower : ∃ e : ℕ, b = 2 ^ e) (hPPower : ∃ e : ℕ, P = 2 ^ e)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P) :
    seedGridSpacing b P ∣ bandRoundSpacing thetaExponent b band initial i := by
  let theta : ℚ := 2 ^ (-(thetaExponent : ℤ))
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hPr : (0 : ℚ) < P := by exact_mod_cast hPpos
  have hratio : (M : ℚ) / P ≤ theta := (div_le_iff₀ hPr).2 hscale
  have hfloor : (b : ℚ) / P ≤ theta * ((b : ℚ) / M) := by
    calc
      _ = ((b : ℚ) / M) * ((M : ℚ) / P) := by field_simp [hMr.ne', hPr.ne']
      _ ≤ ((b : ℚ) / M) * theta :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg (Nat.cast_nonneg _) hMr.le)
      _ = _ := mul_comm _ _
  have henvelope := (bandChildEnvelope_lower b band initial i).1
  have hproduct := hfloor.trans (mul_le_mul_of_nonneg_left henvelope htheta)
  have hwide : (seedGridSpacing b P : ℚ) ≤
      max 1 (theta * bandChildEnvelope b band initial i) := by
    unfold seedGridSpacing
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le_max le_rfl ((Nat.cast_div_le (m := b) (n := P)).trans hproduct)
  have hspacing := bandRoundSpacing_exact thetaExponent b band initial i
  have hle : seedGridSpacing b P ≤ bandRoundSpacing thetaExponent b band initial i := by
    have h := hwide.trans_eq hspacing.symm
    exact_mod_cast h
  exact dyadic_dvd_of_le (seedGridSpacing_dyadic hbPower hPPower)
    ⟨_, rfl⟩ hle

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionGuards
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

theorem roundedBandAction_endpoint_error {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (Nat.dist (action i).lo (roundedBandAction thetaExponent b band initial action i).lo : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i ∧
      (Nat.dist (action i).hi (roundedBandAction thetaExponent b band initial action i).hi : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have hscaled : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le (bandChildEnvelope_pos b band initial i).le
  exact ⟨gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled,
    gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled⟩

theorem roundedBandAction_distance {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := roundedBandAction_endpoint_error thetaExponent b band initial action i
  unfold targetEndpointDistance
  push_cast
  convert add_le_add h.1 h.2 using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Actual rounded wide membership and imbalance guard. The sum premise
is supplied by bandChildEnvelope_sum_guard, and the remaining premises
are explicit computed-parameter inequalities. -/
theorem roundedBandAction_guards {α : Type*} (source target : List α)
    {M b P : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (thetaExponent : ℕ) (tau velocity : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child)
    (hM : 0 < M) (hPpos : 0 < P)
    (hbPower : ∃ e : ℕ, b = 2 ^ e) (hPPower : ∃ e : ℕ, P = 2 ^ e)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P)
    (F : ℚ)
    (hsmall : 64 * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 4)
    (htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 / 2)
    (hinitialGap : ∀ i s, |rationalStateGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤ initial i s)
    (hsum : (∑ i : Fin M, bandChildEnvelope b
      (computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child) initial i) ≤ 64 * F * b) :
    let band := computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    roundedBandAction thetaExponent b band initial action ∈ wideActionList M parent r b P ∧
      ∀ i, |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
          (roundedBandAction thetaExponent b band initial action i)| ≤ 2 * bandChildEnvelope b band initial i := by
  let theta : ℚ := 2 ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let envelope := fun i : Fin M => bandChildEnvelope b band initial i
  let rounded := roundedBandAction thetaExponent b band initial action
  have htheta0 : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have henv (i : Fin M) : 0 ≤ envelope i := (bandChildEnvelope_pos b band initial i).le
  have hsingle (i : Fin M) : envelope i ≤ ∑ j, envelope j :=
    single_le_sum (fun j _ => henv j) (mem_univ i)
  have hbudget (i : Fin M) : theta * envelope i ≤ 4 * b := by
    have h := (mul_le_mul_of_nonneg_left (hsingle i) htheta0).trans
      (mul_le_mul_of_nonneg_left hsum htheta0)
    have hb := mul_le_mul_of_nonneg_right hsmall (show (0 : ℚ) ≤ b by positivity)
    nlinarith only [h, hb]
  obtain ⟨hnonempty, hwide, hv, hpredicate⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child action haction
  have herr := roundedBandAction_endpoint_error thetaExponent b band initial action
  have hanchor (anchor before after : ℕ) (i : Fin M)
      (hbefore : Nat.dist anchor before ≤ 6 * b)
      (herror : (Nat.dist before after : ℚ) ≤ theta * envelope i) :
      Nat.dist anchor after ≤ 10 * b := by
    have htriangle : (Nat.dist anchor after : ℚ) ≤ (Nat.dist anchor before : ℚ) + Nat.dist before after := by
      exact_mod_cast Nat.dist.triangle_inequality anchor before after
    have hbeforeQ : (Nat.dist anchor before : ℚ) ≤ 6 * b := by exact_mod_cast hbefore
    have hafter : (Nat.dist anchor after : ℚ) ≤ 10 * b := by
      linarith only [htriangle, hbeforeQ, herror, hbudget i]
    exact_mod_cast hafter
  constructor
  · apply wideActionList_complete
    · intro i
      have hgrid := bandRoundSpacing_wide_grid thetaExponent band initial i hM hPpos hbPower hPPower hscale
      exact ⟨hgrid.trans (dvd_mul_right _ _), hgrid.trans (dvd_mul_right _ _)⟩
    · intro i
      exact hanchor _ _ _ i (hpredicate.2.1 i).1 (herr i).1
    · intro i
      exact hanchor _ _ _ i (hpredicate.2.1 i).2 (herr i).2
  · intro i
    have hbefore := (hinitialGap i (action i)).trans
      ((bandChildEnvelope_lower b band initial i).2 action haction)
    have hspatial := stateLengthGap_spatial
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (rounded i) (action i)
    rw [← rationalStateGap_cast, ← rationalStateGap_cast] at hspatial
    have hspatialQ : |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (rounded i)| ≤
        |rationalStateGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (action i)| +
          (targetEndpointDistance (rounded i) (action i) : ℚ) := by exact_mod_cast hspatial
    have hdistance := roundedBandAction_distance thetaExponent b band initial action i
    have hsym : targetEndpointDistance (rounded i) (action i) = targetEndpointDistance (action i) (rounded i) := by
      unfold targetEndpointDistance
      rw [Nat.dist_comm (rounded i).lo, Nat.dist_comm (rounded i).hi]
    rw [hsym] at hspatialQ
    have hscaled := mul_le_mul_of_nonneg_right htheta (henv i)
    nlinarith only [hbefore, hspatialQ, hdistance, hscaled]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

theorem comparisonChildren_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    (∑ i, (stateEditCost (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
      target (comparisonChildren source target hM P hP parent q hc i) : ℝ)) ≤
        (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  (Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)).2.2.2.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonPhysical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Active comparison states have precisely the corresponding physical source interval. -/

namespace EditApproximation

theorem comparisonStep_active_parent {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) (i : Fin M)
    (resultParent : TargetInterval source.length) (resultQ : TargetInterval target.length)
    (heq : comparisonStep source target hM P hP node i = some (resultParent, resultQ))
    (hactive : ¬ comparisonStopped source target resultParent resultQ) :
    ∃ parent q, node = some (parent, q) ∧ ¬ comparisonStopped source target parent q ∧
      resultParent = sourceChild parent i := by
  classical
  cases node with
  | none => cases heq
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs] at heq
      split_ifs at heq with hi
      · have hpq := Option.some.inj heq
        have hp : parent = resultParent := congrArg Prod.fst hpq
        have hq : q = resultQ := congrArg Prod.snd hpq
        exact False.elim (hactive (by rw [← hp, ← hq]; exact hs))
    · simp only [comparisonStep, dite_eq_right hs] at heq
      have hpq := Option.some.inj heq
      have hp : sourceChild parent i = resultParent := congrArg Prod.fst hpq
      exact ⟨parent, q, rfl, hs, hp.symm⟩

theorem comparisonFrontier_active_source {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path = some (parent, q))
    (hactive : ¬ comparisonStopped source target parent q) :
    parent = sourceIntervalAt M source.length d path := by
  induction d generalizing parent q with
  | zero =>
    have hpq := Option.some.inj heq
    exact (congrArg Prod.fst hpq).symm
  | succ d ih =>
    obtain ⟨previousParent, previousQ, hprevious, hpreviousActive, hchild⟩ :=
      comparisonStep_active_parent source target hM P hP _ path.2 parent q heq hactive
    have hp := ih path.1 previousParent previousQ hprevious hpreviousActive
    rw [hp] at hchild
    exact hchild

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLift
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual physical tables on the stopped comparison tree. Stopped states retain
their exact cost while the complete-tree representation carries them forward.
-/

namespace EditApproximation

open Finset

theorem stoppedComparisonValue_physical {α : Type*} {M J : ℕ} (source target : List α)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    stoppedComparisonValue source target (fun r => table (node, r))
      (some (physicalSourceInterval source.length node, q)) = table (node, q) := by
  classical
  unfold stoppedComparisonValue
  dsimp only
  split_ifs with hstop
  · exact (hterminal node q hstop).symm
  · rfl

theorem comparisonPhysicalLift_step_active {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ)
    (hterminal : ∀ node q, comparisonStopped source target (physicalSourceInterval source.length node) q →
      table (node, q) = stateEditCost (physicalSource source node) target q)
    (rootQ : TargetInterval target.length) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (hfrontier : comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) node.1.val node.2 =
        some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q)
    (i : Fin M) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    comparisonPhysicalLift source target hM P hP table rootQ (node.1.val + 1) (node.2, i) =
      table (physicalChild node hbelow i,
        comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc i) := by
  classical
  dsimp only
  unfold comparisonPhysicalLift
  rw [dite_eq_left (by omega : node.1.val + 1 ≤ J)]
  change stoppedComparisonValue source target _
    (comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP _ node.1.val node.2) i) = _
  rw [hfrontier]
  simp only [comparisonStep, dite_eq_right hactive]
  exact stoppedComparisonValue_physical source target table hterminal (physicalChild node hbelow i) _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem targetCell_contains {n g : ℕ} {side : ℚ} (hg : 0 < g) (hside : 0 < side)
    (q : TargetInterval n) (hgrid : g ∣ q.lo ∧ g ∣ q.hi) :
    q ∈ cellTargetStates n g side (targetCell side q) := by
  have hcoordinate (p : ℕ) : (⌊(p : ℚ) / side⌋₊ : ℚ) * side ≤ p ∧
      (p : ℚ) < ((⌊(p : ℚ) / side⌋₊ : ℚ) + 1) * side := by
    exact ⟨(le_div_iff₀ hside).mp (Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hside.le)),
      (div_lt_iff₀ hside).mp (Nat.lt_floor_add_one ((p : ℚ) / side))⟩
  exact (cellTargetStates_mem _ hg q).mpr
    ⟨hgrid.1, hgrid.2, (hcoordinate q.lo).1, (hcoordinate q.lo).2,
      (hcoordinate q.hi).1, (hcoordinate q.hi).2⟩



theorem cellRepresentativeStates_contains {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (r : TargetInterval n)
    (hside : 0 < theta * b) (hgrid : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi)
    (heligible : (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b) :
    r ∈ cellRepresentativeStates n P F b a initial theta (targetCell (theta * b) r) := by
  apply List.mem_filter.mpr
  exact ⟨targetCell_contains (by unfold seedGridSpacing; omega) hside r hgrid, decide_eq_true heligible⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBandSpacing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.rationalParametersWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The input-computed dyadic parameters discharge all spacing and basic rounding premises. -/

namespace EditApproximation

theorem computed_theta_dyadic (N : ℕ) :
    (rationalParameters (inputSmallLog N)).theta =
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) := by
  change 1 / (((2 ^ smallLogExponent N : ℕ) : ℚ) ^ 40) = _
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  rw [Nat.mul_comm (smallLogExponent N) 40, one_div]

theorem computed_P_dyadic (N : ℕ) :
    (integerParameters N).P =
      2 ^ (heightExponent N * (coarseExponent (inputSmallLog N) + 20)) := by
  change (2 ^ heightExponent N) ^ (coarseExponent (inputSmallLog N) + 20) = _
  rw [pow_mul]

theorem basic_band_small_constants {ell : ℚ} (hell : 2 ≤ ell) :
    0 < 1 / ell ^ 4 ∧ 0 < 1 / ell ^ 40 ∧ 1 / ell ^ 40 ≤ 1 / 2 ∧
      32 * ell * (1 / ell ^ 40) ≤ 1 ∧ 64 * ell * (1 / ell ^ 40) ≤ 1 := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hcoef : (64 : ℚ) ≤ ell ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hell 6
    norm_num at h
    exact h
  have hpower : (64 : ℚ) ≤ ell ^ 39 :=
    hcoef.trans (pow_le_pow_right₀ hellone (by decide : 6 ≤ 39))
  have hscale : 64 * ell ≤ ell ^ 40 := by
    calc
      64 * ell ≤ ell ^ 39 * ell := mul_le_mul_of_nonneg_right hpower hellpos.le
      _ = ell ^ 40 := (pow_succ ell 39).symm
  have h64 : 64 * ell * (1 / ell ^ 40) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one₀ (pow_pos hellpos 40)).2 hscale
  have h32 : 32 * ell * (1 / ell ^ 40) ≤ 1 := by
    have hnonneg : 0 ≤ ell * (1 / ell ^ 40) := by positivity
    nlinarith only [h64, hnonneg]
  have htheta : 1 / ell ^ 40 ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (pow_pos hellpos 40) (by norm_num : (0 : ℚ) < 2)).2
    have h := pow_le_pow_right₀ hellone (by decide : 1 ≤ 40)
    simp only [pow_one] at h
    linarith only [hell, h]
  exact ⟨by positivity, by positivity, htheta, h32, h64⟩

theorem computed_band_basic_constants (N : ℕ) (hell : 2 ≤ inputSmallLog N) :
    0 < (rationalParameters (inputSmallLog N)).tau ∧
      0 < (rationalParameters (inputSmallLog N)).theta ∧
      (rationalParameters (inputSmallLog N)).theta ≤ 1 / 2 ∧
      (32 * inputSmallLog N : ℚ) * (rationalParameters (inputSmallLog N)).theta ≤ 1 ∧
      (64 * inputSmallLog N : ℚ) * (rationalParameters (inputSmallLog N)).theta ≤ 4 := by
  have h := basic_band_small_constants (show (2 : ℚ) ≤ inputSmallLog N by exact_mod_cast hell)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (by norm_num)⟩

theorem computed_band_spacing_dominates (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    ((integerParameters N).M : ℚ) ≤
      (rationalParameters (inputSmallLog N)).theta * (integerParameters N).P := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by
    have h : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
    exact_mod_cast h
  have hH40 : (inputSmallLog N : ℝ) ^ 40 ≤ inputHeight N :=
    (pow_le_pow_right₀ hellone (by decide : 40 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hH40Q : (inputSmallLog N : ℚ) ^ 40 ≤ inputHeight N := by exact_mod_cast hH40
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMQ : ((integerParameters N).M : ℚ) ≤ inputHeight N := by exact_mod_cast hM
  have hHone : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hPtwo : inputHeight N ^ 2 ≤ (integerParameters N).P :=
    pow_le_pow_right₀ hHone (by omega : 2 ≤ coarseExponent (inputSmallLog N) + 20)
  have hPtwoQ : (inputHeight N : ℚ) ^ 2 ≤ (integerParameters N).P := by exact_mod_cast hPtwo
  have hproduct : ((integerParameters N).M : ℚ) * (inputSmallLog N : ℚ) ^ 40 ≤
      (integerParameters N).P := by
    have h := mul_le_mul hMQ hH40Q (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) 40)
      (Nat.cast_nonneg (inputHeight N))
    exact h.trans (by simpa only [pow_two] using hPtwoQ)
  change ((integerParameters N).M : ℚ) ≤ (1 / (inputSmallLog N : ℚ) ^ 40) * (integerParameters N).P
  rw [one_div_mul_eq_div]
  have hellpos : (0 : ℚ) < inputSmallLog N := by exact_mod_cast (Nat.two_pow_pos (smallLogExponent N))
  apply (le_div_iff₀ (pow_pos hellpos 40)).2
  exact hproduct

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInitial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



theorem physicalInitialTable_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (state : PhysicalEntry M J target.length) :
    max ((stateEditCost (physicalSource source state.1) target state.2 : ℚ) / a)
        |rationalStateGap (physicalSource source state.1) target state.2| ≤
      physicalInitialTable source target U N P F A a state ∧
    physicalInitialTable source target U N P F A a state ≤
      2 * F * stateEditCost (physicalSource source state.1) target state.2 := by
  unfold physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf]
    change max ((stateEditCost _ _ _ : ℚ) / a) |rationalStateGap _ _ _| ≤
        stateEditCost _ _ _ ∧ (stateEditCost _ _ _ : ℚ) ≤ 2 * F * stateEditCost _ _ _
    have hc : (0 : ℚ) ≤ stateEditCost (physicalSource source state.1) target state.2 := Nat.cast_nonneg _
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    have hgap := stateEditCost_length_lower (physicalSource source state.1) target state.2
    rw [← rationalStateGap_cast] at hgap
    constructor
    · apply max_le
      · apply (div_le_iff₀ (by linarith : 0 < a)).2
        nlinarith
      · exact_mod_cast hgap
    · nlinarith
  · rw [localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q))]
    exact globalInitialConeTable_bounds _ _ _ N P F A a hP hF hA ha hfactor
      (fun q => physical_state_cost_le source target N hsize (state.1, q))
      (fun q => hseed (state.1, q)) state.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

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





theorem physicalRefinement_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (t : ℕ) (q : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rw [physicalRefinement]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  split_ifs <;>
    simp only [stageInitial, physicalInitialTable, ite_eq_left hlength,
      shortSourceCost_eq_edit _ _ hlength] <;> rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
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


theorem canonicalRoundedBandAction_congr {ny M : ℕ} (thetaExponent b : ℕ)
    (first second : List (Fin M → TargetInterval ny))
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (initial : Fin M → TargetInterval ny → ℚ) (hequal : first = second) :
    canonicalRoundedBandAction thetaExponent b first hfirst initial =
      canonicalRoundedBandAction thetaExponent b second hsecond initial := by
  subst second
  rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUnskippedComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A comparison action in the physical band passes all literal guards and belongs to its whole cell. -/

namespace EditApproximation

open Finset

theorem representativeList_grid_eligibility {n N P F b : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hrep : (b, r) ∈ representativeList N P F a initial) :
    (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi) ∧
      (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b := by
  obtain ⟨bb, _, hmem⟩ := List.mem_flatMap.mp hrep
  obtain ⟨rr, hrr, heq⟩ := List.mem_map.mp hmem
  have hb : bb = b := congrArg Prod.fst heq
  have hr : rr = r := congrArg Prod.snd heq
  subst bb rr
  have h := of_decide_eq_true (List.mem_filter.mp hrr).2
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem physical_comparison_unskipped {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (b thetaExponent : ℕ) (hb : 0 < b) (hbPower : ∃ e : ℕ, b = 2 ^ e)
    (hPPower : ∃ e : ℕ, P = 2 ^ e) (tau : ℚ) (htau : 0 < tau)
    (htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 / 2)
    (hsmall : (32 * F : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hsmall64 : (64 * F : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 4)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P)
    (r : TargetInterval target.length) (hrep : (b, r) ∈ stageRepresentatives source target U N P F A node)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ representativeBandActions source target (physicalSourceInterval source.length node)
      r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
        (physicalBandChildMassTable source target U N P F A T node hbelow))
    (hcost : (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℚ)) ≤
      4 * b) :
    ∃ member : UnskippedBand source target (physicalSourceInterval source.length node) b P thetaExponent tau F
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow),
      member ∈ cellUnskippedBands source target (physicalSourceInterval source.length node)
        b P F thetaExponent tau (refinementFactor A F)
        (fun s => stageInitial source target U N P F A (node, s))
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow)
        (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) ∧
      member.center = r ∧ comparison ∈ member.actions := by
  let parent := physicalSourceInterval source.length node
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let child := physicalBandChildMassTable source target U N P F A T node hbelow
  let initial := physicalBandChildInitial source target U N P F A node hbelow
  let band := representativeBandActions source target parent r b P tau theta child
  change comparison ∈ band at hcomparison
  have htheta0 : 0 < theta := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hband : band ≠ [] := by
    intro hnil
    have h := hcomparison
    change comparison ∈ band at h
    rw [hnil] at h
    exact List.not_mem_nil h
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [band, representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at hcomparison
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · let velocity := rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hwide child
      let computed := computedBandActions parent r b P tau theta velocity child
      have heq : band = computed := by
        simp only [band, representativeBandActions, dite_eq_right hwide, ite_eq_left hZ, computed, velocity]
      have hc : comparison ∈ computed := heq ▸ hcomparison
      have hcn : computed ≠ [] := by rw [← heq]; exact hband
      have hfactor := refinementFactor_spec A F (by omega)
      have hinitial := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
        hsize hP hF hA hfactor.1 hfactor.2 hseed
      have hgap (i : Fin M) (s : TargetInterval target.length) :
          |rationalStateGap (physicalSource source (physicalChild node hbelow i)) target s| ≤ initial i s := by
        exact (le_max_right _ _).trans (hinitial (physicalChild node hbelow i, s)).1
      have hinonneg (i : Fin M) : 0 ≤ initial i (comparison i) := (abs_nonneg _).trans (hgap i _)
      have hispatial (i : Fin M) (s t : TargetInterval target.length) :
          initial i s ≤ initial i t + (32 * F : ℚ) * targetEndpointDistance s t :=
        physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed (physicalChild node hbelow i) s t
      have hiupper (i : Fin M) : initial i (comparison i) ≤
          2 * F * stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) :=
        (hinitial (physicalChild node hbelow i, comparison i)).2
      have hsumC := bandChildEnvelope_sum_guard source target parent r b P hb hM tau theta velocity
        htau htheta0.le child initial comparison hc (32 * F) F (by positivity)
        (by exact_mod_cast hF) hsmall hinonneg hispatial hiupper hcost
      have hsum : (∑ i, bandChildEnvelope b band initial i) ≤ 64 * F * b := by
        rw [heq]
        exact hsumC
      have hguards := roundedBandAction_guards source target parent r thetaExponent tau velocity child initial
        (computed.head hcn) (List.head_mem hcn) hM (by omega) hbPower hPPower hscale F hsmall64 htheta hgap hsumC
      have hcanonical : canonicalRoundedBandAction thetaExponent b band hband initial =
          roundedBandAction thetaExponent b computed initial (computed.head hcn) :=
        canonicalRoundedBandAction_congr thetaExponent b band computed hband hcn initial heq
      have hwideGuard : canonicalRoundedBandAction thetaExponent b band hband initial ∈ wideActionList M parent r b P := by
        rw [hcanonical]
        exact hguards.1
      have hgapGuard : ∀ i, |rationalStateGap (physicalSource source (physicalChild node hbelow i)) target
          (canonicalRoundedBandAction thetaExponent b band hband initial i)| ≤ 2 * bandChildEnvelope b band initial i := by
        intro i
        rw [hcanonical, heq]
        exact hguards.2 i
      let member : UnskippedBand source target parent b P thetaExponent tau F child initial :=
        ⟨r, hband, hsum, hwideGuard, hgapGuard⟩
      refine ⟨member, ?_, rfl, hcomparison⟩
      apply (unskippedBandList_mem_iff _ member).mpr
      have hgrid := representativeList_grid_eligibility (refinementFactor A F)
        (fun s => stageInitial source target U N P F A (node, s)) r hrep
      exact cellRepresentativeStates_contains _ _ theta r (mul_pos htheta0 (by exact_mod_cast hb)) hgrid.1 hgrid.2
    · simp only [band, representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at hcomparison

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparison
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stage masses and representatives supply the comparison-node warmup hypotheses. -/

namespace EditApproximation

theorem stageRounded_representative_mem {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ stageRepresentatives source target U N P F A node := by
  have hfactor := refinementFactor_spec A F (by omega)
  have hbounds := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed
  exact rounded_comparison_representative (physicalSource source node) target N P F
    (refinementFactor A F) (by omega) (Nat.cast_nonneg _) (by linarith only [hfactor.1])
    (fun r => stageInitial source target U N P F A (node, r))
    (fun r => (le_max_left _ _).trans (hbounds (node, r)).1)
    (fun r => (hbounds (node, r)).2) q hc (physical_state_cost_le source target N hsize (node, q))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalComparisonBand
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Non-bad, low-velocity comparison children belong to an actual unskipped cell band. -/

namespace EditApproximation

open Finset

section Node

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P : ℕ) (A : ℚ)
  (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (q : TargetInterval target.length) (hc : 0 < stateEditCost (physicalSource source node) target q)

local notation "F" => inputSmallLog N
local notation "parent" => physicalSourceInterval source.length node
local notation "b" => (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q) : ℕ)
local notation "r" => roundInterval (seedGridSpacing b P) q
local notation "action" => comparisonChildren source target hM P hP parent q hc
local notation "child" => physicalBandChildMassTable source target U N P F A T node hbelow
local notation "childR" => fun i s => (child i s : ℝ)
local notation "initial" => physicalBandChildInitial source target U N P F A node hbelow
local notation "tau" => RationalParameters.tau (rationalParameters (inputSmallLog N))
local notation "theta" => RationalParameters.theta (rationalParameters (inputSmallLog N))
local notation "thetaExponent" => 40 * smallLogExponent N

include hN hell hMeq hPeq hsize hA hseed hT in
 theorem physicalComparison_unskipped
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (hvelocity : |rationalStateGap (physicalSource source node) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hKsmall : comparisonActionCurvature source target parent r action childR ≤ b / heightQuarterRoot N)
    (hGsmall : comparisonActionMass action childR - wideActionMinimum parent r b P hnonempty childR ≤
      b / heightQuarterRoot N) :
    ∃ member : UnskippedBand source target parent b P thetaExponent tau F child initial,
      member ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau
        (targetCell (theta * b) r) ∧ member.center = r ∧ action ∈ member.actions := by
  have hF : 1 ≤ F := Nat.one_le_two_pow
  have hell2 : 2 ≤ F := by
    have h : 2 ≤ (2 : ℕ) ^ 1000 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
    exact h.trans hell
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hdyadic := cost_dyadicScale _ _ hc le_rfl
  have hcR : (stateEditCost (physicalSource source node) target q : ℝ) ≤ 2 * (b : ℝ) := by
    exact_mod_cast hdyadic.2.2.le
  have hcost := comparisonChildren_cost_bound source target hM P hP parent q hc
  change (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
    (1 + 4 * (M : ℝ) / P) * stateEditCost (physicalSource source node) target q at hcost
  have hcostSum : (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
      4 * b := by
    have h := mul_le_mul_of_nonneg_right hMP
      (Nat.cast_nonneg (α := ℝ) (stateEditCost (physicalSource source node) target q))
    nlinarith only [hcost, hcR, h]
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow
  have hupper (i : Fin M) : (child i (action i) : ℝ) ≤
      2 * F * stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) := by
    dsimp only [physicalBandChildMassTable]
    have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
      (physicalChild node hbelow i, action i)
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (h.2.2.1.trans h.2.2.2)
  have hpositive := (stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale).1
  have hband := computed_comparison_band_mem source target N hN hell hM hMeq parent r action
    hspec.1 hnonempty child (refinementFactor A F : ℝ) ha hlower hupper hcostSum hpositive
    hspec.2.1 hspec.2.2.2.1 hvelocity hKsmall hGsmall
  have hnum := computed_band_basic_constants N hell2
  have hspacing := computed_band_spacing_dominates N hN hell
  rw [← hMeq, ← hPeq, computed_theta_dyadic] at hspacing
  rw [computed_theta_dyadic] at hnum
  have hmember := physical_comparison_unskipped source target hM U N P F A hsize hP hF hA hseed
    T node hbelow b thetaExponent (Nat.two_pow_pos _) ⟨_, rfl⟩
    ⟨_, hPeq.trans (computed_P_dyadic N)⟩ tau hnum.1 hnum.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2 hspacing
    r hrep action (by simpa only [← computed_theta_dyadic, physicalSource] using hband)
    (by exact_mod_cast hcostSum)
  simpa only [physicalNodeCellBands, computed_theta_dyadic] using hmember

end Node

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageParameterBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters for the actual local energy and online inequalities. -/

namespace EditApproximation

theorem refinementFactor_le {A : ℚ} {F : ℕ} (hA : 1 ≤ A) (hF : 1 ≤ F) :
    refinementFactor A F ≤ A := by
  apply max_le hA
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  apply (div_le_iff₀ (by linarith only [hFQ] : (0 : ℚ) < F)).2
  have h := mul_le_mul_of_nonneg_left hFQ (by linarith only [hA] : 0 ≤ A)
  simpa only [mul_one] using h

theorem computed_initialFactor_twice_le_P (N : ℕ) (hN : 0 < N) :
    2 * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  have hH : 2 ≤ H := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (heightExponent_pos N hN)
    simpa only [H, inputHeight, pow_one] using h
  have hHone : 1 ≤ H := by omega
  have hpow : 2 ≤ H ^ 16 := hH.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hHone (by decide : 1 ≤ 16))
  change 2 * H ^ (p + 4) ≤ H ^ (p + 20)
  calc
    2 * H ^ (p + 4) ≤ H ^ (p + 4) * H ^ 16 := by
      simpa only [mul_comm] using Nat.mul_le_mul_left (H ^ (p + 4)) hpow
    _ = H ^ (p + 20) := by
      rw [← pow_add]

theorem computed_refinementFactor_spacing (N : ℕ) (hN : 0 < N) (A : ℚ)
    (hA : 1 ≤ A) (hupper : A ≤ (integerParameters N).initialFactor) :
    2 * (refinementFactor A (inputSmallLog N) : ℝ) ≤ (integerParameters N).P := by
  have hfactor := refinementFactor_le hA (show 1 ≤ inputSmallLog N from Nat.one_le_two_pow)
  have hnum : (2 : ℚ) * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
    exact_mod_cast computed_initialFactor_twice_le_P N hN
  have hQ : (2 : ℚ) * refinementFactor A (inputSmallLog N) ≤ (integerParameters N).P := by
    linarith only [hfactor, hupper, hnum]
  exact_mod_cast hQ

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

/-- The actual dyadic comparison center passes the query filter on every
good initial seed; no local scale premise is assumed. -/
theorem physicalProgramOnlineGuard_comparison
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    physicalProgramOnlineGuard source target U N P F A node q
      (b, roundInterval (seedGridSpacing b P) q) := by
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let a := refinementFactor A F
  let w := stageInitial source target U N P F A (node, q)
  have hfactor := refinementFactor_spec A F (by omega : 0 < F)
  have ha : (0 : ℚ) < a := lt_of_lt_of_le zero_lt_one hfactor.1
  have hFpos : (0 : ℚ) < F := Nat.cast_pos.2 (by omega : 0 < F)
  have hbounds := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed (node, q)
  have hlower : (stateEditCost (physicalSource source node) target q : ℚ) / a ≤ w :=
    (le_max_left _ _).trans hbounds.1
  have hupper : w ≤ 2 * F * stateEditCost (physicalSource source node) target q := hbounds.2
  have hdyadic := cost_dyadicScale _ _ hc le_rfl
  have hblo : (b : ℚ) ≤ stateEditCost (physicalSource source node) target q := by exact_mod_cast hdyadic.2.1
  have hchi : (stateEditCost (physicalSource source node) target q : ℚ) ≤ 2 * b := by exact_mod_cast hdyadic.2.2.le
  have hw : 0 ≤ w := (div_nonneg (Nat.cast_nonneg _) ha.le).trans hlower
  change _ ∧ w / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a * w
  refine ⟨rfl, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 16) hFpos)).2
    have hmul := mul_le_mul_of_nonneg_left hchi (show (0 : ℚ) ≤ 2 * F by positivity)
    have hwb : w ≤ 4 * F * b := by nlinarith only [hupper, hmul]
    have hFb : (0 : ℚ) ≤ F * b := mul_nonneg hFpos.le (Nat.cast_nonneg b)
    nlinarith only [hwb, hFb]
  · have hca : (stateEditCost (physicalSource source node) target q : ℚ) ≤ a * w := by
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hlower
    have haw : (0 : ℚ) ≤ a * w := mul_nonneg ha.le hw
    nlinarith only [hblo, hca, haw]

/-- Every eligible center contributes its whole cell to the actual cell loop. -/
theorem physicalProgramCells_complete (node : PhysicalNode M J) (b : ℕ)
    (r : TargetInterval target.length) (hrep : (b, r) ∈ representatives node) :
    targetCell (theta * b) r ∈ physicalProgramCells source target U N P F A thetaExponent node b := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  refine ⟨(b, r), List.mem_filter.mpr ⟨hrep, by simp⟩, rfl⟩


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageTerminal
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Warmup masses and refinement values equal the true cost at stopped states. -/

namespace EditApproximation

theorem physicalRefinement_at_stopped {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) :
    physicalRefinement source target U N P F A T delta choices node t q =
      stateEditCost (physicalSource source node) target q := by
  rcases hstop with hleaf | hcost
  · exact physicalRefinement_at_leaf source target U N P F A T delta choices node hleaf t q
  · rw [physicalRefinement_zero_cost source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices node t q hcost]
    rw [show stateEditCost (physicalSource source node) target q = 0 from hcost, Nat.cast_zero]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeGeneric
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic cumulative regret at actual comparison-tree slots, including stopped slots. -/

namespace EditApproximation

open Finset

section Tree

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "lifted" => physicalClippedLift source target hM U N P F A hP T delta choices rootQ

include hM hsize hP hF hA hseed hT in
 theorem physicalClippedTable_at_stopped (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hstop : comparisonStopped source target (physicalSourceInterval source.length node) q) (t : ℕ) :
    physicalClippedTable source target U N P F A T delta choices t (node, q) =
      stateEditCost (physicalSource source node) target q := by
  have h := physicalRefinement_at_stopped source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q hstop
  simp only [physicalClippedTable, h, Rat.cast_natCast, max_self]

 theorem physicalComparisonTreeRegret_none (t : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (heq : frontier d.val path = none) :
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = 0 := by
  have hnext (i : Fin M) : frontier (d.val + 1) (path, i) = none := by
    change comparisonStep source target hM P hP (frontier d.val path) i = none
    rw [heq]
    rfl
  simp only [physicalComparisonTreeRegret, physicalClippedLift, comparisonPhysicalLift, heq, hnext,
    stoppedComparisonValue, comparisonMovement, mul_zero, sub_self, sum_const_zero]

 theorem physicalComparisonTreeRegret_stopped (t : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (heq : frontier d.val path = some (parent, q)) (hstop : comparisonStopped source target parent q) :
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t d path = 0 := by
  classical
  have hpoint (i : Fin M) : lifted (t + 1) (d.val + 1) (path, i) =
      if i = ⟨0, hM⟩ then (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) else 0 := by
    unfold physicalClippedLift comparisonPhysicalLift
    change stoppedComparisonValue source target _
      (comparisonStep source target hM P hP (frontier d.val path) i) = _
    rw [heq]
    simp only [comparisonStep, dite_eq_left hstop]
    split_ifs <;> simp only [stoppedComparisonValue, ite_eq_left hstop]
  unfold physicalComparisonTreeRegret
  simp_rw [hpoint]
  simp only [physicalClippedLift, comparisonPhysicalLift, heq, stoppedComparisonValue, ite_eq_left hstop,
    comparisonMovement, mul_zero, sub_zero, sum_ite_eq', mem_univ, ite_true, if_true, sub_self]

include hsize hF hA hseed hT in
 theorem physicalComparisonTreeRegret_active (t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval target.length)
    (heq : frontier node.1.val node.2 = some (physicalSourceInterval source.length node, q))
    (hactive : ¬ comparisonStopped source target (physicalSourceInterval source.length node) q) :
    let hc : 0 < stateEditCost (physicalSource source node) target q := by
      change 0 < stateEditCost (substring source (physicalSourceInterval source.length node).lo
        (physicalSourceInterval source.length node).hi) target q
      unfold comparisonStopped at hactive
      omega
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q
    physicalComparisonTreeRegret source target hM U N P F A hP T delta choices rootQ t ⟨node.1.val, hbelow⟩ node.2 =
      max (stateEditCost (physicalSource source node) target q : ℝ)
        (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
          (128 * (F : ℝ)) * targetEndpointDistance q r -
          physicalComparisonClipped source target U N P F A T delta choices node hbelow
            (comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc) (t + 1) := by
  classical
  dsimp only
  have hnext (i : Fin M) := comparisonPhysicalLift_step_active source target hM P hP
    (physicalClippedTable source target U N P F A T delta choices (t + 1))
    (fun label s hstop => physicalClippedTable_at_stopped source target hM U N P F A hsize hP hF hA hseed
      T hT delta choices label s hstop (t + 1)) rootQ node hbelow q heq hactive i
  have hcurrent : comparisonPhysicalLift source target hM P hP
      (physicalClippedTable source target U N P F A T delta choices (t + 1)) rootQ node.1.val node.2 =
      physicalClippedTable source target U N P F A T delta choices (t + 1) (node, q) := by
    unfold comparisonPhysicalLift
    rw [heq]
    simp only [stoppedComparisonValue, ite_eq_right hactive]
    rw [dite_eq_left (by omega : node.1.val ≤ J)]
  have hmovement : comparisonMovement source target P (frontier node.1.val node.2) =
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)) P) q) := by
    rw [heq]
    simp only [comparisonMovement, ite_eq_right hactive]
    rfl
  unfold physicalComparisonTreeRegret physicalClippedLift
  rw [hcurrent, hmovement]
  simp_rw [hnext]
  rfl

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonPrediction
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual comparison charges and rational velocity predictor at a physical slot. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hP : 66 ≤ P) (T : ℕ) (rootQ : TargetInterval target.length)

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

 theorem stageComparisonPrediction_active (d : Fin J) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length d.val path, q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q)
    (hn : wideActionList M (sourceIntervalAt M source.length d.val path)
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target q)) P ≠ []) :
    stageComparisonPrediction source target hM U N P F A hP T rootQ d path =
      rationalStateGap (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length d.val path).lo
            (sourceIntervalAt M source.length d.val path).hi) target q)) P) q) /
      rationalWideActionMinimum (sourceIntervalAt M source.length d.val path)
        (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
          (substring source (sourceIntervalAt M source.length d.val path).lo
            (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
        (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P hn
        (physicalBandChildMassTable source target U N P F A T
          (⟨⟨d.val, by omega⟩, path⟩ : PhysicalNode M J) d.isLt) := by
  unfold stageComparisonPrediction
  rw [heq]
  simp only [dite_eq_right hactive]

 theorem stageComparisonCharges_active (d : Fin J) (path : TreeLayer M d.val)
    (q : TargetInterval target.length)
    (heq : frontier d.val path = some (sourceIntervalAt M source.length d.val path, q))
    (hactive : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q)
    (hc : 0 < stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
      (sourceIntervalAt M source.length d.val path).hi) target q)
    (hn : wideActionList M (sourceIntervalAt M source.length d.val path)
      (roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost
        (substring source (sourceIntervalAt M source.length d.val path).lo
          (sourceIntervalAt M source.length d.val path).hi) target q)) P) q)
      (2 ^ Nat.log 2 (stateEditCost (substring source (sourceIntervalAt M source.length d.val path).lo
        (sourceIntervalAt M source.length d.val path).hi) target q)) P ≠ []) :
    let parent := sourceIntervalAt M source.length d.val path
    let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
    let r := roundInterval (seedGridSpacing (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (physicalBandChildMassTable source target U N P F A T node d.isLt i s : ℝ)
    stageComparisonCharges source target hM U N P F A hP T rootQ d path =
      (comparisonActionCurvature source target parent r action child,
        comparisonActionMass action child - wideActionMinimum parent r
          (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hn child) := by
  unfold stageComparisonCharges
  rw [heq]
  simp only [dite_eq_right hactive]
  rfl

end Stage

theorem nonbad_charge_bounds (scale ratio K G : ℝ) (hratio : 0 < ratio)
    (hnotbad : ¬ (scale < ratio * K ∨ scale < ratio * G)) :
    K ≤ scale / ratio ∧ G ≤ scale / ratio := by
  have h := not_or.mp hnotbad
  constructor
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.1
  · apply (le_div_iff₀ hratio).2
    simpa only [mul_comm] using le_of_not_gt h.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramComparisonRegret
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selection program supplies the good-node premise of the
comparison-tree expected-regret telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Comparison

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (delta η κ : ℚ) (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * inputSmallLog N : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters (inputSmallLog N)).gamma +
    512 * (128 * inputSmallLog N : ℚ) * inputSmallLog N *
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) ≤ κ * delta)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (rootQ : TargetInterval target.length)

local notation "F" => inputSmallLog N
local notation "thetaExponent" => 40 * smallLogExponent N
local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "hP" => computed_program_grid_lower N P hN hPeq
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "charges" => stageComparisonCharges source target hM U N P F A hP T rootQ
local notation "prediction" => stageComparisonPrediction source target hM U N P F A hP T rootQ
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H (F ^ 80) tau η κ
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H (F ^ 80) tau

include hell hM hMeq hA hAupper hsize hseed hT hHeq hH hdelta hη hκ hκhalf hηrange herror bernstein

/-- Non-bad, low-prediction comparison slots use their literal accepted
representative and whole-cell random coordinates in the global program. -/
theorem physicalProgram_comparison_node_regret_oai (S : ℕ) (d : Fin J) (path : TreeLayer M d.val)
    (hnotbad : ¬ (comparisonActiveScale source target (frontier d.val path) <
      heightQuarterRoot N * (charges d path).1 ∨
      comparisonActiveScale source target (frontier d.val path) < heightQuarterRoot N * (charges d path).2))
    (hvelocity : |prediction d path| ≤ 1 - tau) :
    (∫ draw : Draw, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices draw) rootQ t d path) ∂globalLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * comparisonActiveCost source target (frontier d.val path) := by
  classical
  have hF : 1 ≤ F := Nat.one_le_two_pow
  have hell1764 : 1764 ≤ F := by
    have hlarge : 4096 ≤ (2 : ℕ) ^ 1000 := by
      have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 12 ≤ 1000)
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num] at h
      exact h
    omega
  have hscale : 2 * (refinementFactor A F : ℝ) ≤ P := by
    rw [hPeq]
    exact computed_refinementFactor_spacing N hN A hA hAupper
  have hMP : 4 * (M : ℝ) / P ≤ 1 := by
    rw [hMeq, hPeq]
    exact (computed_stage_grid_bounds N hN).2.2
  generalize heq : frontier d.val path = state at hnotbad ⊢
  cases state with
  | none =>
    have hpoint (draw : Draw) (t : ℕ) := physicalComparisonTreeRegret_none source target hM U N P F A hP T delta
      (choices draw) rootQ t d path heq
    simp_rw [hpoint]
    simp only [sum_const_zero, integral_zero, comparisonActiveCost, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hstop : comparisonStopped source target parent q
    · have hpoint (draw : Draw) (t : ℕ) := physicalComparisonTreeRegret_stopped source target hM U N P F A hP T delta
        (choices draw) rootQ t d path parent q heq hstop
      simp_rw [hpoint]
      simp only [sum_const_zero, integral_zero, comparisonActiveCost, ite_eq_left hstop, mul_zero, le_refl]
    · have hp := comparisonFrontier_active_source source target hM P hP rootQ d.val path parent q heq hstop
      let node : PhysicalNode M J := ⟨⟨d.val, by omega⟩, path⟩
      have hp' : parent = physicalSourceInterval source.length node := hp
      subst parent
      change ¬ comparisonStopped source target (physicalSourceInterval source.length node) q at hstop
      have hc : 0 < stateEditCost (physicalSource source node) target q := by
        change ¬ ((physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 ∨
            stateEditCost (physicalSource source node) target q = 0) at hstop
        omega
      have hleaf : ¬ (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1 := fun h => hstop (Or.inl h)
      let b : ℕ := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
      let r := roundInterval (seedGridSpacing b P) q
      let action := comparisonChildren source target hM P hP (physicalSourceInterval source.length node) q hc
      have hspec := comparisonChildren_spec source target hM P hP (physicalSourceInterval source.length node) q hc
      have hn : wideActionList M (physicalSourceInterval source.length node) r b P ≠ [] := by
        intro hnil
        have hmem := hspec.1
        change action ∈ wideActionList M (physicalSourceInterval source.length node) r b P at hmem
        rw [hnil] at hmem
        exact List.not_mem_nil hmem
      have hcharges := stageComparisonCharges_active source target hM U N P F A hP T rootQ d path q heq hstop hc hn
      have hprediction := stageComparisonPrediction_active source target hM U N P F A hP T rootQ d path q heq hstop hn
      have hratio : 0 < heightQuarterRoot N := by
        unfold heightQuarterRoot
        exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.two_pow_pos _)))
      have hKG := nonbad_charge_bounds _ _ _ _ hratio hnotbad
      change (charges d path).1 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / heightQuarterRoot N ∧
        (charges d path).2 ≤ comparisonActiveScale source target
        (some (physicalSourceInterval source.length node, q)) / heightQuarterRoot N at hKG
      have hscaleEq : comparisonActiveScale source target
          (some (physicalSourceInterval source.length node, q)) = (b : ℝ) := by
        simp only [comparisonActiveScale, ite_eq_right hstop]
        rfl
      rw [hscaleEq, hcharges] at hKG
      rw [hprediction] at hvelocity
      obtain ⟨member, hmember, hcenter, haction⟩ := physicalComparison_unskipped source target hM U N P A hN hell
        hMeq hPeq hsize hP hA hseed T hT node d.isLt q hc hscale hMP hn hvelocity hKG.1 hKG.2
      have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
      obtain ⟨representative, hget⟩ := List.mem_iff_get.mp hrep
      have hget' : (stageRepresentatives source target U N P F A node).get representative = (b, member.center) := by
        simpa only [hcenter] using hget
      have hdyadic := cost_dyadicScale _ N hc (physical_state_cost_le source target N hsize (node, q))
      obtain ⟨scale, hgetScale⟩ := List.mem_iff_get.mp hdyadic.1
      have hcellmem := physicalProgramCells_complete source target U N P F A thetaExponent node b r hrep
      have hmember' : member ∈ physicalNodeCellBands source target U N P F A T node d.isLt b thetaExponent tau
          (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) := by
        simpa only [computed_theta_dyadic, Nat.cast_mul, Nat.cast_ofNat, b, r] using hmember
      have hnonempty : physicalNodeCellBands source target U N P F A T node d.isLt b thetaExponent tau
          (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) ≠ [] := by
        intro he
        rw [he] at hmember'
        exact List.not_mem_nil hmember'
      have hcellmem' : targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * ((dyadicScales N).get scale)) r ∈
          physicalProgramCells source target U N P F A thetaExponent node ((dyadicScales N).get scale) := by
        simpa only [hgetScale, Nat.cast_mul, Nat.cast_ofNat, b] using hcellmem
      obtain ⟨actualCellIndex, hgetActualCell⟩ := List.mem_iff_get.mp hcellmem'
      have htau : 0 < tau := by
        dsimp only [rationalParameters]
        exact div_pos zero_lt_one (pow_pos (Nat.cast_pos.2 (Nat.two_pow_pos _)) 4)
      have hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q := by
        exact_mod_cast hdyadic.2.1
      have hquery : physicalProgramOnlineGuard source target U N P F A node q (b, member.center) := by
        simpa only [hcenter] using physicalProgramOnlineGuard_comparison source target U N P F A
          hsize hP hF hA hseed node q hc
      have hbound := physicalProgram_global_node_regret (R := R) source target N hN hell1764 hM hMeq hPeq rfl
        (Nat.log 2 (stateEditCost (physicalSource source node) target q)) rfl rfl rfl hHeq hH
        U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
        (⟨node, d.isLt⟩ : PhysicalInternalNode M J) hleaf representative scale hgetScale
        (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) actualCellIndex
        (by simpa only [hgetScale] using hgetActualCell) hnonempty member
        hmember' hget' q hb hquery action haction
        htau hηrange herror (bernstein b) S
      have hpoint (draw : Draw) (t : ℕ) :
          physicalComparisonTreeRegret source target hM U N P F A hP T delta (choices draw) rootQ t d path = _ :=
        physicalComparisonTreeRegret_active source target hM U N P F A hsize hP hF hA hseed
          T hT delta (choices draw) rootQ t node d.isLt q heq hstop
      simp_rw [hpoint]
      have hstop' : ¬ comparisonStopped source target (sourceIntervalAt M source.length d.val path) q := hstop
      simpa only [hcenter, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, comparisonActiveCost,
        ite_eq_right hstop', action, physicalSource, physicalSourceInterval, node] using hbound

end Comparison

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgram_comparison_node_regret_oai.{u_1} := @OAI.EditApproximation.physicalProgram_comparison_node_regret_oai.{u_1}

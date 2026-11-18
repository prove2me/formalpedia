-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgram_expected_root_excess
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:27.652196+00:00
-- url     : https://prove2.me/submissions/8ef2b9f5-947d-41fb-8aa1-6fe3c5ebf818

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedRefinementError_lt
import Theorems.Thm_OAI_EditApproximation_physicalComparisonBadRegret_bound
import Theorems.Thm_OAI_EditApproximation_physicalComparisonNearRegret_bound
import Theorems.Thm_OAI_EditApproximation_physicalProgram_comparison_node_regret
import Theorems.Thm_OAI_EditApproximation_physical_tree_expected_excess

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
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

/-- Labeled nodes of a complete `M`-ary tree at one physical depth. -/




theorem tree_layer_sum {M d : ℕ} (weight : TreeLayer M (d + 1) → ℝ) :
    (∑ node : TreeLayer M d, ∑ child : Fin M, weight (node, child)) =
      ∑ node : TreeLayer M (d + 1), weight node := by
  exact (Fintype.sum_prod_type weight).symm

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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem intervalTreeDepth_capacity (M nx : ℕ) (hM : 2 ≤ M) :
    nx ≤ M ^ intervalTreeDepth M nx :=
  (le_max_right 1 nx).trans (Nat.le_pow_clog hM (max 1 nx))

theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
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

theorem comparisonStateCost_nonneg {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonStateCost source target node := by
  cases node with
  | none => exact le_rfl
  | some state => exact Nat.cast_nonneg _

theorem comparisonStep_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (node : ComparisonState source.length target.length) :
    (∑ i, comparisonStateCost source target (comparisonStep source target hM P hP node i)) ≤
      (1 + 4 * (M : ℝ) / P) * comparisonStateCost source target node := by
  classical
  cases node with
  | none => simp only [comparisonStep, comparisonStateCost, sum_const_zero, mul_zero, le_refl]
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonStep, dite_eq_left hs]
      have hsum : (∑ i : Fin M, comparisonStateCost source target
          (if i = ⟨0, hM⟩ then some (parent, q) else none)) =
          comparisonStateCost source target (some (parent, q)) := by
        have hpoint (i : Fin M) : comparisonStateCost source target
            (if i = ⟨0, hM⟩ then some (parent, q) else none) =
            if i = ⟨0, hM⟩ then comparisonStateCost source target (some (parent, q)) else 0 := by
          split_ifs <;> rfl
        simp_rw [hpoint]
        simp
      rw [hsum]
      have hnonneg := comparisonStateCost_nonneg source target (some (parent, q))
      have hf : 0 ≤ 4 * (M : ℝ) / P := by positivity
      nlinarith
    · simpa only [comparisonStep, dite_eq_right hs, comparisonStateCost] using
        comparisonChildren_cost_bound source target hM P hP parent q
          (by unfold comparisonStopped at hs; omega)

theorem comparison_frontier_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (d : ℕ) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        (1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root := by
  induction d with
  | zero =>
    change (∑ _ : PUnit, comparisonStateCost source target root) ≤ _
    simp
  | succ d ih =>
    rw [← tree_layer_sum]
    have hsum := sum_le_sum (fun node (_ : node ∈ (univ : Finset (TreeLayer M d))) =>
      comparisonStep_cost_bound source target hM P hP
        (comparisonFrontier source target hM P hP root d node))
    have hf : 0 ≤ 1 + 4 * (M : ℝ) / P := by positivity
    calc
      _ ≤ ∑ node : TreeLayer M d, (1 + 4 * (M : ℝ) / P) *
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := hsum
      _ = (1 + 4 * (M : ℝ) / P) * ∑ node : TreeLayer M d,
          comparisonStateCost source target
            (comparisonFrontier source target hM P hP root d node) := by rw [mul_sum]
      _ ≤ (1 + 4 * (M : ℝ) / P) *
          ((1 + 4 * (M : ℝ) / P) ^ d * comparisonStateCost source target root) :=
            mul_le_mul_of_nonneg_left ih hf
      _ = _ := by rw [pow_succ]; ring

theorem comparison_frontier_cost_le_twice {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J d : ℕ) (hd : d ≤ J)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ node : TreeLayer M d, comparisonStateCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * comparisonStateCost source target root := by
  have hx : 0 ≤ 4 * (M : ℝ) / P := by positivity
  have hdR : (d : ℝ) ≤ J := by exact_mod_cast hd
  have hdx : (d : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hdR hx).trans hsmall
  have hpow := small_growth_pow d hx hdx
  have htwo : (1 + 4 * (M : ℝ) / P) ^ d ≤ 2 := by linarith
  exact (comparison_frontier_cost_bound source target hM P hP root d).trans
    (mul_le_mul_of_nonneg_right htwo (comparisonStateCost_nonneg source target root))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual terminal, nonterminal-cost and endpoint-movement bounds. -/

namespace EditApproximation

open Finset

theorem comparisonActiveCost_bounds {α : Type*} (source target : List α)
    (node : ComparisonState source.length target.length) :
    0 ≤ comparisonActiveCost source target node ∧
      comparisonActiveCost source target node ≤ comparisonStateCost source target node := by
  classical
  cases node with
  | none => exact ⟨le_rfl, le_rfl⟩
  | some state =>
    rcases state with ⟨parent, q⟩
    by_cases hs : comparisonStopped source target parent q
    · simp only [comparisonActiveCost, ite_eq_left hs, comparisonStateCost]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
    · simp only [comparisonActiveCost, ite_eq_right hs, comparisonStateCost]
      exact ⟨Nat.cast_nonneg _, le_rfl⟩

theorem comparison_total_active_cost_bound {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) (J : ℕ)
    (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2) :
    (∑ d ∈ range J, ∑ node : TreeLayer M d, comparisonActiveCost source target
      (comparisonFrontier source target hM P hP root d node)) ≤
        2 * J * comparisonStateCost source target root := by
  have hlevel (d : ℕ) (hd : d ∈ range J) :
      (∑ node : TreeLayer M d, comparisonActiveCost source target
        (comparisonFrontier source target hM P hP root d node)) ≤
          2 * comparisonStateCost source target root := by
    exact (sum_le_sum (fun node _ => (comparisonActiveCost_bounds source target _).2)).trans
      (comparison_frontier_cost_le_twice source target hM P hP root J d (mem_range.mp hd).le hsmall)
  have hsum := sum_le_sum hlevel
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_assoc, mul_left_comm] using hsum

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSmallConstants
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed small parameters satisfy the group and online error inequalities. -/

namespace EditApproximation

theorem group_online_range_small {ell : ℚ} (hell : 8 ≤ ell) :
    8 * (128 * ell) * (1 / ell ^ 40) ≤ 1 / ell ^ 10 := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef : (1024 : ℚ) ≤ ell ^ 29 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 4
    norm_num at h
    exact (by norm_num : (1024 : ℚ) ≤ 4096) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 4 ≤ 29)))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos he0 40) (pow_pos he0 10)).2
  have h := mul_le_mul_of_nonneg_right hcoef (pow_nonneg he0.le 11)
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem group_online_eta_range {ell : ℚ} (hell : 3 ≤ ell) :
    ell ^ 5 * (3 * (1 / ell ^ 10)) ≤ 1 / ell ^ 4 := by
  have he0 : 0 < ell := by linarith only [hell]
  have h := mul_le_mul_of_nonneg_right hell (pow_nonneg he0.le 9)
  have hmul : ell ^ 5 * (3 * (1 / ell ^ 10)) = 3 * ell ^ 5 / ell ^ 10 := by ring
  rw [hmul]
  apply (div_le_div_iff₀ (pow_pos he0 10) (pow_pos he0 4)).2
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem group_rounded_error_small {ell : ℚ} (hell : 8 ≤ ell) :
    2 * (1 / ell ^ 20) + 512 * (128 * ell) * ell * (1 / ell ^ 40) ≤
      (1 / ell ^ 4) * (1 / ell ^ 10) := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef1 : (4 : ℚ) ≤ ell ^ 6 := by
    exact (by norm_num : (4 : ℚ) ≤ 8).trans
      (hell.trans (by simpa only [pow_one] using pow_le_pow_right₀ he (by decide : 1 ≤ 6)))
  have hcoef2 : (131072 : ℚ) ≤ ell ^ 24 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 6
    norm_num at h
    exact (by norm_num : (131072 : ℚ) ≤ 262144) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 6 ≤ 24)))
  have hfirst : 2 / ell ^ 20 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 20) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef1 (pow_nonneg he0.le 14)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have hsecond : 65536 * ell ^ 2 / ell ^ 40 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 40) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef2 (pow_nonneg he0.le 16)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have hid : (1 / ell ^ 4) * (1 / ell ^ 10) = 2 * (1 / (2 * ell ^ 14)) := by
    field_simp
  rw [hid]
  have hid2 : 512 * (128 * ell) * ell * (1 / ell ^ 40) = 65536 * ell ^ 2 / ell ^ 40 := by ring
  rw [hid2]
  have hid1 : 2 * (1 / ell ^ 20) = 2 / ell ^ 20 := by ring
  rw [hid1]
  simpa only [two_mul] using add_le_add hfirst hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBandSpacing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageParameterBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.rationalParametersWithWork_value
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

theorem computed_online_range (ell : ℕ) (hell : 8 ≤ ell) :
    0 < (rationalParameters ell).eta ∧ 0 ≤ (rationalParameters ell).kappa ∧
      (rationalParameters ell).kappa ≤ 1 / 2 ∧
      ((rationalParameters ell).eta : ℝ) *
        (2 * ((rationalParameters ell).delta : ℝ) +
          8 * (128 * (ell : ℝ)) * ((rationalParameters ell).theta : ℝ)) ≤
        ((rationalParameters ell).kappa : ℝ) := by
  have hellQ : (8 : ℚ) ≤ ell := by exact_mod_cast hell
  have he0 : (0 : ℚ) < ell := by linarith only [hellQ]
  have hpow : (2 : ℚ) ≤ (ell : ℚ) ^ 4 := by
    exact (by linarith only [hellQ] : (2 : ℚ) ≤ ell).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hellQ] : (1 : ℚ) ≤ ell)
        (by decide : 1 ≤ 4))
  have hhalf : (1 : ℚ) / (ell : ℚ) ^ 4 ≤ 1 / 2 := by
    exact (div_le_div_iff₀ (pow_pos he0 4) (by norm_num : (0 : ℚ) < 2)).2 (by simpa using hpow)
  have hrange := group_online_range_small hellQ
  have heta := group_online_eta_range (by linarith only [hellQ] : (3 : ℚ) ≤ ell)
  have h := mul_le_mul_of_nonneg_left hrange (pow_nonneg he0.le 5)
  have hQ : (ell : ℚ) ^ 5 * (2 * (1 / (ell : ℚ) ^ 10) +
      8 * (128 * ell) * (1 / (ell : ℚ) ^ 40)) ≤ 1 / (ell : ℚ) ^ 4 := by
    linarith only [h, heta]
  refine ⟨pow_pos he0 5, (by positivity : (0 : ℚ) ≤ 1 / (ell : ℚ) ^ 4), hhalf, ?_⟩
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  simpa only [rationalParameters, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] using hR

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_tree_small (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    (intervalTreeDepth (integerParameters N).M nx : ℝ) *
      (4 * ((integerParameters N).M : ℝ) / (integerParameters N).P) ≤ 1 / 2 := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let J := intervalTreeDepth M nx
  have hdepth := computed_tree_depth_bound N nx hN hnx hell
  have hellone : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hJ : J ≤ 100 * H := by
    calc
      J = J * 1 := (Nat.mul_one J).symm
      _ ≤ J * inputSmallLog N := Nat.mul_le_mul_left J hellone
      _ ≤ 100 * H := hdepth
  have hJR : (J : ℝ) ≤ 100 * H := by exact_mod_cast hJ
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMR : (M : ℝ) ≤ H := by exact_mod_cast hM
  have hP800 := (computed_stage_grid_bounds N hN).2.1
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P from lt_of_lt_of_le (by decide) (computed_stage_grid_bounds N hN).1)
  have hproduct := mul_le_mul hJR hMR (Nat.cast_nonneg M) (by positivity : (0 : ℝ) ≤ 100 * H)
  change (J : ℝ) * (4 * (M : ℝ) / P) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hPr).2
  nlinarith only [hproduct, hP800]

 theorem computed_stage_positive_counts (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    0 < (integerParameters N).T ∧ 0 < (integerParameters N).S := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpow := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hpowN : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpow
  have hellpos : 0 < inputSmallLog N := Nat.two_pow_pos _
  exact ⟨Nat.two_pow_pos _, Nat.div_pos hpowN (pow_pos hellpos 2)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonCharges
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature and discrepancy are computed from the actual comparison-tree warmup masses. -/

namespace EditApproximation

open Finset

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (rootQ : TargetInterval target.length)

theorem treeLayer_sigma_sum (M J : ℕ) (f : (d : ℕ) → TreeLayer M d → ℝ) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val), f v.1.val v.2) =
      ∑ d ∈ range J, ∑ path : TreeLayer M d, f d path := by
  rw [Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun d => ∑ path : TreeLayer M d, f d path) J

end Stage

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalTreeBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the three actual comparison-node classes in the expected telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem finite_three_region_budget {ι : Type*} [Fintype ι]
    (cost regret : ι → ℝ) (bad near : ι → Prop) [DecidablePred bad] [DecidablePred near]
    (badBudget nearBudget coefficient costBudget : ℝ)
    (hbad : (∑ i with bad i, regret i) ≤ badBudget)
    (hnear : (∑ i with ¬ bad i ∧ near i, regret i) ≤ nearBudget)
    (hgood : ∀ i, ¬ bad i → ¬ near i → regret i ≤ coefficient * cost i)
    (hcoef : 0 ≤ coefficient) (hcost : ∀ i, 0 ≤ cost i)
    (htotal : (∑ i, cost i) ≤ costBudget) :
    (∑ i, regret i) ≤ badBudget + nearBudget + coefficient * costBudget := by
  classical
  have hsplit : (∑ i, regret i) = (∑ i with bad i, regret i) +
      (∑ i with ¬ bad i ∧ near i, regret i) +
      (∑ i with ¬ bad i ∧ ¬ near i, regret i) := by
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hb : bad i <;> by_cases hn : near i <;> simp only [hb, hn, not_true_eq_false,
      not_false_eq_true, and_false, and_true, ite_true, if_true, ite_false, if_false, add_zero, zero_add]
  have hgoodSum : (∑ i with ¬ bad i ∧ ¬ near i, regret i) ≤ coefficient * costBudget := by
    apply (sum_le_sum (fun i hi => hgood i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2)).trans
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hcoef
    apply le_trans _ htotal
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hcost i)
  rw [hsplit]
  linarith only [hbad, hnear, hgoodSum]

section Tree

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))
local notation "charges" => stageComparisonCharges source target hM U N P F A hP T rootQ
local notation "prediction" => stageComparisonPrediction source target hM U N P F A hP T rootQ
local notation "D" => comparisonStateCost source target
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physical_comparison_expected_regret_sum (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin J) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∑ v : (Σ d : Fin J, TreeLayer M d.val),
      ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t v.1 v.2) ∂μ) ≤
      (40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
        2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) * D := by
  classical
  let cost := fun (v : Σ d : Fin J, TreeLayer M d.val) => comparisonActiveCost source target (frontier v.1.val v.2)
  let regret := fun (v : Σ d : Fin J, TreeLayer M d.val) =>
    ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) rootQ t v.1 v.2) ∂μ
  let bad := fun (v : Σ d : Fin J, TreeLayer M d.val) =>
    comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).1 ∨
      comparisonActiveScale source target (frontier v.1.val v.2) < ratio * (charges v.1 v.2).2
  let near := fun (v : Σ d : Fin J, TreeLayer M d.val) => 1 - tau < |prediction v.1 v.2|
  have hbad : (∑ v with bad v, regret v) ≤
      40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      physicalComparisonBadRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) rootQ ratio hratio.le hscale hMP hcapacity hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hnear : (∑ v with ¬ bad v ∧ near v, regret v) ≤
      2 * J * (1 / ratio + 4 * (tau : ℝ) * F) * D := by
    rw [← integral_finsetSum _ (by intro v hv; exact .of_finite)]
    have h := integral_mono (μ := μ) (.of_finite) (integrable_const _) (fun ω =>
      physicalComparisonNearRegret_bound source target hM U N P F A hsize hP hF hA hseed
        T hT delta (choices ω) rootQ ratio hratio tau htau hscale hMP hsmall S)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hcost : (∑ v, cost v) ≤ 2 * J * D := by
    have heq := treeLayer_sigma_sum M J (fun (d : ℕ) (path : TreeLayer M d) =>
      comparisonActiveCost source target (frontier d path))
    exact heq.le.trans (comparison_total_active_cost_bound source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) J hsmall)
  have h := finite_three_region_budget cost regret bad near _ _ coefficient (2 * J * D)
    hbad hnear (fun v hb hn => hgood v.1 v.2 hb (le_of_not_gt hn)) hcoef
    (fun v => (comparisonActiveCost_bounds source target _).1) hcost
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

include hsize hF hA hseed hT in
 theorem physical_tree_expected_excess_of_good_nodes (ratio : ℝ) (hratio : 0 < ratio)
    (tau : ℚ) (htau : 0 ≤ tau)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (S : ℕ) (hS : 0 < S) (coefficient : ℝ) (hcoef : 0 ≤ coefficient)
    (hgood : ∀ (d : Fin J) (path : TreeLayer M d.val),
      ¬ (comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).1 ∨
        comparisonActiveScale source target (frontier d.val path) < ratio * (charges d path).2) →
      |prediction d path| ≤ 1 - tau →
      (∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
        (choices ω) rootQ t d path) ∂μ) ≤ coefficient * comparisonActiveCost source target (frontier d.val path)) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω)
        (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ : ℝ) -
      stateEditCost source target rootQ) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * J / P +
        (40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
          2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) / S) *
        stateEditCost source target rootQ := by
  classical
  let budget := fun (d : ℕ) (path : TreeLayer M d) => if hd : d < J then
    ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
      (choices ω) rootQ t ⟨d, hd⟩ path) ∂μ else 0
  have hnode (d : ℕ) (hd : d < J) (path : TreeLayer M d) :
      (∫ ω, (∑ t ∈ range S,
        (physicalClippedLift source target hM U N P F A hP T delta (choices ω) rootQ (t + 1) d path -
          (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, physicalClippedLift source target hM U N P F A hP T delta
            (choices ω) rootQ (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path := by
    simp only [budget, dite_eq_left hd, physicalComparisonTreeRegret, le_refl]
  have htelescope := physical_tree_expected_excess source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices rootQ μ S hS hcapacity hsmall budget hnode
  have hsum := physical_comparison_expected_regret_sum source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices rootQ μ ratio hratio tau htau hscale hMP hcapacity hsmall S coefficient hcoef hgood
  have heq : (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) =
      ∑ v : (Σ d : Fin J, TreeLayer M d.val),
        ∫ ω, (∑ t ∈ range S, physicalComparisonTreeRegret source target hM U N P F A hP T delta
          (choices ω) rootQ t v.1 v.2) ∂μ := by
    rw [← treeLayer_sigma_sum M J budget]
    apply sum_congr rfl
    intro v _
    simp only [budget, dite_eq_left v.1.isLt]
  rw [heq] at htelescope
  have hroot : D = (stateEditCost source target rootQ : ℝ) := by
    simp only [comparisonStateCost, sourceIntervalAt, substring, List.take_length, List.drop_zero]
  rw [hroot] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) S)
  calc
    _ ≤ _ := htelescope
    _ ≤ ((8 * (M : ℝ) + 512 * F) * J / P) * stateEditCost source target rootQ +
        ((40000 * ratio * (F : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
          2 * J * (1 / ratio + 4 * (tau : ℝ) * F + coefficient)) *
            stateEditCost source target rootQ) / S := add_le_add_right hdiv _
    _ = _ := by ring

end Tree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramAccuracy
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected root-excess accuracy of the finite selection program under finite Bernstein bounds. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem physicalProgramNodeCoefficient_nonneg (N F S H : ℕ) (eta kappa delta : ℚ)
    (heta : (0 : ℝ) ≤ eta) (hkappa : (0 : ℝ) ≤ kappa) (hdelta : (0 : ℝ) ≤ delta) :
    0 ≤ physicalProgramNodeCoefficient N F eta kappa delta S H := by
  unfold physicalProgramNodeCoefficient
  positivity

section Accuracy

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T S : ℕ) (hTeq : T = (integerParameters N).T) (hSeq : S = (integerParameters N).S)
  (hHeq : H = inputHeight N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (rootQ : TargetInterval target.length)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein

/-- A pass of the actual rational recurrence has expected positive root
error at most the actual edit cost divided by the computed small logarithm. -/
theorem physicalProgram_expected_root_excess_oai :
    (∫ draw : Draw, max ((physicalRefinement source target U N P ell A T delta (choices draw)
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ : ℝ) -
        stateEditCost source target rootQ) 0 ∂globalLaw) ≤
      (1 / (ell : ℝ)) * stateEditCost source target rootQ := by
  classical
  have hell1764 : 1764 ≤ ell := by
    have hlarge : 4096 ≤ (2 : ℕ) ^ 1000 := by
      have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 12 ≤ 1000)
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num] at h
      exact h
    omega
  have hell200 : 200 ≤ ell := by omega
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hEllQ : (8 : ℚ) ≤ ell := by exact_mod_cast (show 8 ≤ ell by omega)
  have hEllPos : (0 : ℚ) < ell := Nat.cast_pos.2 (Nat.two_pow_pos _)
  have hbranch : 2 ≤ M := by
    rw [hMeq]
    exact (computed_branching_bounds N hN hell200).1
  have hM : 0 < M := by omega
  have hP := computed_program_grid_lower N P hN hPeq
  have hcounts := computed_stage_positive_counts N hN hell
  have hT : 0 < T := by rw [hTeq]; exact hcounts.1
  have hS : 0 < S := by rw [hSeq]; exact hcounts.2
  have hpoly : ell ^ 20000 ≤ inputHeight N := by exact_mod_cast inputHeight_polynomial_slack N hN hell
  have hEllHeight : ell ≤ inputHeight N := by
    have hpow : ell ≤ ell ^ 20000 := by
      simpa only [pow_one] using pow_le_pow_right₀ hF (by decide : 1 ≤ 20000)
    exact hpow.trans hpoly
  have hH : 4 ≤ H := by rw [hHeq]; omega
  have hrange := computed_online_range ell (by omega : 8 ≤ ell)
  have hdelta : 0 < delta := div_pos zero_lt_one (pow_pos hEllPos 10)
  have htau : 0 ≤ tau := (div_pos zero_lt_one (pow_pos hEllPos 4)).le
  have hηrange : (eta : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * ell : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (kappa : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, computed_theta_dyadic,
      Rat.cast_zpow] using hrange.2.2.2
  have herror : 2 * (rationalParameters ell).gamma + 512 * (128 * ell : ℚ) * ell *
      (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ kappa * delta := by
    simpa only [← computed_theta_dyadic, rationalParameters] using group_rounded_error_small hEllQ
  have hscale : 2 * (refinementFactor A ell : ℝ) ≤ P := by
    rw [hPeq]
    exact computed_refinementFactor_spacing N hN A hA hAupper
  have hMP : 4 * (M : ℝ) / P ≤ 1 := by
    rw [hMeq, hPeq]
    exact (computed_stage_grid_bounds N hN).2.2
  have hcapacity : source.length ≤ M ^ J := by
    rw [hJeq]
    exact intervalTreeDepth_capacity M source.length hbranch
  have hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 := by
    rw [hJeq, hMeq, hPeq]
    exact computed_stage_tree_small N source.length hN (by omega) hell200
  have hratio : 0 < heightQuarterRoot N := by
    unfold heightQuarterRoot
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.two_pow_pos _)))
  have hηR : (0 : ℝ) < eta := (Rat.cast_pos (K := ℝ)).mpr hrange.1
  have hκR : (0 : ℝ) ≤ kappa := (Rat.cast_nonneg (K := ℝ)).mpr hrange.2.1
  have hdeltaR : (0 : ℝ) < delta := (Rat.cast_pos (K := ℝ)).mpr hdelta
  have hcoef := physicalProgramNodeCoefficient_nonneg N ell S H eta kappa delta hηR.le hκR hdeltaR.le
  have hgood := fun (d : Fin J) (path : TreeLayer M d.val) =>
    physicalProgram_comparison_node_regret (R := R) source target N hN hell hM hMeq U P hPeq A hA hAupper
      hsize hseed T hT hHeq hH delta eta kappa hdelta hrange.1 hrange.2.1 hrange.2.2.1
      hηrange herror bernstein rootQ S d path
  have hbound := physical_tree_expected_excess_of_good_nodes source target hM U N P ell A
    hsize hP hF hA hseed T hT delta choices rootQ globalLaw (heightQuarterRoot N) hratio tau htau
    hscale hMP hcapacity hsmall S hS (physicalProgramNodeCoefficient N ell eta kappa delta S H) hcoef hgood
  have hbudget : ((8 * (M : ℝ) + 512 * ell) * J / P +
      (40000 * heightQuarterRoot N * (ell : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
        2 * J * (1 / heightQuarterRoot N + 4 * (tau : ℝ) * ell +
          physicalProgramNodeCoefficient N ell eta kappa delta S H)) / S) =
        computedRefinementError N source.length := by
    dsimp only [physicalProgramNodeCoefficient, computedRefinementError]
    rw [hJeq, hMeq, hPeq, hTeq, hSeq, hHeq]
    simp only [rationalParameters, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_ofNat]
  rw [hbudget] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (computedRefinementError_lt N source.length hN (by omega) hell).le (Nat.cast_nonneg _))

end Accuracy

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgram_expected_root_excess_oai.{u_1} := @OAI.EditApproximation.physicalProgram_expected_root_excess_oai.{u_1}

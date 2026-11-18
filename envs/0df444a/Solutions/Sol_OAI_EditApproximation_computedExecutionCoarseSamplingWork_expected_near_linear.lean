-- Prove2me | solution 1 for OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:59.781406+00:00
-- url     : https://prove2.me/submissions/46c69da1-8695-4bdd-ae26-aad16eca2a54

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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedPhysicalCoarseWork_expected_le
import Theorems.Thm_OAI_EditApproximation_weighted_dependency_div_height_tendsto

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_maximal (ell p : ℕ) (hp : p ^ 4 ≤ Nat.log 2 ell) :
    p ≤ coarseExponent ell := by
  apply Nat.le_sqrt'.2
  apply Nat.le_sqrt'.2
  simpa only [← pow_mul] using hp

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem twice_square_le_two_pow (r : ℕ) (hr : 8 ≤ r) : 2 * r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith

theorem computed_coarse_B_upper (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    (integerParameters N).B ≤ 2 ^ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  have hp : coarseExponent (inputSmallLog N) ≤ 2 * heightExponent N := by
    have hsqrt := (Nat.sqrt_le_self (Nat.sqrt (Nat.log 2 (inputSmallLog N)))).trans
      (Nat.sqrt_le_self (Nat.log 2 (inputSmallLog N)))
    exact hsqrt.trans ((Nat.log_le_self _ _).trans (by omega))
  have hpoly := twice_square_le_two_pow (heightExponent N) hr
  have hexponent : heightExponent N * coarseExponent (inputSmallLog N) ≤ inputHeight N := by
    have hmul := Nat.mul_le_mul_left (heightExponent N) hp
    change _ ≤ 2 ^ heightExponent N
    nlinarith
  change (2 ^ heightExponent N) ^ coarseExponent (inputSmallLog N) ≤ 2 ^ inputHeight N
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hexponent

theorem computed_coarse_height_large (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    256 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  change 2 ^ 8 ≤ 2 ^ heightExponent N
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hr

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Expected array work of the actual dyadic initial estimator

These are expectations of the concrete pruning-stopped counters. The
linear penalty sweeps and representation bounds separately convert the
array units into arithmetic and RAM work.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

theorem coarseInverseAllowanceFactor_log_bound (B : ℕ) (Q lam : ℚ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) :
    coarseInverseAllowanceFactor B Q lam ≤ (Q : ℝ) / lam * (1 + Real.log B) := by
  have hharmonic : (∑ r ∈ Icc 1 B, (1 : ℝ) / r) = harmonic B := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  unfold coarseInverseAllowanceFactor
  rw [hharmonic]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log B)
    (div_nonneg (by exact_mod_cast hQ) (by exact_mod_cast hlam))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseLabelWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.coarseInitialMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Only expanded internal nodes request their child thresholds. The full
product seed is a specification; labels below a pruned node are never read. -/




private theorem coarseLabelChildren_le {B d : ℕ} {α : Type*} (Q lam allowance : ℚ)
    (labels arrays : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hle : ∀ child draw below, (child, draw, below) ∈ children → ∀ a, labels child below a ≤ arrays child below a) :
    coarseLabelChildren Q lam allowance labels children ≤
      coarseActiveChildrenWork Q lam allowance arrays children := by
  induction children with
  | nil => exact le_rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact Nat.add_le_add (hle child draw below List.mem_cons_self _)
      (ih (fun child draw below hmem => hle child draw below (List.mem_cons_of_mem _ hmem)))

 theorem coarseLabelCount_le_arrayWork {B d : ℕ} {α : Type*} (k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : ℚ) :
    coarseLabelCount Q lam tree draws allowance ≤ coarseActiveArrayWork k Q lam tree draws allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs <;> omega
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs
    · exact le_rfl
    · have hc := coarseLabelChildren_le Q lam allowance
        (fun child => coarseLabelCount Q lam child)
        (fun child => coarseActiveArrayWork k Q lam child)
        (List.ofFn fun i => (children i, draws i, below i)) (by
          intro child draw childBelow hmem a
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) a)
      have hunit : B ≤ B * (2 * k + 1) := by nlinarith
      exact Nat.add_le_add hunit hc

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialLabels
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Only labels in roots actually reached by the dyadic initializer are drawn. -/


theorem coarseInitialLabelCount_le_arrayWork {α : Type*} [DecidableEq α]
    (B d : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseInitialLabelCount B d Q lam x y draws ≤ coarseInitialArrayWork B d Q lam x y draws := by
  unfold coarseInitialLabelCount coarseInitialArrayWork
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact Finset.sum_le_sum (fun i _ => coarseLabelCount_le_arrayWork
      (coarseGuess (coarseEntryWidth x y) i) Q lam (coarseEntryTree B d x y) (draws i) _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

theorem smallLogExponent_tendsto : Tendsto smallLogExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ b))]
    with N hN
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hN

theorem inputSmallLog_log_two (N : ℕ) :
    Nat.log 2 (inputSmallLog N) = smallLogExponent N := by
  exact Nat.log_pow (by decide : 1 < (2 : ℕ)) _

theorem coarseExponent_tendsto :
    Tendsto (fun N => coarseExponent (inputSmallLog N)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [smallLogExponent_tendsto.eventually (eventually_ge_atTop (b ^ 4))]
    with N hN
  exact coarseExponent_maximal _ b ((inputSmallLog_log_two N).symm ▸ hN)

theorem inputSmallLog_real_tendsto :
    Tendsto (fun N => (inputSmallLog N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp inputSmallLog_tendsto

theorem coarseExponent_real_tendsto :
    Tendsto (fun N => (coarseExponent (inputSmallLog N) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp coarseExponent_tendsto

theorem log_smallLog_div_smallLog_tendsto :
    Tendsto (fun N => Real.log (inputSmallLog N : ℝ) / inputSmallLog N) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputSmallLog_real_tendsto

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem inputHeight_real_tendsto :
    Tendsto (fun N => (inputHeight N : ℝ)) atTop atTop := by
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp heightExponent_tendsto

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

theorem inputHeight_real_log (N : ℕ) :
    Real.log (inputHeight N : ℝ) = (heightExponent N : ℝ) * Real.log 2 := by
  simp only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem encoding_exponent_div_height_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      Real.log (inputHeight N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (2 * Real.log 2)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have he : (heightExponent N : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast (inputSmallLog_bounds N hN).1
  have hprod := mul_le_mul hq he (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hlog := mul_le_mul_of_nonneg_right hprod (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [inputHeight_real_log]
  have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (inputHeight N))
  first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

theorem height_log_sandwich (N : ℕ) (hN : 0 < N) :
    Real.log (N + 2 : ℝ) / Real.log 2 ≤ inputHeight N ∧
      (inputHeight N : ℝ) ≤ (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcover : (N + 2 : ℝ) ≤ (2 : ℝ) ^ inputHeight N := by
    exact_mod_cast inputHeight_covers_length N
  have hlower := Real.log_le_log (by positivity : (0 : ℝ) < N + 2) hcover
  rw [Real.log_pow] at hlower
  have hL : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ))
    (by omega : 1 < N + 2)
  have hpredR : (2 : ℝ) ^ (Nat.clog 2 (N + 2)).pred < N + 2 := by exact_mod_cast hpred
  have hpredlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 (N + 2)).pred) hpredR
  rw [Real.log_pow] at hpredlog
  have hpredcast : ((Nat.clog 2 (N + 2)).pred : ℝ) = (Nat.clog 2 (N + 2) : ℝ) - 1 := by
    have hnat : (Nat.clog 2 (N + 2)).pred + 1 = Nat.clog 2 (N + 2) :=
      Nat.succ_pred_eq_of_pos (by omega)
    have hcast : ((Nat.clog 2 (N + 2)).pred : ℝ) + 1 = (Nat.clog 2 (N + 2) : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hpredcast] at hpredlog
  have hH : (inputHeight N : ℝ) < 2 * (Nat.clog 2 (N + 2) : ℝ) := by
    have h := (rejectionWord_range (Nat.clog 2 (N + 2)) (by omega)).2
    simpa only [inputHeight, heightExponent, rejectionBitCount, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_lt.mpr h :
      ((2 ^ rejectionBitCount (Nat.clog 2 (N + 2)) : ℕ) : ℝ) <
        ((2 * Nat.clog 2 (N + 2) : ℕ) : ℝ))
  have hlogN : Real.log 2 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N + 2))
  constructor
  · exact (div_le_iff₀ hlogtwo).2 hlower
  · have hproduct : (inputHeight N : ℝ) * Real.log 2 ≤ 4 * Real.log (N + 2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hH.le hlogtwo.le
      nlinarith
    calc
      (inputHeight N : ℝ) ≤ (4 * Real.log (N + 2 : ℝ)) / Real.log 2 :=
        (le_div_iff₀ hlogtwo).2 hproduct
      _ = (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWorkAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The depth-dependent scalar overhead of the actual initial estimator.
The expected array-counter bound includes every pruning outcome. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem coarse_depth_mul_exponent_bound (N : ℕ) :
    computedMaxCoarseDepth N * (heightExponent N * coarseExponent (inputSmallLog N)) ≤
      inputHeight N + heightExponent N * coarseExponent (inputSmallLog N) := by
  let e := heightExponent N * coarseExponent (inputSmallLog N)
  have hB : (integerParameters N).B = 2 ^ e := by
    simp only [integerParameters, inputHeight, ← pow_mul, e]
  have hdepth : computedMaxCoarseDepth N = (Nat.clog 2 (max 1 N) + (e - 1)) / e := by
    unfold computedMaxCoarseDepth computedCoarseDepth
    rw [hB, Nat.clog_pow_left]
  have hlength : max 1 N ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact (Nat.le_add_right N 2).trans (inputHeight_covers_length N)
  have hlog : Nat.clog 2 (max 1 N) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hlength
  have hprod := Nat.div_mul_le_self (Nat.clog 2 (max 1 N) + (e - 1)) e
  rw [← hdepth] at hprod
  exact hprod.trans (Nat.add_le_add hlog (Nat.sub_le _ _))

theorem scalar_coarse_depth_log_bound (D e p H c : ℝ)
    (hp : 0 < p) (hH : 0 < H) (hc : 0 ≤ c)
    (hbound : D * (e * p) ≤ H + e * p) :
    D * (e * c) / H ≤ e * c / H + c / p := by
  have hDe : D * e ≤ H / p + e := by
    calc
      D * e ≤ (H + e * p) / p := (le_div_iff₀ hp).2 (by nlinarith only [hbound])
      _ = H / p + e := by field_simp [hp.ne']
  have hmul := mul_le_mul_of_nonneg_right hDe hc
  have hdiv := div_le_div_of_nonneg_right hmul hH.le
  calc
    D * (e * c) / H = (D * e) * c / H := by ring
    _ ≤ (H / p + e) * c / H := hdiv
    _ = e * c / H + c / p := by field_simp [hp.ne', hH.ne'] <;> ring

theorem coarse_depth_log_height_div_height_tendsto :
    Tendsto (fun N => (computedMaxCoarseDepth N : ℝ) *
      Real.log (inputHeight N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hinv : Tendsto (fun N => Real.log 2 / (coarseExponent (inputSmallLog N) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using
      coarseExponent_real_tendsto.inv_tendsto_atTop.const_mul (Real.log 2)
  have hupper := hlog.add hinv
  simp only [zero_add] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [coarseExponent_tendsto.eventually (eventually_ge_atTop 1)] with N hp
  have hbound : (computedMaxCoarseDepth N : ℝ) *
      ((heightExponent N : ℝ) * coarseExponent (inputSmallLog N)) ≤
      (inputHeight N : ℝ) + (heightExponent N : ℝ) * coarseExponent (inputSmallLog N) := by
    exact_mod_cast coarse_depth_mul_exponent_bound N
  rw [inputHeight_real_log]
  exact scalar_coarse_depth_log_bound _ _ _ _ _
    (by exact_mod_cast (show 0 < coarseExponent (inputSmallLog N) by omega))
    (by exact_mod_cast Nat.two_pow_pos (heightExponent N))
    (Real.log_nonneg (by norm_num)) hbound

theorem computedCoarseOverheadExponent_tendsto (C : ℝ) :
    Tendsto (fun N => computedCoarseOverheadExponent C N / inputHeight N) atTop (𝓝 0) := by
  have h := (coarse_depth_log_height_div_height_tendsto.add
    encoding_exponent_div_height_tendsto).const_mul C
  simp only [zero_add, mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  unfold computedCoarseOverheadExponent
  ring

theorem coarse_branching_log_div_height_tendsto :
    Tendsto (fun N => Real.log ((integerParameters N).B : ℝ) / inputHeight N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have h := encoding_exponent_div_height_tendsto.sub hlog
  simp only [sub_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  simp only [integerParameters, Nat.cast_pow, Real.log_pow]
  ring

/-- The literal coarse threshold law has the paper's `H^8` inverse-allowance
factor, for all sufficiently large inputs and without any accuracy event. -/
theorem coarse_inverse_allowance_le_height_eight_eventually :
    ∀ᶠ N in atTop, coarseInverseAllowanceFactor (integerParameters N).B
      (initialThresholdQ N) (initialLambda N) ≤ (inputHeight N : ℝ) ^ 8 := by
  have hratio := coarse_branching_log_div_height_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, inputHeight_real_tendsto.eventually (eventually_ge_atTop 128)] with N hratio hlarge
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlog : Real.log ((integerParameters N).B : ℝ) ≤ inputHeight N :=
    ((div_lt_one hH).1 hratio).le
  have hraw := coarseInverseAllowanceFactor_log_bound (integerParameters N).B
    (initialThresholdQ N) (initialLambda N)
    (by unfold initialThresholdQ; positivity) (by unfold initialLambda; positivity)
  have hfactor : ((initialThresholdQ N : ℚ) : ℝ) / ((initialLambda N : ℚ) : ℝ) =
      64 * (inputHeight N : ℝ) ^ 5 := by
    simp only [initialThresholdQ, initialLambda, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    field_simp [hH.ne']
  rw [hfactor] at hraw
  have hstep : 1 + Real.log ((integerParameters N).B : ℝ) ≤ 2 * (inputHeight N : ℝ) := by
    linarith
  calc
    _ ≤ 64 * (inputHeight N : ℝ) ^ 5 * (1 + Real.log ((integerParameters N).B : ℝ)) := hraw
    _ ≤ 64 * (inputHeight N : ℝ) ^ 5 * (2 * (inputHeight N : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 128 * (inputHeight N : ℝ) ^ 6 := by ring
    _ ≤ (inputHeight N : ℝ) ^ 2 * (inputHeight N : ℝ) ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = (inputHeight N : ℝ) ^ 8 := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterDependencyAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- A uniform depth upper bound is obtained by using the total length as
the source length. -/
theorem tree_logSmallLog_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) *
      Real.log (inputSmallLog N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := log_smallLog_div_smallLog_tendsto.const_mul 100
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  have hbound : (computedMaxTreeDepth N : ℝ) * inputSmallLog N ≤ 100 * (inputHeight N : ℝ) := by
    exact_mod_cast computed_tree_depth_bound N N hN le_rfl hell
  have hlog : 0 ≤ Real.log (inputSmallLog N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hellpos : (0 : ℝ) < inputSmallLog N := by exact_mod_cast Nat.two_pow_pos (smallLogExponent N)
  have hscaled := mul_le_mul_of_nonneg_right hbound hlog
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hH hellpos).2
  nlinarith only [hscaled]

theorem tree_depth_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ tree_logSmallLog_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputSmallLog_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hlog

theorem dependency_index_div_height_tendsto :
    Tendsto (fun N => (computedDependencyIndexCount N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ weighted_dependency_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputHeight_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (computedDependencyIndexCount N : ℝ) ≤
        ((coarseExponent (inputSmallLog N) : ℝ) + 1) * computedDependencyIndexCount N := by
      have hm : (0 : ℝ) ≤ (coarseExponent (inputSmallLog N) : ℝ) * computedDependencyIndexCount N :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [hm]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog

/-- Every fixed choice of the two branching-budget constants yields a
sublinear logarithmic overhead in the dependency-path bound. -/
theorem computedDependencyOverheadExponent_tendsto (C₁ C₂ : ℝ) :
    Tendsto (fun N => computedDependencyOverheadExponent C₁ C₂ N / inputHeight N)
      atTop (𝓝 0) := by
  have htwo : Tendsto (fun N => 2 / (inputHeight N : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using inputHeight_real_tendsto.inv_tendsto_atTop.const_mul 2
  have h := (((tree_depth_div_height_tendsto.add dependency_index_div_height_tendsto).add htwo).const_mul
    (1 + Real.log 2)).add ((tree_logSmallLog_div_height_tendsto.const_mul C₁).add
      (weighted_dependency_div_height_tendsto.const_mul C₂))
  simp only [zero_add, mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  unfold computedDependencyOverheadExponent
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SubexponentialTransfer
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion from the computed-height bounds to asymptotics in the actual
input length. The bounds concern scalar envelopes, not an uncharged program. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem subexponential_height_to_input (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (f N) ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := hf.eventually (gt_mem_nhds
    (show (0 : ℝ) < epsilon * Real.log 2 / 4 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hfN : f N ≤ (epsilon * Real.log 2 / 4) * inputHeight N :=
    ((div_lt_iff₀ hH).1 hsmall).le
  have hheight := (height_log_sandwich N hN).2
  have hscaled := mul_le_mul_of_nonneg_left hheight
    (show (0 : ℝ) ≤ epsilon * Real.log 2 / 4 by positivity)
  have hcancel : (epsilon * Real.log 2 / 4) *
      ((4 / Real.log 2) * Real.log (N + 2 : ℝ)) = epsilon * Real.log (N + 2 : ℝ) := by
    field_simp [hlogtwo.ne']
  have hexponent : f N ≤ epsilon * Real.log (N + 2 : ℝ) :=
    hfN.trans (hscaled.trans_eq hcancel)
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < N + 2)]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hexponent

theorem sublinear_height_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ (N : ℕ) in atTop, (N + 2 : ℝ) * Real.exp (f N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [subexponential_height_to_input f hf epsilon hepsilon] with N hN
  rw [Real.rpow_add (by positivity : (0 : ℝ) < N + 2), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyPathEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit subpolynomial envelope for the finite dependency-path sum.
The connection between this sum and an execution is a separate obligation. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem nat_pow_eq_exp_log (a n : ℕ) (ha : 0 < a) :
    (a : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log a) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]

end EditApproximation

end OAI
end

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

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseWidthCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coarse array counter has a common source-width overhead.
Its exponent is sublinear in the computed logarithmic height. -/

namespace EditApproximation

open MeasureTheory

theorem coarse_width_overhead_le_power (H D p L : ℕ) (hH : 2 ≤ H) (hL : L ≤ H) :
    6 * H ^ p * (L + 1) * (D + 1) * H ^ (8 * D) ≤ H ^ (10 * (D + p + 1)) := by
  have hsix : 6 ≤ H ^ 3 := by
    have hpow := Nat.pow_le_pow_left hH 3
    norm_num at hpow
    omega
  have hlogtwo : L + 1 ≤ H ^ 2 := by nlinarith
  have hdepth : D + 1 ≤ H ^ D :=
    (Nat.succ_le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans
      (Nat.pow_le_pow_left hH D)
  calc
    _ ≤ H ^ 3 * H ^ p * H ^ 2 * H ^ D * H ^ (8 * D) := by gcongr
    _ = H ^ (p + 9 * D + 5) := by
      simp only [← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < H) (by omega)

theorem computedCoarseWidthOverhead_le (N : ℕ) (hN : 0 < N) :
    computedCoarseWidthOverhead N ≤ inputHeight N ^
      (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1)) := by
  have hH : 2 ≤ inputHeight N := by
    exact (show 2 ^ 1 ≤ 2 ^ heightExponent N from
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (heightExponent_pos N hN))
  have hlog : Nat.clog 2 N ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
      ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  exact coarse_width_overhead_le_power (inputHeight N) (computedMaxCoarseDepth N)
    (coarseExponent (inputSmallLog N)) (Nat.clog 2 N) hH hlog

theorem computedCoarseWidthOverhead_exp_le (N : ℕ) (hN : 0 < N) :
    (computedCoarseWidthOverhead N : ℝ) ≤ Real.exp (computedCoarseOverheadExponent 10 N) := by
  have h := computedCoarseWidthOverhead_le N hN
  have hcast : (computedCoarseWidthOverhead N : ℝ) ≤ (inputHeight N : ℝ) ^
      (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1)) := by exact_mod_cast h
  rw [nat_pow_eq_exp_log (inputHeight N)
    (10 * (computedMaxCoarseDepth N + coarseExponent (inputSmallLog N) + 1))
    (show 0 < inputHeight N from Nat.two_pow_pos (heightExponent N))] at hcast
  convert hcast using 1
  all_goals try with_reducible_and_instances rfl
  unfold computedCoarseOverheadExponent
  push_cast
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-seed numerical dimension and source-range bounds after substituting
the computed grid size. These bounds do not use an accuracy event. -/

namespace EditApproximation

theorem wide_coordinate_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    M * (40 * P + 2) ^ 2 ≤ H ^ (2 * p + 45) := by
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hconstant : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hconstant hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H 2 (p + 20)).symm
      _ = _ := by congr 1; omega
  calc
    _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul hM (Nat.pow_le_pow_left hbox 2)
    _ = H * H ^ ((p + 22) * 2) := by rw [pow_mul]
    _ = H ^ ((p + 22) * 2 + 1) := (pow_succ' H _).symm
    _ = _ := by congr 1; omega

theorem optimizer_parameter_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    H + M * (40 * P + 2) ^ 2 + 4 ≤ H ^ (2 * p + 46) := by
  have hdimension := wide_coordinate_budget_le H M P p hH hM hP hPcap
  have hlarge : H ≤ H ^ (2 * p + 45) := Nat.le_pow (by omega)
  have hfour : 4 ≤ H ^ (2 * p + 45) := (by omega : 4 ≤ H).trans hlarge
  calc
    _ ≤ 3 * H ^ (2 * p + 45) := by omega
    _ ≤ H * H ^ (2 * p + 45) := Nat.mul_le_mul_right _ (by omega)
    _ = H ^ (2 * p + 45 + 1) := (pow_succ' H _).symm
    _ = _ := rfl

theorem optimizerTriangularMass_le_square (K : ℕ) : optimizerTriangularMass K ≤ K ^ 2 := by
  have htwice := optimizerTriangularMass_twice K
  have hpower : K ≤ K ^ 2 := Nat.le_pow (by decide)
  nlinarith only [htwice, hpower]

theorem localOnlineMassBound_polynomial (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    localOnlineMassBound M P H ≤ H ^ (8000 * (p + 1)) := by
  have hG : H + M * (40 * P + 2) ^ 2 + 2 ≤ H ^ (2 * p + 46) :=
    (by omega : H + M * (40 * P + 2) ^ 2 + 2 ≤ H + M * (40 * P + 2) ^ 2 + 4).trans
      (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  calc
    _ ≤ ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ^ 2 := optimizerTriangularMass_le_square _
    _ = (H + M * (40 * P + 2) ^ 2 + 2) ^ (80 * 2) := (pow_mul _ 80 2).symm
    _ ≤ (H ^ (2 * p + 46)) ^ (80 * 2) := Nat.pow_le_pow_left hG _
    _ = H ^ ((2 * p + 46) * (80 * 2)) := (pow_mul H _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem computed_localOnlineMassBound_polynomial (N : ℕ) (hH : 64 ≤ inputHeight N) :
    localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N) ≤
      inputHeight N ^ (8000 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply localOnlineMassBound_polynomial _ _ _ _ hH
  · exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  · exact Nat.one_le_pow _ _ (by omega)
  · exact le_rfl

theorem computed_localOnlineMassBound_bits (N : ℕ) (hH : 64 ≤ inputHeight N) :
    Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
      8000 * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 :=
  (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (natural_power_bit_length _ _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWidthEnvelope
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parameter-only majorant for every executed dependency tree. It is
independent of the accepted random values and of all accuracy events. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computedWidthEnvelope_nonneg (N : ℕ) : 0 ≤ computedWidthEnvelope N := by
  unfold computedWidthEnvelope
  positivity

theorem computedWidthEnvelope_mul_exp_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * Real.exp (f N) ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := ((computedDependencyOverheadExponent_tendsto 257 512).add
    (hlog.const_mul 2)).add hf
  simp only [mul_zero, add_zero] at hlimit
  have hfinal := sublinear_height_near_linear
    (fun N => computedDependencyOverheadExponent 257 512 N +
      2 * Real.log (inputHeight N : ℝ) + f N) (by
        convert hlimit using 1
        all_goals try with_reducible_and_instances rfl
        ext N
        ring) epsilon hepsilon
  filter_upwards [hfinal] with N hN
  convert hN using 1
  all_goals try with_reducible_and_instances rfl
  unfold computedWidthEnvelope
  rw [Real.exp_add, Real.exp_add]
  have hp : Real.exp (2 * Real.log (inputHeight N : ℝ)) = (inputHeight N : ℝ) ^ 2 := by
    simpa using (nat_pow_eq_exp_log (inputHeight N) 2 (Nat.two_pow_pos _)).symm
  rw [hp]
  ring

theorem computedWidthEnvelope_coarse_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * computedCoarseWidthOverhead N ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _
    (computedCoarseOverheadExponent_tendsto 10) epsilon hepsilon, eventually_ge_atTop 1] with N hN hpos
  exact (mul_le_mul_of_nonneg_left (computedCoarseWidthOverhead_exp_le N (by omega))
    (computedWidthEnvelope_nonneg N)).trans hN

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_HeightPowerWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 theorem fixed_height_power_subpolynomial (k : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (inputHeight N : ℝ) ^ k ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (k : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((k : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1 <;> first | (with_reducible_and_instances rfl) | (ext N; ring)
  filter_upwards [subexponential_height_to_input _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) k (Nat.two_pow_pos _)] at hN

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionSelectedCost
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rejection counts are independent of all accepted values. Thus even
an adaptive choice of coordinates incurs fewer than two word trials per
selected coordinate in expectation. No unused source is charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Selected

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]



 theorem rejectionRuntimeArrayLaw_accepted :
    (rejectionRuntimeArrayLaw range).map Prod.snd = rejectionAcceptedLaw range := by
  unfold rejectionRuntimeArrayLaw
  simp



end Selected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteProductWork
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executed sampler law supports both selected rejection work and
work depending only on the accepted finite draws. -/

namespace EditApproximation
open MeasureTheory

section Accepted
variable {α ι : Type*} [Fintype α] [Fintype ι]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (range : ι → ℕ) [∀ i, NeZero (range i)]
  (μ : Measure α) [IsFiniteMeasure μ]

omit [Fintype α] [Fintype ι] [MeasurableSingletonClass α] [∀ i, NeZero (range i)] in
 theorem rejectionProductAccepted_measurable : Measurable (rejectionProductAccepted (α := α) range) :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

omit [MeasurableSingletonClass α] [IsFiniteMeasure μ] in
 theorem rejectionProductAccepted_law :
    (μ.prod (rejectionRuntimeArrayLaw range)).map (rejectionProductAccepted range) =
      μ.prod (rejectionAcceptedLaw range) := by
  change (μ.prod _).map (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    rejectionRuntimeArrayLaw_accepted]

omit [IsFiniteMeasure μ] in
 theorem rejectionProductWork_integral (f : α × (∀ i, Fin (range i)) → ℝ) :
    (∫ outcome, f (rejectionProductAccepted range outcome)
      ∂μ.prod (rejectionRuntimeArrayLaw range)) = ∫ outcome, f outcome ∂μ.prod (rejectionAcceptedLaw range) := by
  rw [← rejectionProductAccepted_law range μ]
  exact (integral_map (rejectionProductAccepted_measurable range).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable).symm

omit [IsFiniteMeasure μ] in
 theorem rejectionProductWork_expected_le [IsProbabilityMeasure μ]
    (f : α × (∀ i, Fin (range i)) → ℝ) (budget : ℝ)
    (hbudget : ∀ draw, (∫ a, f (a, draw) ∂μ) ≤ budget) :
    (∫ outcome, f (rejectionProductAccepted range outcome)
      ∂μ.prod (rejectionRuntimeArrayLaw range)) ≤ budget := by
  rw [rejectionProductWork_integral range μ f, integral_prod_symm f Integrable.of_finite]
  calc
    _ ≤ ∫ _ : (∀ i, Fin (range i)), budget ∂rejectionAcceptedLaw range :=
      integral_mono Integrable.of_finite (integrable_const _) hbudget
    _ = _ := by simp

end Accepted
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uniform source-range address fits in one logarithmic input
word eventually. The coefficient can be any fixed natural number. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_sourceAddressBits_div_height_tendsto (C : ℕ) :
    Tendsto (fun N =>
      ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) /
        inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (4 * (C : ℝ) + 1)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := (inputSmallLog_bounds N hN).1
  have hp := coarseExponent_le_smallLog N
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hs : Nat.size (inputHeight N) = heightExponent N + 1 := by
    simp only [inputHeight, Nat.size_pow]
  have hsmall : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hell
  have hpR : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show coarseExponent (inputSmallLog N) + 1 ≤ 2 * inputSmallLog N by omega)
  have hsR : (Nat.size (inputHeight N) : ℝ) ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show Nat.size (inputHeight N) ≤ 2 * inputSmallLog N by omega)
  have hproduct := mul_le_mul hpR hsR (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hscaled := mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hnum : ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) ≤
      (4 * (C : ℝ) + 1) * (inputSmallLog N : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hscaled, hsmall, sq_nonneg ((inputSmallLog N : ℝ) - 1)]
  have h := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (inputHeight N) : (0 : ℝ) ≤ inputHeight N)
  simpa only [mul_div_assoc] using h

theorem computed_sourceAddressBits_le_height (C : ℕ) :
    ∀ᶠ N in atTop,
      C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 ≤ inputHeight N := by
  filter_upwards [(computed_sourceAddressBits_div_height_tendsto C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with N h
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlt := (div_lt_one hH).mp h
  exact_mod_cast hlt.le

theorem computed_localOnlineMassBound_word :
    ∀ᶠ N in atTop,
      Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
        inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000,
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 64)] with N hbits hH
  have hHnat : 64 ≤ inputHeight N := by exact_mod_cast hH
  exact (computed_localOnlineMassBound_bits N hHnat).trans hbits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Polynomial coarse-sampling budgets for the computed dimensions. -/

namespace EditApproximation
open MeasureTheory Filter

section Coarse
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 theorem symbolicComputedCoarseBudget_mono (a b : ℝ) (hab : a ≤ b)
    (h : SymbolicComputedCoarseBudget (B := B) source target N depth encode a) :
    SymbolicComputedCoarseBudget (B := B) source target N depth encode b := fun draw => (h draw).trans hab

end Coarse
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory Filter




 theorem computedPhysicalCoarseWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ComputedPhysicalCoarseBudget source target N ((N + 2 : ℝ) ^ (1 + epsilon)) := by
  filter_upwards [computedWidthEnvelope_coarse_near_linear epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word, coarse_inverse_allowance_le_height_eight_eventually]
    with N hw hN hell hB hinverse
  intro source target hsize
  exact symbolicComputedCoarseBudget_mono source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) _ _ hw
    (computedPhysicalCoarseWork_expected_le source target N (by omega) hell hsize hB hinverse)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedJointCoarseWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 theorem symbolicComputedExecutionCoarseWork_expected_le (budget : ℝ)
    (hbudget : SymbolicComputedCoarseBudget (B := B) source target N depth encode budget) :
    (∫ execution, symbolicComputedExecutionCoarseWork source target N depth encode execution
      ∂physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) ≤ budget := by
  exact rejectionProductWork_expected_le _ _
    (fun outcome => symbolicComputedCoarseWork source target N depth encode outcome.2 outcome.1)
    budget hbudget

 theorem symbolicComputedExecutionCoarseWork_integrable :
    Integrable (symbolicComputedExecutionCoarseWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedCoarseWork source target N depth encode outcome.2 outcome.1
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
end Symbolic



 theorem computedExecutionCoarseWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

 theorem computedExecutionCoarseWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedPhysicalCoarseWork_expected_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  exact symbolicComputedExecutionCoarseWork_expected_le source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    _ (hN source target hsize)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseSamplingWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.chargedPhysicalCodeWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalFamilyCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalTableCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalBoundedWithWork_value _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.querySupportedChildWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Coarse
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

/- One binary word is consumed for every threshold label actually exposed. -/


omit [NeZero B] in
theorem physicalFamilyCoarseSamplingWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (coarse : PhysicalCoarseDraw source target B depth) :
    physicalFamilyCoarseSamplingWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw depth bits encode root coarse ≤ (Nat.size B : ℝ) *
      physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta draw B depth bits encode root coarse := by
  classical
  unfold physicalFamilyCoarseSamplingWork physicalFamilyMemoCoarseWork
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro entry _
  have h := coarseInitialLabelCount_le_arrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
    (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (coarse entry)
  have hs : 0 ≤ selectionIndicator (Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
        T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger
        (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        answer bits encode root).freshKeys) := by
    unfold selectionIndicator
    split <;> norm_num
  push_cast
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (Nat.cast_nonneg (Nat.size B))) hs).trans_eq (by ring)

end Coarse
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseSamplingWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



theorem symbolicComputedExecutionCoarseSamplingWork_integrable :
    Integrable (symbolicComputedExecutionCoarseSamplingWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedExecutionCoarseSamplingWork source target N depth encode
      (outcome.1, (fun _ => 0, outcome.2))
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
omit [NeZero B] in
theorem symbolicComputedExecutionCoarseSamplingWork_bound
    (execution : PhysicalCoarseExecution (R := R) source target N
      (integerParameters N).P (inputHeight N) B depth) :
    symbolicComputedExecutionCoarseSamplingWork source target N depth encode execution ≤
      (Nat.size B : ℝ) * symbolicComputedExecutionCoarseWork source target N depth encode execution := by
  exact physicalFamilyCoarseSamplingWork_bound source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    execution.2.2 depth (16384 * inputHeight N + 5) encode
    (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length)) execution.1

end Symbolic



theorem computedExecutionCoarseSamplingWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseSamplingWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseSamplingWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

theorem computedExecutionCoarseSamplingWork_bound (source target : List ℕ) (N : ℕ)
    (execution : ComputedExecutionOutcome source target N) :
    computedExecutionCoarseSamplingWork source target N execution ≤
      (Nat.size (integerParameters N).B : ℝ) * computedExecutionCoarseWork source target N execution :=
  symbolicComputedExecutionCoarseSamplingWork_bound source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2)) execution

theorem computedExecutionCoarseSamplingWork_expected_near_linear_oai (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseSamplingWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have he : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarseWork_expected_near_linear (epsilon / 2) he,
    fixed_height_power_subpolynomial 2 (epsilon / 2) he,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hc hp hN hell
  intro source target hsize
  have hB := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
  rw [Nat.size_pow] at hB
  have hH := computed_coarse_height_large N (by omega) hell
  have hsizeB : Nat.size (integerParameters N).B ≤ inputHeight N ^ 2 := by nlinarith only [hB, hH]
  have hb : (∫ execution, computedExecutionCoarseSamplingWork source target N execution
      ∂computedExecutionLaw source target N) ≤
      (Nat.size (integerParameters N).B : ℝ) *
      (∫ execution, computedExecutionCoarseWork source target N execution ∂computedExecutionLaw source target N) := by
    calc
      _ ≤ ∫ execution, (Nat.size (integerParameters N).B : ℝ) *
          computedExecutionCoarseWork source target N execution ∂computedExecutionLaw source target N :=
        integral_mono (computedExecutionCoarseSamplingWork_integrable source target N)
          ((computedExecutionCoarseWork_integrable source target N).const_mul _)
          (computedExecutionCoarseSamplingWork_bound source target N)
      _ = _ := by rw [integral_const_mul]
  have hsizeBReal : (Nat.size (integerParameters N).B : ℝ) ≤ (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hsizeB
  calc
    _ ≤ (Nat.size (integerParameters N).B : ℝ) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      hb.trans (mul_le_mul_of_nonneg_left (hc source target hsize) (Nat.cast_nonneg _))
    _ ≤ (inputHeight N : ℝ) ^ 2 * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hsizeBReal (by positivity)
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear_oai := @OAI.EditApproximation.computedExecutionCoarseSamplingWork_expected_near_linear_oai

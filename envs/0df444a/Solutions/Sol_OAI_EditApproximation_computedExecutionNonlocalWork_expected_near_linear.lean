-- Prove2me | solution 1 for OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:02.731564+00:00
-- url     : https://prove2.me/submissions/8de771ff-0d6f-421c-bcf1-9a7620fcb310

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
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_le
import Theorems.Thm_OAI_EditApproximation_computedPhysicalCoarseWork_expected_le
import Theorems.Thm_OAI_EditApproximation_weighted_dependency_div_height_tendsto

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











theorem child_nodes (tree : BinaryMemo α) :
    tree.left.nodes + tree.right.nodes ≤ tree.nodes := by
  cases tree <;> simp only [left, right, nodes] <;> omega

theorem insert_nodes (tree : BinaryMemo α) (key : List Bool) (a : α) :
    (tree.insert key a).nodes ≤ tree.nodes + key.length + 1 := by
  induction key generalizing tree with
  | nil =>
    have h := child_nodes tree
    simp only [insert, nodes, List.length_nil]
    omega
  | cons b rest ih =>
    have h := child_nodes tree
    cases b
    · have hi := ih tree.left
      simp only [insert, nodes, List.length_cons]
      omega
    · have hi := ih tree.right
      simp only [insert, nodes, List.length_cons]
      omega

/-- Persistent insertion allocates one new node at each visited level;
the two untouched subtrees are retained by pointer. -/


theorem insertCosted_spec (tree : BinaryMemo α) (key : List Bool) (a : α) :
    tree.insertCosted key a = (tree.insert key a, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [insertCosted, insert, ih, List.length_cons]

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem rejectionFailureProbability_range (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    0 ≤ rejectionFailureProbability N R ∧ rejectionFailureProbability N R < 1 := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  constructor
  · unfold rejectionFailureProbability
    positivity
  · unfold rejectionFailureProbability
    rw [div_lt_one hR, Nat.cast_sub hNR]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    linarith

/-- The actual first-success trace law has expected trial count `R/N`;
this identifies the tail-sum calculation with the terminating executions. -/
theorem rejection_first_success_expected_trials (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * N *
      (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R))) ((R : ℝ) / N) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := rejectionFailureProbability_range N R hN hNR
  have hnorm : ‖rejectionFailureProbability N R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
    exact hq.2
  have hseries := ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hq.1 hq.2)).mul_right ((N : ℝ) / R)
  have hterm (n : ℕ) :
      ((n : ℝ) * rejectionFailureProbability N R ^ n + rejectionFailureProbability N R ^ n) *
          ((N : ℝ) / R) =
        ((n : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) := by
    simp only [rejectionFailureProbability, div_pow]
    ring
  have hratio : 1 - rejectionFailureProbability N R = (N : ℝ) / R := by
    unfold rejectionFailureProbability
    rw [Nat.cast_sub hNR]
    field_simp
    ring
  have hsum : (rejectionFailureProbability N R / (1 - rejectionFailureProbability N R) ^ 2 +
        (1 - rejectionFailureProbability N R)⁻¹) * ((N : ℝ) / R) = (R : ℝ) / N := by
    rw [hratio]
    have hqeq : rejectionFailureProbability N R = 1 - (N : ℝ) / R := by linarith [hratio]
    rw [hqeq]
    field_simp [hR.ne', hNreal.ne']
    ring
  simpa only [hterm, hsum] using hseries

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Computable base-M node labels and mixed-radix table-entry keys.
Equal source intervals at different physical nodes keep distinct keys. -/

namespace EditApproximation



theorem treeLayerCode_bound (M d : ℕ) (path : TreeLayer M d) :
    treeLayerCode M d path < M ^ d := by
  induction d with
  | zero => exact Nat.zero_lt_one
  | succ d ih =>
    have hp := ih path.1
    have hi := path.2.isLt
    change path.2.val + M * treeLayerCode M d path.1 < M ^ (d + 1)
    rw [pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hp)]

theorem treeLayerCode_injective (M d : ℕ) : Function.Injective (treeLayerCode M d) := by
  induction d with
  | zero => intro first second _; cases first; cases second; rfl
  | succ d ih =>
    rintro ⟨first, i⟩ ⟨second, j⟩ heq
    obtain ⟨hlabel, hpath⟩ := mixedRadix_injective i.isLt j.isLt heq
    exact Prod.ext (ih hpath) (Fin.ext hlabel)



theorem physicalNode_layer_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    treeLayerCode M node.1.val node.2 < M ^ J :=
  (treeLayerCode_bound M node.1.val node.2).trans_le
    (pow_le_pow_right₀ hM (Nat.le_of_lt_succ node.1.isLt))

theorem physicalNodeCode_injective {M J : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalNodeCode M J) := by
  rintro ⟨depth, path⟩ ⟨depth', path'⟩ heq
  obtain ⟨hp, hd⟩ := mixedRadix_injective
    (physicalNode_layer_bound hM ⟨depth, path⟩)
    (physicalNode_layer_bound hM ⟨depth', path'⟩) heq
  have hdepth : depth = depth' := Fin.ext hd
  subst depth'
  have hpath := treeLayerCode_injective M depth.val hp
  change path = path' at hpath
  subst path'
  rfl

theorem physicalNodeCode_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    physicalNodeCode node < M ^ J * (J + 1) := by
  have hpath := physicalNode_layer_bound hM node
  have hdepth := node.1.isLt
  unfold physicalNodeCode
  nlinarith only [hpath, Nat.mul_le_mul_left (M ^ J) (Nat.succ_le_of_lt hdepth)]



theorem physicalEntryCode_injective {M J n : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalEntryCode M J n) := by
  rintro ⟨node, q⟩ ⟨node', q'⟩ heq
  obtain ⟨hq, hn⟩ := mixedRadix_injective
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q))
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q')) heq
  have hstate := childInputCode_injective 1 n hq
  have hqeq : q = q' := congrArg (fun pair : Fin 1 × TargetInterval n => pair.2) hstate
  exact Prod.ext (physicalNodeCode_injective hM hn) hqeq

theorem physicalEntryCode_bound {M J n : ℕ} (hM : 1 ≤ M) (state : PhysicalEntry M J n) :
    physicalEntryCode state < (n + 1) ^ 2 * (M ^ J * (J + 1)) := by
  have hstate : childInputCode ((0 : Fin 1), state.2) < (n + 1) ^ 2 := by
    simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), state.2)
  have hnode := physicalNodeCode_bound hM state.1
  unfold physicalEntryCode
  nlinarith only [hstate, Nat.mul_le_mul_left ((n + 1) ^ 2) (Nat.succ_le_of_lt hnode)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





theorem code_injective {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ) :
    Function.Injective (fun request : {r : PhysicalTableRequest M J n // Bounded passes copies T S r} =>
      code copies T S request.val) := by
  intro first second heq
  obtain ⟨hindex, hrest⟩ := mixedRadix_injective
    (Nat.lt_succ_of_le first.2.2.2) (Nat.lt_succ_of_le second.2.2.2) heq
  obtain ⟨hcopy, hrest⟩ := mixedRadix_injective first.2.2.1 second.2.2.1 hrest
  obtain ⟨hentry, hpass⟩ := mixedRadix_injective
    (physicalEntryCode_bound hM (first.1.node, first.1.state))
    (physicalEntryCode_bound hM (second.1.node, second.1.state)) hrest
  have he := physicalEntryCode_injective hM hentry
  have hnode := congrArg Prod.fst he
  have hstate := congrArg Prod.snd he
  apply Subtype.ext
  cases first with
  | mk first hf =>
    cases second with
    | mk second hs =>
      cases first
      cases second
      simp only at hpass hcopy hnode hindex hstate
      cases hpass
      cases hcopy
      cases hnode
      cases hindex
      cases hstate
      rfl

theorem code_bound {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) (hrequest : Bounded passes copies T S request) :
    code copies T S request < capacity M J n passes copies T S := by
  have he := physicalEntryCode_bound hM (request.node, request.state)
  change physicalEntryCode (request.node, request.state) < entryCapacity M J n at he
  have hinner : physicalEntryCode (request.node, request.state) +
      entryCapacity M J n * request.pass < entryCapacity M J n * passes := by
    nlinarith only [he, Nat.mul_le_mul_left (entryCapacity M J n) (Nat.succ_le_of_lt hrequest.1)]
  have hmiddle : request.copy + copies *
      (physicalEntryCode (request.node, request.state) + entryCapacity M J n * request.pass) <
        copies * (entryCapacity M J n * passes) := by
    nlinarith only [hrequest.2.1, Nat.mul_le_mul_left copies (Nat.succ_le_of_lt hinner)]
  unfold code capacity
  nlinarith only [hrequest.2.2, Nat.mul_le_mul_left (T + S + 1) (Nat.succ_le_of_lt hmiddle)]

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem code_injective {M J ny passes copies T S : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@code M J ny passes copies T S) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hentry : physicalEntryCode left = physicalEntryCode right := by
        change 2 * physicalEntryCode left = 2 * physicalEntryCode right at heq
        omega
      exact congrArg Sum.inl (physicalEntryCode_injective hM hentry)
    | inr right =>
      change 2 * physicalEntryCode left = 2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * PhysicalTableRequest.code copies T S left.val + 1 = 2 * physicalEntryCode right at heq
      omega
    | inr right =>
      have htable : PhysicalTableRequest.code copies T S left.val =
          PhysicalTableRequest.code copies T S right.val := by
        change 2 * PhysicalTableRequest.code copies T S left.val + 1 =
          2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
        omega
      exact congrArg Sum.inr (PhysicalTableRequest.code_injective hM passes copies T S htable)

 theorem code_bound {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < capacity M J ny passes copies T S := by
  cases request with
  | inl entry =>
    have h := physicalEntryCode_bound hM entry
    change physicalEntryCode entry < PhysicalTableRequest.entryCapacity M J ny at h
    simp only [code, capacity]
    omega
  | inr request =>
    have h := PhysicalTableRequest.code_bound hM passes copies T S request.val request.property
    simp only [code, capacity]
    omega

end ChargedPhysicalRequest

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

theorem run_resource_bounds {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ) (B D : ℕ)
    (hask : ∀ key memory,
      (ask key memory).freshKeys.length ≤ (ask key memory).requests ∧
      (ask key memory).dictionaryVisits ≤ (ask key memory).requests * D ∧
      (ask key memory).memory.nodes ≤ memory.nodes + (ask key memory).freshKeys.length * B)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    (run ask program memory).freshKeys.length ≤ (run ask program memory).requests ∧
    (run ask program memory).dictionaryVisits ≤ (run ask program memory).requests * D ∧
    (run ask program memory).memory.nodes ≤ memory.nodes + (run ask program memory).freshKeys.length * B := by
  induction program generalizing memory with
  | done _ => simp only [run, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl, and_self]
  | read key next ih =>
    have hf := hask key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    dsimp only [run]
    simp only [List.length_append, Nat.add_mul]
    exact ⟨Nat.add_le_add hf.1 hr.1, Nat.add_le_add hf.2.1 hr.2.1, by omega⟩

end FiniteQuery

theorem rankedMemoEvaluate_resource_bounds {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length ≤
        (rankedMemoEvaluate rank program bits encode key memory).requests ∧
    (rankedMemoEvaluate rank program bits encode key memory).dictionaryVisits ≤
        (rankedMemoEvaluate rank program bits encode key memory).requests * (2 * (bits + 1)) ∧
    (rankedMemoEvaluate rank program bits encode key memory).memory.nodes ≤
        memory.nodes + (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length * (bits + 1) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length ≤
          (rankedMemoEvaluate rank program bits encode key memory).requests ∧
      (rankedMemoEvaluate rank program bits encode key memory).dictionaryVisits ≤
          (rankedMemoEvaluate rank program bits encode key memory).requests * (2 * (bits + 1)) ∧
      (rankedMemoEvaluate rank program bits encode key memory).memory.nodes ≤
          memory.nodes + (rankedMemoEvaluate rank program bits encode key memory).freshKeys.length * (bits + 1) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec, binaryMemoKey_length]
      split
      · simp only [List.length_nil, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
        exact ⟨Nat.zero_le _, by omega, le_rfl⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys.length ≤
                (rankedMemoEvaluate rank program bits encode child.val previous).requests ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).dictionaryVisits ≤
                (rankedMemoEvaluate rank program bits encode child.val previous).requests * (2 * (bits + 1)) ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).memory.nodes ≤
                previous.nodes + (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys.length * (bits + 1) := by
          intro child previous
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := FiniteQuery.run_resource_bounds
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (bits + 1) (2 * (bits + 1)) hchildren (program key) memory
        simp only [BinaryMemo.insertCosted_spec, binaryMemoKey_length, List.length_cons]
        have hn := BinaryMemo.insert_nodes
          (FiniteQuery.run (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).memory (binaryMemoKey bits (encode key))
          (FiniteQuery.run (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value
        simp only [binaryMemoKey_length] at hn
        constructor
        · omega
        constructor
        · nlinarith only [hr.2.1]
        · nlinarith only [hr.2.2, hn]
  exact hall (rank key) key rfl memory

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

theorem computedWidthEnvelope_weighted_near_linear (C : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * (inputHeight N : ℝ) ^ C ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (C : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((C : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1 <;> first | (with_reducible_and_instances rfl) | (ext N; ring)
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) C (Nat.two_pow_pos _)] at hN

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionRuntimeLaw
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A probability law for terminating fair-word rejection executions.
It records the failed trial count and accepted integer, identifies their
joint masses with literal finite fair-word traces, and charges all trials. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



theorem rejectionSuccessParameter_ne_zero (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    rejectionSuccessParameter N R hN hNR ≠ 0 := by
  intro h
  have heq := congrArg (fun p : unitInterval => (p : ℝ)) h
  have hpos : (0 : ℝ) < (N : ℝ) / R :=
    div_pos (by exact_mod_cast hN) (by exact_mod_cast hN.trans_le hNR)
  change (N : ℝ) / R = 0 at heq
  linarith

theorem rejectionSuccessParameter_complement (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    1 - (rejectionSuccessParameter N R hN hNR : ℝ) = ((R - N : ℕ) : ℝ) / R := by
  change 1 - (N : ℝ) / R = _
  rw [Nat.cast_sub hNR]
  have hR : (R : ℝ) ≠ 0 := by exact_mod_cast (hN.trans_le hNR).ne'
  field_simp [hR]

theorem rejection_trial_moment (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    (∫ failures : ℕ, ((failures : ℝ) + 1)
      ∂geometricMeasure (rejectionSuccessParameter N R hN hNR)) = (R : ℝ) / N := by
  rw [integral_geometricMeasure (rejectionSuccessParameter_ne_zero N R hN hNR)]
  have hterm (k : ℕ) :
      ((1 - (rejectionSuccessParameter N R hN hNR : ℝ)) ^ k *
          (rejectionSuccessParameter N R hN hNR : ℝ)) * ((k : ℝ) + 1) =
        ((k : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ k / ((R : ℝ) ^ k * R)) := by
    rw [rejectionSuccessParameter_complement]
    change (((R - N : ℕ) : ℝ) / R) ^ k * ((N : ℝ) / R) * ((k : ℝ) + 1) = _
    rw [div_pow]
    ring
  simp_rw [smul_eq_mul, hterm]
  exact (rejection_first_success_expected_trials N R hN hNR).tsum_eq

theorem rejection_trials_integrable (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    Integrable (fun failures : ℕ => (failures : ℝ) + 1)
      (geometricMeasure (rejectionSuccessParameter N R hN hNR)) := by
  apply (integrable_geometricMeasure_iff (rejectionSuccessParameter_ne_zero N R hN hNR)).mpr
  have hterm (k : ℕ) :
      (1 - (rejectionSuccessParameter N R hN hNR : ℝ)) ^ k *
        (rejectionSuccessParameter N R hN hNR : ℝ) * ‖(k : ℝ) + 1‖ =
      ((k : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ k / ((R : ℝ) ^ k * R)) := by
    rw [Real.norm_of_nonneg (by positivity), rejectionSuccessParameter_complement]
    change (((R - N : ℕ) : ℝ) / R) ^ k * ((N : ℝ) / R) * ((k : ℝ) + 1) = _
    rw [div_pow]
    ring
  simpa only [hterm] using (rejection_first_success_expected_trials N R hN hNR).summable

/-- All failed trials are included in this strict factor-two bound. -/
theorem rejection_fair_word_trial_moment (N : ℕ) (hN : 0 < N) :
    (∫ failures : ℕ, ((failures : ℝ) + 1)
      ∂geometricMeasure (rejectionSuccessParameter N (2 ^ rejectionBitCount N)
        hN (rejectionWord_range N hN).1)) < 2 := by
  rw [rejection_trial_moment]
  apply (div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact_mod_cast (rejectionWord_range N hN).2

/-- Exact expected number of consumed fair bits, including failed words. -/
theorem rejection_consumed_bits_moment (N : ℕ) (hN : 0 < N) :
    (∫ failures : ℕ, (((failures : ℝ) + 1) * rejectionBitCount N)
      ∂geometricMeasure (rejectionSuccessParameter N (2 ^ rejectionBitCount N)
        hN (rejectionWord_range N hN).1)) ≤ 2 * rejectionBitCount N := by
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right
    (rejection_fair_word_trial_moment N hN).le (Nat.cast_nonneg _)


end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 theorem naturalPairWithWork_cost (a b : ℕ) : (naturalPairWithWork a b).2 ≤ 5 := by
  unfold naturalPairWithWork
  split_ifs <;> dsimp only <;> decide



 theorem physicalNodeCodeWithWork_cost {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).2 ≤ 5 * J + 5 := by
  have h := node.1.isLt
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  omega



 theorem physicalEntryCodeWithWork_cost {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).2 ≤ 5 * J + 13 := by
  have h := physicalNodeCodeWithWork_cost entry.1
  change (physicalNodeCodeWithWork entry.1).2 + 8 ≤ _
  omega



 theorem physicalTableCodeWithWork_cost {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).2 ≤ 7 * J + 29 := by
  have he := physicalEntryCodeWithWork_cost (request.node, request.state)
  simp only [physicalTableCodeWithWork, parameterPowerWithWork_spec]
  omega



 theorem chargedPhysicalCodeWithWork_cost {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).2 ≤ 7 * J + 32 := by
  cases request with
  | inl entry => have h := physicalEntryCodeWithWork_cost entry
                 change (physicalEntryCodeWithWork entry).2 + 2 ≤ _
                 omega
  | inr request => have h := physicalTableCodeWithWork_cost copies T S request.val
                   change (physicalTableCodeWithWork copies T S request.val).2 + 3 ≤ _
                   omega



 theorem physicalScalarCodeWithWork_cost {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).2 ≤ 5 * J + 40 := by
  rcases key with ⟨online | group, index⟩
  · have hn := physicalEntryCodeWithWork_cost (online.1.1.val, online.1.2.2)
    have ha := naturalPairWithWork_cost online.2.val.val index.val
    have hb := naturalPairWithWork_cost online.1.2.1.val
      (naturalPairWithWork online.2.val.val index.val).1
    have hc := naturalPairWithWork_cost (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega
  · have hn := physicalNodeCodeWithWork_cost group.1.val
    have ha := naturalPairWithWork_cost index.2.1.val index.2.2.val
    have hb := naturalPairWithWork_cost index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have hc := naturalPairWithWork_cost group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have hd := naturalPairWithWork_cost group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have he := naturalPairWithWork_cost group.2.1.val
      (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val
          (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have hf := naturalPairWithWork_cost (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val
        (naturalPairWithWork group.2.2.1.val
          (naturalPairWithWork group.2.2.2.val
            (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega

section Family
variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 theorem physicalFamilyCodeWithWork_cost
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).2 ≤ 5 * J + 52 := by
  have hs := physicalScalarCodeWithWork_cost key.2.2
  have hc := naturalPairWithWork_cost key.2.1.val (physicalScalarCodeWithWork key.2.2).1
  have hp := naturalPairWithWork_cost key.1.val
    (naturalPairWithWork key.2.1.val (physicalScalarCodeWithWork key.2.2).1).1
  dsimp only [physicalFamilyCodeWithWork]
  omega
end Family



 theorem computedFamilyMemoCodeWithWork_cost (source target : List ℕ) (N R : ℕ)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    (computedFamilyMemoCodeWithWork source target N R key).2 ≤
      7 * intervalTreeDepth (integerParameters N).M source.length + 60 := by
  cases key with
  | inl key =>
    have h := physicalFamilyCodeWithWork_cost target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key
    change (physicalFamilyCodeWithWork target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key).2 + 2 ≤ _
    omega
  | inr key =>
    have h := chargedPhysicalCodeWithWork_cost key
    change (chargedPhysicalCodeWithWork key).2 + 3 ≤ _
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoAddressWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace FiniteQuery

/-- Annotate exactly the requests made by an existing adaptive run. -/


 theorem requestWork_le {ι κ : Type*} (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (cost : ι → BinaryMemo ℚ → ℕ) (C : ℕ)
    (hcost : ∀ key memory, cost key memory ≤ C * (ask key memory).requests)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    requestWork ask cost program memory ≤ C * (run ask program memory).requests := by
  induction program generalizing memory with
  | done value => simp only [requestWork, run, Nat.mul_zero, le_refl]
  | read key next ih =>
    have hfirst := hcost key memory
    have hrest := ih (ask key memory).value (ask key memory).memory
    simp only [requestWork, run, Nat.mul_add]
    exact Nat.add_le_add hfirst hrest

end FiniteQuery

/-- Code construction is incurred for lookup and, on a miss, for insertion.
The recursive calls use the exact same returned values and cache states. -/


 theorem rankedMemoAddressWork_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (C : ℕ) (hcost : ∀ key, cost key ≤ C)
    (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoAddressWork rank program bits encode cost key memory ≤
      2 * C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoAddressWork rank program bits encode cost key memory ≤
        2 * C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoAddressWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only
        simpa only [Nat.mul_one] using (hcost key).trans (by omega : C ≤ 2 * C)
      · rename_i hfound
        simp only
        have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            rankedMemoAddressWork rank program bits encode cost child.val previous ≤
              2 * C * (rankedMemoEvaluate rank program bits encode child.val previous).requests := by
          intro child previous
          exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
        have hr := FiniteQuery.requestWork_le
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoAddressWork rank program bits encode cost child.val previous)
          (2 * C) hchildren (program key) memory
        have hk := hcost key
        rw [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FreshCoordinateCost
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A first request can depend on earlier answers, but cannot depend on
its own unexposed coordinate. Finite product independence then preserves
that coordinate's unconditional expected cost. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory Finset

attribute [local instance] Classical.propDecidable



theorem sum_distinct_requests_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, if i ∈ keys then weight i else 0) ≤ (keys.map weight).sum := by
  have hset : univ.filter (fun i => i ∈ keys) = keys.toFinset := by ext i; simp
  rw [← sum_filter, hset]
  clear hset
  induction keys with
  | nil => simp
  | cons key keys ih =>
    by_cases hmem : key ∈ keys
    · simp only [List.toFinset_cons, insert_eq_of_mem (List.mem_toFinset.mpr hmem),
        List.map_cons, List.sum_cons]
      omega
    · rw [List.toFinset_cons, sum_insert (by simpa only [List.mem_toFinset] using hmem),
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

theorem sum_selected_nat_weights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, selectionIndicator (i ∈ keys) * (weight i : ℝ)) ≤
      ((keys.map weight).sum : ℕ) := by
  calc
    _ = ∑ i, if i ∈ keys then (weight i : ℝ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ keys <;> simp [selectionIndicator, hi]
    _ ≤ _ := by exact_mod_cast sum_distinct_requests_le keys weight

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionSelectedCost
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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



 theorem rejectionFailureArray_bits_integrable (i : ι) :
    Integrable (fun failures : ι → ℕ => ((failures i : ℝ) + 1) * rejectionBitCount (range i))
      (Measure.pi (rejectionFailureLaw range)) := by
  apply integrable_comp_eval (X := fun _ : ι => ℕ) (μ := rejectionFailureLaw range) (i := i)
    (f := fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i))
  exact (rejection_trials_integrable (range i) (2 ^ rejectionBitCount (range i))
    (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    (rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1).mul_const _

 theorem rejectionSelectedBits_integrable (selected : ι → (∀ i, Fin (range i)) → Prop) :
    Integrable (rejectionSelectedBits range selected) (rejectionRuntimeArrayLaw range) := by
  classical
  unfold rejectionSelectedBits rejectionRuntimeArrayLaw
  apply integrable_finsetSum
  intro i _
  exact (rejectionFailureArray_bits_integrable range i).mul_prod (Integrable.of_finite (μ := rejectionAcceptedLaw range)
    (f := fun accepted => selectionIndicator (selected i accepted)))

 theorem rejectionSelectedBits_expected_le
    (selected : ι → (∀ i, Fin (range i)) → Prop) (budget : ℝ)
    (hbudget : ∀ accepted, ∑ i, (rejectionBitCount (range i) : ℝ) *
      selectionIndicator (selected i accepted) ≤ budget) :
    (∫ execution, rejectionSelectedBits range selected execution ∂rejectionRuntimeArrayLaw range) ≤
      2 * budget := by
  classical
  unfold rejectionSelectedBits rejectionRuntimeArrayLaw
  rw [integral_finsetSum]
  · have hprod (i : ι) :
        (∫ execution : RejectionRuntimeArray range,
          (((execution.1 i : ℝ) + 1) * rejectionBitCount (range i)) *
            selectionIndicator (selected i execution.2)
          ∂(Measure.pi (rejectionFailureLaw range)).prod (rejectionAcceptedLaw range)) =
        (∫ failures : ι → ℕ, ((failures i : ℝ) + 1) * rejectionBitCount (range i)
          ∂Measure.pi (rejectionFailureLaw range)) *
        (∫ accepted, selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) :=
      integral_prod_mul (μ := Measure.pi (rejectionFailureLaw range))
        (ν := rejectionAcceptedLaw range)
        (fun failures : ι → ℕ => ((failures i : ℝ) + 1) * rejectionBitCount (range i))
        (fun accepted : ∀ i, Fin (range i) => selectionIndicator (selected i accepted))
    simp_rw [hprod]
    have hcost (i : ι) :
        (∫ failures : ι → ℕ, ((failures i : ℝ) + 1) * rejectionBitCount (range i)
          ∂Measure.pi (rejectionFailureLaw range)) ≤ 2 * rejectionBitCount (range i) := by
      rw [integral_comp_eval (X := fun _ : ι => ℕ) (μ := rejectionFailureLaw range) (i := i)
        (f := fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i))
        (by fun_prop)]
      exact rejection_consumed_bits_moment (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    calc
      _ ≤ ∑ i, (2 * rejectionBitCount (range i)) *
          (∫ accepted, selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right (hcost i)
        exact integral_nonneg (fun _ => by unfold selectionIndicator; split_ifs <;> norm_num)
      _ = 2 * (∫ accepted, ∑ i, (rejectionBitCount (range i) : ℝ) *
          selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) := by
        rw [integral_finsetSum]
        · simp only [integral_const_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        · intro i _
          exact Integrable.of_finite
      _ ≤ 2 * budget := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (integral_mono Integrable.of_finite (integrable_const _) hbudget).trans_eq (by simp [rejectionAcceptedLaw])
  · intro i _
    exact (rejectionFailureArray_bits_integrable range i).mul_prod (Integrable.of_finite (μ := rejectionAcceptedLaw range)
    (f := fun accepted => selectionIndicator (selected i accepted)))

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

 theorem finite_outer_integrable {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hsections : ∀ a, Integrable (fun b => f (a, b)) ν) :
    Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff (measurable_of_countable f).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hsections, Integrable.of_finite⟩

 theorem finite_outer_expected_le {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hsections : ∀ a, Integrable (fun b => f (a, b)) ν)
    (budget : ℝ) (hbudget : ∀ a, (∫ b, f (a, b) ∂ν) ≤ budget) :
    (∫ outcome, f outcome ∂μ.prod ν) ≤ budget := by
  rw [integral_prod f (finite_outer_integrable μ ν f hsections)]
  calc
    _ ≤ ∫ _ : α, budget ∂μ := integral_mono Integrable.of_finite (integrable_const _) hbudget
    _ = _ := by simp

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionMemoCost
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal rejection trials are charged only for source coordinates
encountered by the shared memo execution. The accepted coordinates may
influence the entire request list; failure counts remain independent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Memo

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
  (range : σ → ℕ) [∀ key, NeZero (range key)]

omit [∀ key, NeZero (range key)] in
 theorem memo_selected_source_bits_le (keys : List (Sum σ κ)) (bits : ℕ)
    (hbits : ∀ key, rejectionBitCount (range key) ≤ bits) :
    (∑ key, (rejectionBitCount (range key) : ℝ) *
      selectionIndicator (Sum.inl key ∈ keys)) ≤ keys.length * bits := by
  let weight : Sum σ κ → ℕ := Sum.elim (fun key => rejectionBitCount (range key)) (fun _ => 0)
  have hs := sum_selected_nat_weights_le keys weight
  rw [Fintype.sum_sum_type] at hs
  simp only [weight, Sum.elim_inl, Sum.elim_inr, Nat.cast_zero, mul_zero,
    Finset.sum_const_zero, add_zero] at hs
  have hb : (keys.map weight).sum ≤ keys.length * bits := by
    clear hs
    induction keys with
    | nil => simp
    | cons key keys ih =>
      have hk : weight key ≤ bits := by cases key <;> simp only [weight, Sum.elim_inl, Sum.elim_inr]; exact hbits _; omega
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
      omega
  calc
    _ = ∑ key, selectionIndicator (Sum.inl key ∈ keys) * (rejectionBitCount (range key) : ℝ) := by
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ ((keys.map weight).sum : ℕ) := hs
    _ ≤ (keys.length * bits : ℕ) := by exact_mod_cast hb
    _ = _ := by push_cast; rfl

theorem memo_rejectionBits_expected_le_real
    (freshKeys : (∀ key, Fin (range key)) → List (Sum σ κ))
    (budget : ℝ) (bits : ℕ)
    (hrequests : ∀ accepted, ((freshKeys accepted).length : ℝ) ≤ budget)
    (hbits : ∀ key, rejectionBitCount (range key) ≤ bits) :
    (∫ execution, rejectionSelectedBits range
      (fun key accepted => Sum.inl key ∈ freshKeys accepted) execution
      ∂rejectionRuntimeArrayLaw range) ≤ 2 * (budget * bits) := by
  apply rejectionSelectedBits_expected_le
  intro accepted
  exact (memo_selected_source_bits_le range (freshKeys accepted) bits hbits).trans
    (mul_le_mul_of_nonneg_right (hrequests accepted) (Nat.cast_nonneg _))

end Memo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite scalar family is exactly the accepted output of the
independent literal rejection samplers. Only requested coordinates need
be generated; their failure counts have a product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)





omit [NeZero M] in
 theorem physicalFamilyRange_bits_le (bits : ℕ)
    (hM : M ≤ 2 ^ bits) (hB : localOnlineMassBound M P H ≤ 2 ^ bits)
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    rejectionBitCount (physicalFamilyRange target N P F exponent H Q passes copies key) ≤ bits := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  rcases key with ⟨pass, copy, scalar, index⟩
  cases scalar with
  | inl online =>
    change online.2.val.val ≤ 2 ^ bits
    exact (Nat.le_of_lt_succ online.2.val.isLt).trans hB
  | inr group => exact hM

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computedFamilyRange_bits_le (source target : List ℕ) (N R : ℕ)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : ComputedFamilyScalarKey source target N R) :
    rejectionBitCount (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key) ≤ inputHeight N := by
  apply physicalFamilyRange_bits_le
  · change 2 ^ (heightExponent N / 20) ≤ 2 ^ inputHeight N
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    exact (Nat.div_le_self _ _).trans (Nat.lt_two_pow_self.le)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hB)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRejectionWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Work

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)



 theorem physicalFamilyMemoBits_integrable (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (seed : SeedState) :
    Integrable (physicalFamilyMemoBits source target N P T S H hH bits encode rootQ seed)
      (rejectionRuntimeArrayLaw FamilyRange) := rejectionSelectedBits_integrable _ _

 theorem physicalFamilyMemoBits_expected_le (hH : 0 < H) (bits sourceBits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (seed : SeedState)
    (budget : ℝ)
    (hrequests : ∀ draw, ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ
      (seed, draw)).requests : ℝ) ≤ budget)
    (hbits : ∀ key, rejectionBitCount (FamilyRange key) ≤ sourceBits) :
    (∫ execution, physicalFamilyMemoBits source target N P T S H hH bits encode rootQ seed execution
      ∂rejectionRuntimeArrayLaw FamilyRange) ≤ 2 * (budget * sourceBits) := by
  classical
  let : Fintype Table := Fintype.ofInjective
    (fun key : Table => (⟨ChargedPhysicalRequest.code key,
      ChargedPhysicalRequest.code_bound (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) key⟩ :
        Fin (ChargedPhysicalRequest.capacity M J target.length (passes + 1) (H ^ 2) T S)))
    (fun _ _ h => ChargedPhysicalRequest.code_injective
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) (congrArg Fin.val h))
  apply memo_rejectionBits_expected_le_real FamilyRange _ budget sourceBits _ hbits
  intro draw
  have hf : (physicalFamilyMemoResult source target N P T S H hH bits encode rootQ
      (seed, draw)).freshKeys.length ≤
      (physicalFamilyMemoResult source target N P T S H hH bits encode rootQ (seed, draw)).requests :=
    (rankedMemoEvaluate_resource_bounds _ _ _ _ _ _).1
  exact (Nat.cast_le (α := ℝ)).mpr hf |>.trans (hrequests draw)

end Work

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open Filter MeasureTheory

private theorem power_succ_add_one (x : ℝ) (hx : 2 ≤ x) (n : ℕ) :
    x ^ n + 1 ≤ x ^ (n + 1) := by
  have hnonneg : 0 ≤ x ^ n := pow_nonneg (by linarith) _
  have hone : 1 ≤ x ^ n := one_le_pow₀ (by linarith)
  calc
    _ ≤ x ^ n + x ^ n := add_le_add le_rfl hone
    _ = x ^ n * 2 := by ring
    _ ≤ x ^ n * x := mul_le_mul_of_nonneg_left hx hnonneg
    _ = _ := (pow_succ _ _).symm

private theorem rejection_factor_le (x : ℝ) (hx : 2 ≤ x) (n : ℕ) :
    2 * (x ^ n + 1) * x ≤ x ^ (n + 3) := by
  have hnonneg : 0 ≤ x := by linarith
  have hone : 1 ≤ x ^ n := one_le_pow₀ (by linarith)
  have hsum : x ^ n + 1 ≤ 2 * x ^ n := by linarith
  have hsquare : 4 ≤ x ^ 2 := by nlinarith only [hx]
  calc
    _ ≤ 2 * (2 * x ^ n) * x := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (by norm_num)) hnonneg
    _ = 4 * x ^ (n + 1) := by rw [pow_succ]; ring
    _ ≤ x ^ 2 * x ^ (n + 1) := mul_le_mul_of_nonneg_right hsquare (pow_nonneg hnonneg _)
    _ = x ^ (2 + (n + 1)) := (pow_add _ _ _).symm
    _ = _ := by congr 1; omega

private theorem dictionary_factor_le (H : ℕ) (hH : 32780 ≤ H) :
    2 * (16384 * H + 5 + 1) ≤ H ^ 2 := by nlinarith only [hH]


 theorem computedFamilyResult_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 92 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize input
  have hH : (2 : ℝ) ≤ inputHeight N := by
    exact_mod_cast (show 2 ≤ inputHeight N from
      ((by decide : 2 ≤ 200).trans two_hundred_le_two_pow_thousand).trans (hell.trans (computed_smallLog_le_height N)))
  have hp : (inputHeight N : ℝ) ^ 91 + 1 ≤ (inputHeight N : ℝ) ^ 92 := by
    exact power_succ_add_one (inputHeight N) hH 91
  calc
    _ ≤ ((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N :=
      computedFamilyResult_requests_le source target N (by omega) hell hsize hB input
    _ ≤ (inputHeight N : ℝ) ^ 92 * computedWidthEnvelope N :=
      mul_le_mul_of_nonneg_right hp (computedWidthEnvelope_nonneg N)
    _ ≤ _ := by simpa only [mul_comm] using hw



 theorem computedFamilyRejectionWork_expected_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (seed : ClampedPhysicalSeed (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M source.length) target.length N) :
    (∫ execution, computedFamilyRejectionWork source target N (seed, execution)
      ∂rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
        (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
        target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) ≤
      2 * ((((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) * inputHeight N) := by
  apply physicalFamilyMemoBits_expected_le source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (inputHeight N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) (finalTargetState target.length) seed
  · intro draw
    exact computedFamilyResult_requests_le source target N hN hell hsize hB (seed, draw)
  · exact computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hB


 theorem computedFamilyRejectionWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ seed : ComputedFamilySeed source target N,
      (∫ execution, computedFamilyRejectionWork source target N (seed, execution)
        ∂rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
          target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
          (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 94 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize seed
  have hH : (2 : ℝ) ≤ inputHeight N := by
    exact_mod_cast (show 2 ≤ inputHeight N from
      ((by decide : 2 ≤ 200).trans two_hundred_le_two_pow_thousand).trans (hell.trans (computed_smallLog_le_height N)))
  have hfactor : 2 * ((inputHeight N : ℝ) ^ 91 + 1) * inputHeight N ≤
      (inputHeight N : ℝ) ^ 94 := rejection_factor_le (inputHeight N) hH 91
  calc
    _ ≤ 2 * ((((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) * inputHeight N) :=
      computedFamilyRejectionWork_expected_le source target N (by omega) hell hsize hB seed
    _ = computedWidthEnvelope N * (2 * ((inputHeight N : ℝ) ^ 91 + 1) * inputHeight N) := by ring
    _ ≤ computedWidthEnvelope N * (inputHeight N : ℝ) ^ 94 :=
      mul_le_mul_of_nonneg_left hfactor (computedWidthEnvelope_nonneg N)
    _ ≤ _ := hw


 theorem computedFamilyResult_dictionary_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).dictionaryVisits : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 94 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 32780),
    computed_localOnlineMassBound_word] with N hw hN hell hH hB
  intro source target hsize input
  have hd : (computedFamilyResult source target N input).dictionaryVisits ≤
      (computedFamilyResult source target N input).requests *
        (2 * (16384 * inputHeight N + 5 + 1)) :=
    (rankedMemoEvaluate_resource_bounds _ _ _ _ _ _).2.1
  have hc : (2 * (16384 * inputHeight N + 5 + 1) : ℕ) ≤ inputHeight N ^ 2 := by
    have hnat : 32780 ≤ inputHeight N := by exact_mod_cast hH
    exact dictionary_factor_le (inputHeight N) hnat
  have hcR : ((2 * (16384 * inputHeight N + 5 + 1) : ℕ) : ℝ) ≤
      (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hc
  have hr := computedFamilyResult_requests_le source target N (by omega) hell hsize hB input
  have hpower : (inputHeight N : ℝ) ^ 91 + 1 ≤ (inputHeight N : ℝ) ^ 92 := by
    exact power_succ_add_one (inputHeight N) (by linarith only [hH]) 91
  have hdR : ((computedFamilyResult source target N input).dictionaryVisits : ℝ) ≤
      ((computedFamilyResult source target N input).requests : ℝ) *
        ((2 * (16384 * inputHeight N + 5 + 1) : ℕ) : ℝ) := by exact_mod_cast hd
  calc
    _ ≤ (((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) *
        (inputHeight N : ℝ) ^ 2 := hdR.trans (mul_le_mul hr hcR (by positivity)
          (mul_nonneg (by positivity) (computedWidthEnvelope_nonneg N)))
    _ ≤ ((inputHeight N : ℝ) ^ 92 * computedWidthEnvelope N) * (inputHeight N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower
        (computedWidthEnvelope_nonneg N)) (by positivity)
    _ = computedWidthEnvelope N * (inputHeight N : ℝ) ^ 94 := by
      rw [show (94 : ℕ) = 92 + 2 from rfl, pow_add]
      ring
    _ ≤ _ := hw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseExecution
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory

section Execution
variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

omit [NeZero M] [NeZero R] [NeZero B] in
 theorem physicalCoarseExecutionProjection_measurable :
    Measurable (physicalCoarseExecutionProjection (R := R) source target N P H B depth) := by
  unfold physicalCoarseExecutionProjection
  exact ((measurable_of_finite (physicalCoarseSeedTable source target N B depth)).comp
    measurable_fst).prodMk measurable_snd

omit [NeZero R] in
 theorem physicalCoarseExecutionProjection_law :
    (physicalCoarseExecutionLaw (R := R) source target N P H B depth).map
      (physicalCoarseExecutionProjection (R := R) source target N P H B depth) =
    physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth) := by
  unfold physicalCoarseExecutionLaw physicalCoarseExecutionProjection physicalFamilyRuntimeLaw
  change ((_ : Measure (PhysicalCoarseDraw source target B depth)).prod _).map
    (Prod.map (physicalCoarseSeedTable source target N B depth) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id, Measure.map_id]
  rfl

end Execution
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse sampler execution and its returned seed share one probability space. -/

namespace EditApproximation

open MeasureTheory








 theorem computedExecutionProjection_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionProjection source target N) :=
  physicalCoarseExecutionProjection_measurable source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)

 theorem computedExecutionProjection_law (source target : List ℕ) (N : ℕ) :
    (computedExecutionLaw source target N).map (computedExecutionProjection source target N) =
      physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) (physicalCoarseSeedLaw (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) source target N (integerParameters N).B
          (computedPhysicalCoarseDepth source target N)) :=
  physicalCoarseExecutionProjection_law source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter





 theorem computedFamilyRejectionWork_integrable (source target : List ℕ) (N : ℕ)
    (seed : ComputedFamilySeed source target N) :
    Integrable (fun execution : ComputedRejectionRuntime source target N =>
      computedFamilyRejectionWork source target N (seed, execution))
      (rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
        (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
        target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) :=
  physicalFamilyMemoBits_integrable source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (finalTargetState target.length) seed

 theorem computedExecutionRejectionWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      integral (computedExecutionLaw source target N) (computedExecutionRejectionWork source target N) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyRejectionWork_expected_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  let incoming := physicalCoarseSeedLaw (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) source target N
    (integerParameters N).B (computedPhysicalCoarseDepth source target N)
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    (computedExecutionProjection_measurable source target N).aemeasurable
    (measurable_of_countable (computedFamilyRejectionWork source target N)).aestronglyMeasurable
  rw [computedExecutionProjection_law] at hmap
  change (∫ execution, computedFamilyRejectionWork source target N
    (computedExecutionProjection source target N execution) ∂computedExecutionLaw source target N) ≤ _
  rw [← hmap]
  apply finite_outer_expected_le incoming _ (computedFamilyRejectionWork source target N)
    (computedFamilyRejectionWork_integrable source target N) _
  intro seed
  exact hN source target hsize seed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedAddressWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter



 theorem computedFamilyAddressWork_le (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyAddressWork source target N input ≤
      2 * (7 * intervalTreeDepth (integerParameters N).M source.length + 60) *
        (computedFamilyResult source target N input).requests :=
  rankedMemoAddressWork_le _ _ _ _ _ _
    (computedFamilyMemoCodeWithWork_cost source target N (inputHeight N ^ 2)) _ _

private theorem address_factor_bound (H J : ℕ) (hH : 100 ≤ H) (hJ : J ≤ H) :
    2 * (7 * J + 60) ≤ H ^ 2 := by nlinarith only [hH, hJ]

 theorem computedFamilyAddressWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      (computedFamilyAddressWork source target N input : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedFamilyResult_requests_near_linear (epsilon / 2) hh,
    fixed_height_power_subpolynomial 2 (epsilon / 2) hh,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hr hp hN hell
  intro source target hsize input
  have hdepth := computed_tree_depth_bound N source.length (by omega) (by omega) hell
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    nlinarith only [hdepth, hell]
  have hH : 100 ≤ inputHeight N := (by omega : 100 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  have hfactor := address_factor_bound (inputHeight N) _ hH hJ
  have ha := computedFamilyAddressWork_le source target N input
  have haR : (computedFamilyAddressWork source target N input : ℝ) ≤
      (inputHeight N : ℝ) ^ 2 * (computedFamilyResult source target N input).requests := by
    exact_mod_cast ha.trans (Nat.mul_le_mul_right _ hfactor)
  calc
    _ ≤ (inputHeight N : ℝ) ^ 2 * (computedFamilyResult source target N input).requests := haR
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul hp (hr source target hsize input) (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionCosts
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

 theorem computedExecutionRejectionWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionRejectionWork source target N) (computedExecutionLaw source target N) := by
  let incoming := physicalCoarseSeedLaw (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) source target N
    (integerParameters N).B (computedPhysicalCoarseDepth source target N)
  have hi : Integrable (computedFamilyRejectionWork source target N)
      (physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) incoming) :=
    finite_outer_integrable incoming _ (computedFamilyRejectionWork source target N)
      (computedFamilyRejectionWork_integrable source target N)
  have hj : Integrable (computedFamilyRejectionWork source target N)
      ((computedExecutionLaw source target N).map (computedExecutionProjection source target N)) := by
    rw [computedExecutionProjection_law]
    exact hi
  exact hj.comp_measurable (computedExecutionProjection_measurable source target N)

 theorem computedExecutionAccepted_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionAccepted source target N) := measurable_of_countable _

 theorem computedExecutionAcceptedWork_integrable (source target : List ℕ) (N : ℕ)
    (f : ComputedFamilyInput source target N → ℝ) :
    Integrable (f ∘ computedExecutionAccepted source target N) (computedExecutionLaw source target N) := by
  have hi : Integrable f ((computedExecutionLaw source target N).map
      (computedExecutionAccepted source target N)) := Integrable.of_finite
  exact hi.comp_measurable (computedExecutionAccepted_measurable source target N)



 theorem computedExecutionDictionaryWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionDictionaryWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyResult source target N input).dictionaryVisits)

 theorem computedExecutionDictionaryWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionDictionaryWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyResult_dictionary_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionDictionaryWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp



 theorem computedExecutionAddressWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionAddressWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyAddressWork source target N input : ℝ))

 theorem computedExecutionAddressWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionAddressWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyAddressWork_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionAddressWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp

 theorem constant_le_rpow_eventually (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N + 2 : ℝ) ^ epsilon := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop hepsilon).comp ht).eventually (eventually_ge_atTop C)

 theorem computedExecutionNonlocalWork_expected_near_linear_oai (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionNonlocalWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarseWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionRejectionWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionDictionaryWork_expected_near_linear (epsilon / 2) hhalf,
    computedExecutionAddressWork_expected_near_linear (epsilon / 2) hhalf,
    constant_le_rpow_eventually 4 (epsilon / 2) hhalf] with N hc hr hd ha hfour
  intro source target hsize
  have hiC := computedExecutionCoarseWork_integrable source target N
  have hiR := computedExecutionRejectionWork_integrable source target N
  have hiD := computedExecutionDictionaryWork_integrable source target N
  have hiA := computedExecutionAddressWork_integrable source target N
  change integral (computedExecutionLaw source target N)
    (((computedExecutionCoarseWork source target N + computedExecutionRejectionWork source target N) +
      computedExecutionDictionaryWork source target N) + computedExecutionAddressWork source target N) ≤ _
  rw [integral_add' ((hiC.add hiR).add hiD) hiA, integral_add' (hiC.add hiR) hiD,
    integral_add' hiC hiR]
  calc
    _ ≤ 4 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hc source target hsize, hr source target hsize, hd source target hsize,
        ha source target hsize]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear_oai := @OAI.EditApproximation.computedExecutionNonlocalWork_expected_near_linear_oai

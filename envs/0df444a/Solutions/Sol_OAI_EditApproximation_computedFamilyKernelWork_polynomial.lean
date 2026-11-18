-- Prove2me | solution 1 for OAI.EditApproximation.computedFamilyKernelWork_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:21.97366+00:00
-- url     : https://prove2.me/submissions/d149feef-ecf3-42f0-86f1-92d462ae3909

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_near_linear

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

theorem computed_branching_square_le_height (N : ℕ) :
    ((integerParameters N).M : ℝ) ^ 2 ≤ inputHeight N := by
  have hexponent : heightExponent N / 20 * 2 ≤ heightExponent N := by omega
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using h

/-- This directly controls the scalar exponent `M q ell` occurring in the
local wide-action enumeration. -/
theorem branching_smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => Real.sqrt
      ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (smallLog_polynomial_div_height_tendsto (2 * k)).sqrt
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) _ hupper
  apply Eventually.of_forall
  intro N
  apply Real.le_sqrt_of_sq_le
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hM := computed_branching_square_le_height N
  have hproduct := mul_le_mul_of_nonneg_right hM
    (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) (2 * k))
  rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]
  apply (div_le_iff₀ (sq_pos_of_pos hH)).2
  calc
    ((integerParameters N).M : ℝ) ^ 2 * (inputSmallLog N : ℝ) ^ (2 * k) ≤
        (inputHeight N : ℝ) * (inputSmallLog N : ℝ) ^ (2 * k) := hproduct
    _ = ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N) *
        (inputHeight N : ℝ) ^ 2 := by field_simp [hH.ne']

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

theorem local_enumeration_exponent_div_height_tendsto :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N / inputHeight N)
      atTop (𝓝 0) := by
  have hupper := (branching_smallLog_polynomial_div_height_tendsto 2).const_mul 2
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
  apply Eventually.of_forall
  intro N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (inputSmallLog N)))
    (Nat.cast_nonneg (integerParameters N).M)
  have hdiv := div_le_div_of_nonneg_right hprod (Nat.cast_nonneg (inputHeight N))
  first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Count local arithmetic only on a cache miss, following exactly the
recursive evaluator's returned values, requests and intermediate memories. -/


 theorem rankedMemoKernelWork_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (C : ℕ) (hcost : ∀ key, cost key ≤ C)
    (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoKernelWork rank program bits encode cost key memory ≤
      C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoKernelWork rank program bits encode cost key memory ≤
        C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoKernelWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only
        exact Nat.zero_le _
      · rename_i hfound
        simp only
        have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            rankedMemoKernelWork rank program bits encode cost child.val previous ≤
              C * (rankedMemoEvaluate rank program bits encode child.val previous).requests := by
          intro child previous
          exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
        have hr := FiniteQuery.requestWork_le
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoKernelWork rank program bits encode cost child.val previous)
          C hchildren (program key) memory
        have hk := hcost key
        rw [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedLocalKernelWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 theorem computedLocalKernelExponent_tendsto (D : ℕ) :
    Tendsto (fun N => computedLocalKernelExponent D N / inputHeight N) atTop (𝓝 0) := by
  have h := ((local_enumeration_exponent_div_height_tendsto.const_mul (100 * Real.log 2)).add
    (encoding_exponent_div_height_tendsto.const_mul 100000)).const_mul (D : ℝ)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  unfold computedLocalKernelExponent
  ring

private theorem localKernelBudget_exp_scalar (D H M p ell : ℕ) (hH : 0 < H)
    (hlog : Real.log (H : ℝ) ≤ (ell : ℝ) * Real.log 2) :
    ((H ^ localKernelPowerExponent M p D : ℕ) : ℝ) ≤
      Real.exp ((D : ℝ) * ((100 * Real.log 2) * (M : ℝ) * ((p : ℝ) + 1) * ell +
        100000 * ((p : ℝ) + 1) * Real.log (H : ℝ))) := by
  rw [Nat.cast_pow, nat_pow_eq_exp_log H _ hH]
  apply Real.exp_le_exp.mpr
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hM) hp)
  have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  unfold localKernelPowerExponent
  push_cast
  nlinarith only [mul_nonneg hD (sub_nonneg.mpr hmul)]

 theorem computedLocalKernelBudget_exp_bound (D N : ℕ) (hN : 0 < N) :
    (computedLocalKernelBudget D N : ℝ) ≤ Real.exp (computedLocalKernelExponent D N) := by
  have hlog : Real.log (inputHeight N : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [inputHeight_real_log]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (inputSmallLog_bounds N hN).1)
      (Real.log_nonneg (by norm_num))
  exact localKernelBudget_exp_scalar D (inputHeight N) (integerParameters N).M
    (coarseExponent (inputSmallLog N)) (inputSmallLog N) (Nat.two_pow_pos _) hlog

 theorem computedLocalKernelBudget_subpolynomial (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, (computedLocalKernelBudget D N : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input (computedLocalKernelExponent D)
    (computedLocalKernelExponent_tendsto D) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (computedLocalKernelBudget_exp_bound D N (by omega)).trans he

 theorem computedLocalKernelBudget_requests_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) * computedLocalKernelBudget D N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedFamilyResult_requests_near_linear (epsilon / 2) hh,
    computedLocalKernelBudget_subpolynomial D (epsilon / 2) hh] with N hr hk
  intro source target hsize input
  calc
    _ ≤ (N + 2 : ℝ) ^ (1 + epsilon / 2) * (N + 2 : ℝ) ^ (epsilon / 2) :=
      mul_le_mul (hr source target hsize input) hk (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedKernelWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter



/-- Local arithmetic annotations follow the actual memo run, hence are
incurred once per cache miss, with the original program and draw values. -/


theorem computedFamilyKernelWork_le (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N)
    (cost : ComputedFamilyMemoKey source target N → ℕ) (C : ℕ)
    (hcost : ∀ key, cost key ≤ C) :
    computedFamilyKernelWork source target N input cost ≤
      C * (computedFamilyResult source target N input).requests :=
  rankedMemoKernelWork_le _ _ _ _ cost C hcost _ _

theorem computedFamilyKernelWork_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      (computedFamilyKernelWork source target N input cost : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedLocalKernelBudget_requests_near_linear D epsilon hepsilon] with N hN
  intro source target hsize input cost hcost
  have h := computedFamilyKernelWork_le source target N input cost
    (computedLocalKernelBudget D N) hcost
  have hr : (computedFamilyKernelWork source target N input cost : ℝ) ≤
      (computedLocalKernelBudget D N : ℝ) * (computedFamilyResult source target N input).requests := by
    exact_mod_cast h
  exact hr.trans (by simpa only [mul_comm] using hN source target hsize input)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBaseStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedFamilyKernelWork_polynomial_oai (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      computedFamilyKernelWork source target N input cost ≤ (N + 2) ^ 2 := by
  filter_upwards [computedFamilyKernelWork_near_linear D 1 (by norm_num)] with N hN
  intro source target hsize input cost hcost
  have h := hN source target hsize input cost hcost
  norm_num at h
  exact_mod_cast h

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedFamilyKernelWork_polynomial_oai := @OAI.EditApproximation.computedFamilyKernelWork_polynomial_oai

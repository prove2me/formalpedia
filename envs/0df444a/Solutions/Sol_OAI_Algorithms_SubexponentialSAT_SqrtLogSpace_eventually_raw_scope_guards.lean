-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:58:23.663816+00:00
-- url     : https://prove2.me/submissions/bf92af8b-2afb-42e7-83b1-75214daaca12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S075
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_forwardHighMask_guards
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_sparse_parameter_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeResourceBounds_measured_polylog

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Incidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq E] in
/-- Counting incidences by coordinates or by factors gives the same result. -/
theorem sum_degrees [Fintype V] (scope : E → Finset V) :
    ∑ v, degree scope v = ∑ e, (scope e).card := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

end SubexponentialSAT.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRuntime
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform runtime assembly with growing layout parameters

Unlike the older fixed-width-exponent accounting, all layout parameters are
input-dependent here. `GrowingParameters.entries` exposes every argument of
the polynomial costs in Proposition 4.2 and the layout construction. The
analytic lemmas also pay for the variable-degree sunflower search.

Only the purely numerical work/trace infrastructure from `RuntimeAssembly`
is reused; none of its fixed-prime or exponent-0.9 estimates is used.
-/

namespace SubexponentialSAT.SubexpRuntime

open Filter
open scoped Topology

noncomputable section

/-- Any fixed power of log is eventually dominated by the input size, with
an arbitrary fixed positive coefficient and the source's shift by sixteen. -/
theorem eventually_logb_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℝ in atTop, C * (Real.logb 2 (n + 16)) ^ q ≤ n := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (Real.log (2 : ℝ)) ^ q := pow_pos hl q
  have ht : Tendsto (fun n : ℝ => n + 16) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := q)).bound
    (show 0 < (Real.log (2 : ℝ)) ^ q / (2 * C) by positivity)
  filter_upwards [ht.eventually hsmall, eventually_ge_atTop (16 : ℝ)] with n hb hn
  have hn0 : 0 ≤ n + 16 := by linarith
  have hlog0 : 0 ≤ Real.log (n + 16) := Real.log_nonneg (by linarith)
  have hb' : (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16) := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 q), abs_of_nonneg hn0] using hb
  have hmul : C * (Real.log (n + 16)) ^ q ≤
      (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
    calc
      C * (Real.log (n + 16)) ^ q ≤
          C * ((Real.log (2 : ℝ)) ^ q / (2 * C) * (n + 16)) :=
        mul_le_mul_of_nonneg_left hb' hC.le
      _ = (Real.log (2 : ℝ)) ^ q * ((n + 16) / 2) := by
        field_simp
  calc
    C * (Real.logb 2 (n + 16)) ^ q =
        (C * (Real.log (n + 16)) ^ q) / (Real.log (2 : ℝ)) ^ q := by
      unfold Real.logb
      rw [div_pow]
      ring
    _ ≤ (n + 16) / 2 := (div_le_iff₀ hp).mpr (by nlinarith [hmul])
    _ ≤ n := by linarith

end
end SubexponentialSAT.SubexpRuntime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; omega

theorem le_s_iff (n a : ℕ) : a ≤ s n ↔ a ^ 2 * w n ^ 4 ≤ L n := by
  rw [s, Nat.le_div_iff_mul_le (pow_pos (w_pos n) 2), Nat.le_sqrt']
  ring_nf

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem two_le_logLogSize (n : ℕ) : 2 ≤ logLogSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by have := four_le_logSize n; linarith : 0 < logSize n)).mpr
  norm_num
  exact four_le_logSize n

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

theorem L_le_logSize_add_one (n : ℕ) : (L n : ℝ) ≤ logSize n + 1 := by
  have h := Real.natLog_le_logb (n + 16) 2
  simpa [L, logSize, Nat.log2_eq_log_two, Nat.cast_add] using add_le_add_right h 1

theorem L_le_twice_logSize (n : ℕ) : (L n : ℝ) ≤ 2 * logSize n := by
  have := L_le_logSize_add_one n
  have := four_le_logSize n
  linarith

theorem w_le_twice_logLogSize (n : ℕ) : (w n : ℝ) ≤ 2 * logLogSize n := by
  have hp : (0 : ℝ) < logSize n := by have := four_le_logSize n; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hn := Real.natLog_le_logb (L n) 2
  have hlog : Real.logb 2 (L n : ℝ) ≤ 1 + logLogSize n := by
    calc
      Real.logb 2 (L n : ℝ) ≤ Real.logb 2 (2 * logSize n) :=
        Real.logb_le_logb_of_le (by norm_num) hL (L_le_twice_logSize n)
      _ = 1 + logLogSize n := by
        rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne']
        norm_num [logLogSize]
  have hw : (w n : ℝ) ≤ Real.logb 2 (L n : ℝ) + 1 := by
    simpa [w, Nat.log2_eq_log_two] using add_le_add_right hn 1
  have := two_le_logLogSize n
  linarith

theorem logSize_tendsto : Tendsto logSize atTop atTop := by
  exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)

theorem eventually_le_s (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ s n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le 4
      (show (0 : ℝ) < ((a : ℝ) + 1) ^ 2 * 16 by positivity))
  filter_upwards [hb] with n hn
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) := by
    have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
      Real.logb_le_logb_of_le (by norm_num)
        (by have := four_le_logSize n; linarith) (by linarith)
    exact (w_le_twice_logLogSize n).trans (by linarith)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ w n by positivity) hw 4
  have ha : (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤ (L n : ℝ) := by
    calc
      (a : ℝ) ^ 2 * (w n : ℝ) ^ 4 ≤
          ((a : ℝ) + 1) ^ 2 * (2 * Real.logb 2 (logSize n + 16)) ^ 4 := by
        apply mul_le_mul
        · nlinarith [Nat.cast_nonneg (α := ℝ) a]
        · exact hp
        · positivity
        · positivity
      _ = (((a : ℝ) + 1) ^ 2 * 16) * Real.logb 2 (logSize n + 16) ^ 4 := by ring_nf
      _ ≤ logSize n := hn
      _ ≤ (L n : ℝ) := (logSize_lt_L n).le
  exact (le_s_iff n a).mpr (by exact_mod_cast ha)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutRate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_L_ge (a : ℕ) : ∀ᶠ n : ℕ in atTop, a ≤ L n := by
  filter_upwards [eventually_le_s a] with n hn
  exact hn.trans (s_le_L n)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticResidual
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform transport from the original dimension to a residual dimension
between one half and all of it. No lower bound on arbitrary residuals is
assumed: callers must supply the displayed half-dimension condition. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem L_le_succ_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ L m + 1 := by
  have harg : n + 16 ≤ (m + 16) * 2 := by omega
  have h := Nat.log_mono_right (b := 2) harg
  rw [Nat.log_mul_base (by norm_num : 1 < (2 : ℕ)) (by omega : m + 16 ≠ 0)] at h
  simpa [L, Nat.log2_eq_log_two, Nat.add_assoc] using Nat.add_le_add_right h 1

theorem L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ 2 * L m := by
  have := L_le_succ_of_half hnm
  have := L_pos m
  omega

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

/-- A fixed polynomial bound in the original logarithm is still a fixed
polynomial bound in every half-size residual logarithm. -/
theorem eventually_residual_polynomial (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, n ≤ 2 * m →
      b ≤ C * L n ^ q → b ≤ L m ^ (q + 1) := by
  filter_upwards [eventually_uniform_half (eventually_L_ge (C * 2 ^ q))] with n hn m b hnm hb
  have hC := hn m hnm
  calc
    b ≤ C * L n ^ q := hb
    _ ≤ C * (2 * L m) ^ q := by gcongr; exact L_le_twice_of_half hnm
    _ = (C * 2 ^ q) * L m ^ q := by rw [mul_pow]; ring
    _ ≤ L m * L m ^ q := Nat.mul_le_mul_right _ hC
    _ = _ := by rw [pow_succ]; ring

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem high_mass_le (scope : E → Finset V) (cut : ℕ) :
    (high scope cut).card * (cut + 1) ≤ totalScope scope := by
  calc
    _ = ∑ _v ∈ high scope cut, (cut + 1) := by simp
    _ ≤ ∑ v ∈ high scope cut, Incidence.degree scope v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, Incidence.degree scope v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = totalScope scope := Incidence.sum_degrees scope

omit [DecidableEq E] in
theorem high_card_mul_le (scope : E → Finset V) (cut t : ℕ)
    (hbudget : totalScope scope * t ≤ Fintype.card V * cut) :
    (high scope cut).card * t ≤ Fintype.card V := by
  have hm := high_mass_le scope cut
  have hmul := Nat.mul_le_mul_right t hm
  by_cases hc : cut = 0
  · simp only [hc, Nat.mul_zero] at hbudget
    have hh : (high scope cut).card ≤ totalScope scope := by nlinarith
    have := (Nat.mul_le_mul_right t hh).trans hbudget
    omega
  · have hp : 0 < cut := Nat.pos_of_ne_zero hc
    have hsmall : (high scope cut).card * t * cut ≤ Fintype.card V * cut := by
      nlinarith
    exact Nat.le_of_mul_le_mul_right hsmall hp

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PaddedCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

open SubexponentialSAT.LocalExpectation
open SubexponentialSAT.Subexp.LocalExpectation

variable {I W J : Type*} [DecidableEq I]

theorem trueCount_eq_count (bs : List Bool) :
    trueCount bs = bs.count true := by
  have h : (fun b : Bool => b == true) = id := by
    funext b
    cases b <;> rfl
  simp only [List.count_eq_countP, List.countP_eq_length_filter, h,
    trueCount, successful]

end SubexponentialSAT.Subexp.PaddedCompletion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

theorem totals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free + scanSum (fun _ => 1) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_uncovered (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).uncovered =
      t.uncovered + scanSum (fun i => if degree scopes i = 0 then 1 else 0) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem scanSum_eq_free_sum (f : ℕ → ℕ) (mask : List Bool) :
    scanSum f 0 mask = ∑ i : Free mask, f i.val.val := by
  unfold scanSum
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin mask.length => i ∉ highMask mask), f i.val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_highMask, List.get_eq_getElem]
      by_cases hb : mask[i.val] = true <;> simp [hb]
    _ = _ := Finset.sum_subtype _ (by intro i; simp) _

theorem free_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).free = Fintype.card (Free mask) := by
  rw [totals_free, scanSum_eq_free_sum]
  simp [zero]

theorem uncovered_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).uncovered = (uncovered (residualScope scopes mask)).card := by
  rw [totals_uncovered, scanSum_eq_free_sum]
  simp [zero, uncovered]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

theorem free_le_ambient (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free ≤ mask.length := by
  rw [measured, free_exact]
  simp

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

theorem highPrefix_trueCount (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      ∑ v ∈ Finset.range n, if cut < degree scopes v then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : cut < degree scopes n
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using ih

theorem highPrefix_count_eq_card (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      (HighIncidence.high (suppliedScope n scopes) cut).card := by
  rw [highPrefix_trueCount, Finset.sum_range]
  simp only [HighIncidence.high, Finset.card_eq_sum_ones, Finset.sum_filter,
    degree_suppliedScope]


/-- Even nonnormalized supplied records overcount rather than undercount mass.
This suffices for the high-dimension bound with the physically counted S. -/
theorem suppliedScope_card_le (n : ℕ) (scopes : List (List ℕ)) (e : Fin scopes.length) :
    (suppliedScope n scopes e).card ≤ (scopes.get e).length := by
  have hi : (suppliedScope n scopes e).image Fin.val ⊆ (scopes.get e).toFinset := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((Subexp.IncidencePlanSpec.mem_pattern_scope n scopes v e).mp hv)
  calc
    _ = ((suppliedScope n scopes e).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (scopes.get e).toFinset.card := Finset.card_le_card hi
    _ ≤ (scopes.get e).length := List.toFinset_card_le _

theorem suppliedScope_mass_le (n : ℕ) (scopes : List (List ℕ)) :
    HighIncidence.totalScope (suppliedScope n scopes) ≤ (scopes.map List.length).sum := by
  calc
    _ ≤ ∑ e : Fin scopes.length, (scopes.get e).length :=
      Finset.sum_le_sum (fun e _ => suppliedScope_card_le n scopes e)
    _ = (scopes.map List.length).sum := by
      rw [← Fin.sum_ofFn]
      change (List.ofFn (List.length ∘ scopes.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]

/-- The threshold may be computed from raw entry counts. Duplicates or
out-of-range supplied IDs cannot invalidate the dimension estimate. -/
theorem computed_high_dimension_rawMass (scopes : List (List ℕ)) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    Branches.trueCount
      (highPrefix scopes (((scopes.map List.length).sum * t) ⌈/⌉ n) n) ≤ n / t := by
  rw [highPrefix_count_eq_card]
  apply (Nat.le_div_iff_mul_le ht).mpr
  have hb : HighIncidence.totalScope (suppliedScope n scopes) * t ≤
      n * (((scopes.map List.length).sum * t) ⌈/⌉ n) := by
    calc
      _ ≤ (scopes.map List.length).sum * t := Nat.mul_le_mul_right _ (suppliedScope_mass_le n scopes)
      _ ≤ n * (((scopes.map List.length).sum * t) ⌈/⌉ n) :=
        (ceilDiv_le_iff_le_mul hn).mp le_rfl
  simpa only [Fintype.card_fin] using HighIncidence.high_card_mul_le
    (suppliedScope n scopes) (((scopes.map List.length).sum * t) ⌈/⌉ n) t (by simpa using hb)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyHighMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Guard success for the actual forward mask computed from all supplied raw
scopes.  The high cutoff counts raw entries, including harmless overcounts. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafStatisticsSemantics HighIncidenceProgram

private theorem scanSum_ones_eq_count (mask : List Bool) (v : ℕ) :
    scanSum (fun _ => 1) v mask = mask.count false := by
  induction mask generalizing v with
  | nil => simp
  | cons b bs ih => cases b <;> simp [scanSum_cons, ih, Nat.add_comm]

theorem measured_free_eq_false_count (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free = mask.count false := by
  simp only [measured, totals_free, LeafStatisticsSemantics.zero, Nat.zero_add]
  exact scanSum_ones_eq_count mask 0

private theorem count_bool_partition (mask : List Bool) :
    mask.count false + mask.count true = mask.length := by
  induction mask with
  | nil => simp
  | cons b bs ih => cases b <;> simp [] <;> omega

theorem measured_highPrefix_free (scopes : List (List ℕ)) (cut n : ℕ) :
    (measured scopes (highPrefix scopes cut n).reverse).free =
      n - Branches.trueCount (highPrefix scopes cut n) := by
  rw [measured_free_eq_false_count, List.count_reverse]
  have hc := count_bool_partition (highPrefix scopes cut n)
  have hl := highPrefix_length scopes cut n
  have ht := Subexp.PaddedCompletion.trueCount_eq_count (highPrefix scopes cut n)
  change Branches.trueCount (highPrefix scopes cut n) =
    (highPrefix scopes cut n).count true at ht
  omega

theorem forwardHighMask_length (scopes : List (List ℕ)) (n τ : ℕ) :
    (forwardHighMask scopes n τ).length = n := by
  simp [forwardHighMask]

theorem forwardHighMask_retains_half (scopes : List (List ℕ)) (n τ : ℕ)
    (hn : 0 < n) (hτ : 2 ≤ τ) :
    n ≤ 2*(measured scopes (forwardHighMask scopes n τ)).free := by
  have hpos : 0 < τ := by omega
  have h := computed_high_dimension_rawMass scopes n τ hn hpos
  have hm := (Nat.le_div_iff_mul_le hpos).mp h
  have ht := Nat.mul_le_mul_left
    (Branches.trueCount (highPrefix scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n)) hτ
  have he := measured_highPrefix_free scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n
  change (measured scopes (forwardHighMask scopes n τ)).free = _ at he
  omega

theorem highThreshold_ge_two (n : ℕ) : 2 ≤ Nat.sqrt (Asymptotic.L n)+1 := by
  have h := Nat.sqrt_pos.mpr (Asymptotic.L_pos n)
  omega

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsStatistics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Upper bounds for the actual measured statistics. The mask is the forward
reverse of the physical descending high-prefix stream. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram LeafStatisticsSemantics

theorem measured_uncovered_le (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).uncovered ≤ mask.length := by
  rw [measured, uncovered_exact]
  apply (Finset.card_le_univ _).trans
  simp

theorem measured_factors_le (scopes : List (List ℕ)) (mask : List Bool) :
    scopes.length + (measured scopes mask).uncovered ≤ scopes.length + mask.length :=
  Nat.add_le_add_left (measured_uncovered_le scopes mask) _

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryScopeBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.LeafStatisticsProgram
open SqrtLog.LeafScopeResourceBounds SqrtLog.CostAssembly
open scoped Topology

/-- Raw retained scope resources suffice for every guard. This theorem is
independent of candidate order or an old materialized selector history. -/
theorem eventually_raw_scope_guards_oai (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (m B : ℕ),
      0 < m → m ≤ n * B → B ≤ L n ^ qi →
      scopes.length ≤ 3 * n + HashSelect.loopCap n m + 2 →
      HighIncidenceProgram.Prepare.mass scopes ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k →
      (∀ row ∈ scopes, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) →
      (∀ row ∈ scopes, row.Nodup) →
      let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
      let x := measuredParameterInput scopes mask m k
      LeafParametersProgram.Guard x ∧ x.freeCount ≤ n ∧ n ≤ 2 * x.freeCount ∧
        x.factors ≤ 4 * n + HashSelect.loopCap n m + 2 ∧
        x.occurrence ≤ L x.freeCount ^ (resourceExponent qi + 1) ∧
        x.arity ≤ L x.freeCount ^ (resourceExponent qi + 1) := by
  filter_upwards [eventually_forwardHighMask_guards (statCoefficient k qi) (resourceExponent qi),
    eventually_sparse_parameter_bounds qi,
    eventually_residual_polynomial (statCoefficient k qi) (resourceExponent qi),
    eventually_ge_atTop (1 : ℕ)] with n hguard hparameters hpoly hn scopes m B hm hmb hB hlen hmass har hnd
  let mask := forwardHighMask scopes n (Nat.sqrt (L n) + 1)
  have hmask : forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes n.bits
      (Nat.sqrt (L n) + 1).bits) n = mask := by
    simp [mask, forwardMask, forwardHighMask, HighIncidenceProgram.Prepare.cut,
      HighIncidenceProgram.Prepare.mass, ArithmeticExpressionSupport.bits_value]
  have hs := measured_polylog n m B k qi (by omega) hmb hB
    (hparameters m B hmb hB).1 scopes n.bits (Nat.sqrt (L n) + 1).bits
    (ArithmeticExpressionSupport.bits_value n) (ArithmeticExpressionSupport.bits_value _)
    hmass har
  rw [hmask] at hs
  have hfree : (measured scopes mask).free ≤ n :=
    (LeafStatisticsProgram.free_le_ambient scopes mask).trans_eq
      (forwardHighMask_length scopes n _)
  have hhalf : n ≤ 2 * (measured scopes mask).free :=
    forwardHighMask_retains_half scopes n _ (by omega) (highThreshold_ge_two n)
  have hfac := measured_factors_le scopes mask
  rw [forwardHighMask_length] at hfac
  refine ⟨hguard scopes m k hm hnd hs.1 hs.2, hfree, hhalf, ?_,
    hpoly _ _ hhalf hs.1, hpoly _ _ hhalf hs.2⟩
  change scopes.length + (measured scopes mask).uncovered ≤ _
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards_oai

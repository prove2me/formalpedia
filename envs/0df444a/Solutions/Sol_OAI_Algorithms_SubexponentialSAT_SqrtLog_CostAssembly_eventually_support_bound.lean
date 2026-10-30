-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:45:51.823095+00:00
-- url     : https://prove2.me/submissions/48c007a4-5409-4a1d-b1e8-d7a22b901779

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S030

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BranchTree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Counting binary branch-tree paths

False labels an A edge and true labels a B edge. A word is encoded injectively
by its length and the finite set of positions occupied by B. This proves the
finite counting step in Appendix A.3 without any analytic hypotheses.
-/

namespace SubexponentialSAT.BranchTree

/-- A uniform binomial estimate valid at a real, not necessarily integral, cutoff. -/
theorem choose_le_rpow_real (D r : ℕ) {q : ℝ} (hq : 0 < q)
    (hD : q ≤ D) (hr : (r : ℝ) ≤ q) :
    (D.choose r : ℝ) ≤ (4 * (D : ℝ) / q) ^ q := by
  have hbase : 1 ≤ (D : ℝ) / q := (le_div_iff₀ hq).2 (by simpa using hD)
  have hbasenonneg : 0 ≤ (D : ℝ) / q := le_trans zero_le_one hbase
  have hsplit : (D : ℝ) ^ r / (r.factorial : ℝ) =
      ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := by
    rw [div_pow]
    field_simp
  have hpow : ((D : ℝ) / q) ^ r ≤ ((D : ℝ) / q) ^ q := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hbase hr)
  have hexp : Real.exp q ≤ (4 : ℝ) ^ q := by
    rw [← Real.exp_one_rpow]
    exact Real.rpow_le_rpow (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) hq.le
  calc
    (D.choose r : ℝ) ≤ (D : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r D
    _ = ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := hsplit
    _ ≤ ((D : ℝ) / q) ^ r * Real.exp q :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp q hq.le r)
        (pow_nonneg hbasenonneg r)
    _ ≤ ((D : ℝ) / q) ^ q * Real.exp q :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg q)
    _ ≤ ((D : ℝ) / q) ^ q * (4 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hbasenonneg _)
    _ = (4 * (D : ℝ) / q) ^ q := by
      rw [← Real.mul_rpow hbasenonneg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

end SubexponentialSAT.BranchTree

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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticOverhead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Absorption of all fixed polylogarithmic exponents. The quantifiers keep
the power and multiplicative constant independent of the input size. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_w_power_le_L (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (w n : ℝ) ^ q ≤ L n := by
  have hb := logSize_tendsto.eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  have hm : logLogSize n ≤ Real.logb 2 (logSize n + 16) :=
    Real.logb_le_logb_of_le (by norm_num)
      (by have := four_le_logSize n; linarith) (by linarith)
  have hw : (w n : ℝ) ≤ 2 * Real.logb 2 (logSize n + 16) :=
    (w_le_twice_logLogSize n).trans (by linarith)
  calc
    C * (w n : ℝ) ^ q ≤ C * (2 * Real.logb 2 (logSize n + 16)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw q) hC.le
    _ = (C * (2 : ℝ) ^ q) * Real.logb 2 (logSize n + 16) ^ q := by
      rw [mul_pow]; ring
    _ ≤ logSize n := hn
    _ ≤ L n := (logSize_lt_L n).le

theorem eventually_logSize_power_le (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * logSize n ^ q ≤ binaryScale n := by
  have hmain := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le (q + 1) hC)
  filter_upwards [hmain] with n hn
  have ht := four_le_logSize n
  have hW := two_le_logLogSize n
  have ht0 : 0 < Real.sqrt (logSize n) := Real.sqrt_pos.2 (by linarith)
  have hroot : Real.sqrt (logSize n) ≤ logSize n := by
    apply Real.sqrt_le_iff.2
    constructor <;> nlinarith
  have hprod : C * logSize n ^ q * Real.sqrt (logSize n) ≤
      (n : ℝ) * logLogSize n ^ 2 := by
    calc
      C * logSize n ^ q * Real.sqrt (logSize n) ≤
          C * logSize n ^ q * logSize n :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = C * logSize n ^ (q + 1) := by rw [pow_succ]; ring
      _ ≤ n := hn
      _ ≤ (n : ℝ) * logLogSize n ^ 2 := by
        have := Nat.cast_nonneg (α := ℝ) n
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
          (show 0 ≤ logLogSize n ^ 2 - 1 by nlinarith)]
  exact (le_div_iff₀ ht0).2 hprod

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The exact square-root-logarithm runtime scale

These are numerical definitions and elementary lemmas only.  In particular,
this module supplies no SAT algorithm and makes no computational existence claim.
The logarithms in the target are natural logarithms, including at small inputs.
-/

namespace SubexponentialSAT.SqrtLog.Statement

noncomputable section

theorem two_le_log_shift (n : ℕ) : 2 ≤ Real.log ((n : ℝ) + 16) := by
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hpow := Real.log_pow (2 : ℝ) 4
  norm_num at hpow
  have hmon : Real.log 16 ≤ Real.log ((n : ℝ) + 16) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  linarith

theorem log_shift_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 16) := by
  have := two_le_log_shift n
  linarith

theorem sqrt_log_shift_pos (n : ℕ) : 0 < Real.sqrt (Real.log ((n : ℝ) + 16)) :=
  Real.sqrt_pos.2 (log_shift_pos n)

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Conversion to the exact natural-logarithm target and absorption of
fixed polylogarithmic construction, search, and arithmetic overheads. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem log_two_bounds : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

theorem logSize_natural_bounds (n : ℕ) :
    Real.log ((n : ℝ) + 16) ≤ logSize n ∧
      logSize n ≤ 2 * Real.log ((n : ℝ) + 16) := by
  have hpos := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  unfold logSize Real.logb
  constructor
  · apply (le_div_iff₀ htwo).2
    nlinarith
  · apply (div_le_iff₀ htwo).2
    nlinarith

theorem logLogSize_le_natural (n : ℕ) :
    logLogSize n ≤ 4 * Real.log (Real.log ((n : ℝ) + 16)) := by
  have ha := Statement.two_le_log_shift n
  have hap := Statement.log_shift_pos n
  have hb := log_two_bounds
  have htwo : 0 < Real.log (2 : ℝ) := by linarith
  have hlog : Real.log 2 ≤ Real.log (Real.log ((n : ℝ) + 16)) :=
    Real.log_le_log (by norm_num) ha
  have ht : 0 < logSize n := by have := four_le_logSize n; linarith
  have htlog : Real.log (logSize n) ≤
      Real.log 2 + Real.log (Real.log ((n : ℝ) + 16)) := by
    calc
      Real.log (logSize n) ≤ Real.log (2 * Real.log ((n : ℝ) + 16)) :=
        Real.log_le_log ht (logSize_natural_bounds n).2
      _ = _ := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hap.ne'
  unfold logLogSize Real.logb
  apply (div_le_iff₀ htwo).2
  nlinarith

theorem binaryScale_le_target (n : ℕ) :
    binaryScale n ≤ 16 * Statement.runtimeScale n := by
  have hW := logLogSize_le_natural n
  have hW0 : 0 ≤ logLogSize n := by have := two_le_logLogSize n; linarith
  have hroot := Real.sqrt_le_sqrt (logSize_natural_bounds n).1
  have ha := Statement.sqrt_log_shift_pos n
  have hb : 0 < Real.sqrt (logSize n) := by linarith
  have hsq : logLogSize n ^ 2 ≤
      16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 := by nlinarith
  unfold binaryScale Statement.runtimeScale
  calc
    (n : ℝ) * logLogSize n ^ 2 / Real.sqrt (logSize n) ≤
        (n : ℝ) * (16 * Real.log (Real.log ((n : ℝ) + 16)) ^ 2) /
          Real.sqrt (Real.log ((n : ℝ) + 16)) := by gcongr
    _ = _ := by ring

theorem eventually_polylog_le_target (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * logSize n ^ q ≤ Statement.runtimeScale n := by
  filter_upwards [eventually_logSize_power_le q (show 0 < 16 * C by positivity)] with n hn
  have h := binaryScale_le_target n
  nlinarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact squarefree support entropy at the square-root-log scale.  The
hypothesis on J is a numerical jet-order bound, not a support-count oracle. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology BigOperators
open Asymptotic

/-- The extra logarithm in support entropy is exactly the second w factor. -/
theorem weighted_scale_le_target (n : ℕ) :
    (n : ℝ) * (w n : ℝ)^2 / Real.sqrt (L n : ℝ) ≤
      64 * Statement.runtimeScale n := by
  have ht := four_le_logSize n
  have hroots : Real.sqrt (logSize n) ≤ Real.sqrt (L n : ℝ) :=
    Real.sqrt_le_sqrt (logSize_lt_L n).le
  have hw := w_le_twice_logLogSize n
  have hfirst : (n : ℝ) * (w n : ℝ)^2 / Real.sqrt (L n : ℝ) ≤
      4 * binaryScale n := by
    calc
      _ ≤ (n : ℝ) * (2 * logLogSize n)^2 / Real.sqrt (logSize n) := by
        gcongr
      _ = _ := by unfold binaryScale; ring
  linarith [binaryScale_le_target n]

theorem log_four_L_le (n : ℕ) :
    Real.log (4 * (L n : ℝ)) ≤ 3 * (w n : ℝ) := by
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hlog : Real.log (L n : ℝ) ≤ (w n : ℝ) := by
    have h := SubexpExponentArithmetic.logb_lt_natLog2_add_one (L n)
    have h' : Real.log (L n : ℝ) / Real.log 2 < (w n : ℝ) := by
      simpa [Real.logb, w, Nat.cast_add, Nat.cast_one] using h
    have h2 := log_two_bounds
    have hmul := (div_lt_iff₀ (show 0 < Real.log 2 by linarith)).mp h'
    nlinarith
  have hfour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [log_two_bounds]
  rw [Real.log_mul (by norm_num) hL.ne']
  linarith

/-- Pointwise entropy bound, using any positive real upper cutoff. -/
theorem support_le_entropy (n J : ℕ) {u : ℝ}
    (hu : 0 < u) (hun : u ≤ n) (hJu : (J : ℝ) ≤ u)
    (hlo : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ u) :
    (SupportProgram.count n J : ℝ) ≤
      (J : ℝ) * (2 : ℝ) ^ (6 * u * w n) := by
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hL1 : (1 : ℝ) ≤ L n := by exact_mod_cast L_pos n
  have hsqrt : Real.sqrt (L n : ℝ) ≤ (L n : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨hL.le, by nlinarith⟩
  have hroot : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hn : (0 : ℝ) < n := hu.trans_le hun
  have hratio : 4 * (n : ℝ) / u ≤ 4 * (L n : ℝ) := by
    have hh := (div_le_iff₀ hroot).mp hlo
    have hh' : (n : ℝ) ≤ u * (L n : ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_left hsqrt hu.le)
    apply (div_le_iff₀ hu).mpr
    nlinarith
  have hlog : Real.log (4 * (n : ℝ) / u) ≤ 3 * (w n : ℝ) :=
    (Real.log_le_log (by positivity) hratio).trans (log_four_L_le n)
  have hbudget : u * Real.log (4 * (n : ℝ) / u) ≤
      Real.log 2 * (6 * u * w n) := by
    have hh := mul_le_mul_of_nonneg_left hlog hu.le
    have h2 := log_two_bounds
    have hw : (0 : ℝ) ≤ w n := by positivity
    nlinarith [mul_nonneg hu.le hw]
  have hpow : (4 * (n : ℝ) / u)^u ≤ (2 : ℝ)^(6 * u * w n) := by
    rw [Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
    nlinarith [hbudget]
  unfold SupportProgram.count
  push_cast
  calc
    ∑ j ∈ Finset.range J, (n.choose j : ℝ) ≤
        ∑ _j ∈ Finset.range J, (2 : ℝ)^(6 * u * w n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (j : ℝ) ≤ u :=
        (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hj))).trans hJu
      exact (SubexponentialSAT.BranchTree.choose_le_rpow_real n j hu hun hj').trans hpow
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyUniform
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform bounds over every input at a fixed size.  The cutoff depends only
on fixed numerical exponents, never on a chosen sequence of formulas. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

theorem eventually_support_bound_oai {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ J : ℕ, (J : ℝ) ≤ entropyCutoff n C →
      (SupportProgram.count n J : ℝ) ≤
      (2 : ℝ)^((384 * C + 1) * Statement.runtimeScale n) := by
  have hCpos : 0 < C := by linarith
  have hsmall := eventually_w_power_le_L 2 (sq_pos_of_pos hCpos)
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, hpoly, eventually_ge_atTop 1] with n hnsmall hnpoly hn J hJ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hL : (0 : ℝ) < L n := by exact_mod_cast L_pos n
  have hr : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 hL
  have hcw : C * (w n : ℝ) ≤ Real.sqrt (L n : ℝ) := by
    apply (Real.le_sqrt (by positivity) hL.le).2
    nlinarith [hnsmall]
  have hu : 0 < entropyCutoff n C := by unfold entropyCutoff; positivity
  have hun : entropyCutoff n C ≤ n := by
    unfold entropyCutoff
    apply (div_le_iff₀ hr).2
    nlinarith
  have hlo : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ entropyCutoff n C := by
    unfold entropyCutoff
    apply div_le_div_of_nonneg_right _ hr.le
    have hc := mul_le_mul hC hw (by norm_num : (0 : ℝ) ≤ 1) hCpos.le
    nlinarith
  have hmain := support_le_entropy n J hu hun hJ hlo
  have hcost : 6 * entropyCutoff n C * w n ≤
      384 * C * Statement.runtimeScale n := by
    have hh := mul_le_mul_of_nonneg_left (weighted_scale_le_target n) (show 0 ≤ 6*C by positivity)
    unfold entropyCutoff
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hJn : (J : ℝ) ≤ n := hJ.trans hun
  have hnexp : (n : ℝ) ≤ (2 : ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hnpoly
    calc
      (n : ℝ) ≤ (n : ℝ) + 16 := by linarith
      _ = (2 : ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  calc
    (SupportProgram.count n J : ℝ) ≤
        (J : ℝ) * (2 : ℝ)^(6 * entropyCutoff n C * w n) := hmain
    _ ≤ (2 : ℝ)^Statement.runtimeScale n *
        (2 : ℝ)^(384*C*Statement.runtimeScale n) := by
      exact mul_le_mul (hJn.trans hnexp)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hcost)
        (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring


end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound_oai

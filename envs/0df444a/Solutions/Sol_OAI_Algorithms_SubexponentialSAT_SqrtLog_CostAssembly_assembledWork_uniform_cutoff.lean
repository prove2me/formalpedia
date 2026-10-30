-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:42:21.673313+00:00
-- url     : https://prove2.me/submissions/aa708cde-7458-4aca-9866-b84034832b93

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Asymptotic_eventually_residual_cutoff_ratio
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_hashCalls_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_residual_enumeration_ambient_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_sparse_parameter_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_support_bound

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

/-- A polynomial base can be rewritten as an actual base-two real power. -/
theorem rpow_eq_two_rpow_logb {x : ℝ} (hx : 0 < x) (d : ℝ) :
    x ^ d = (2 : ℝ) ^ (d * Real.logb 2 x) := by
  rw [Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold Real.logb
  field_simp

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

theorem eventually_L_power_le_n (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (L n : ℝ) ^ q ≤ n := by
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (SubexpRuntime.eventually_logb_power_le q
      (show 0 < C * (2 : ℝ) ^ q by positivity))
  filter_upwards [hb] with n hn
  calc
    C * (L n : ℝ) ^ q ≤ C * (2 * logSize n) ^ q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (L_le_twice_logSize n) q) hC.le
    _ = (C * (2 : ℝ) ^ q) * logSize n ^ q := by rw [mul_pow]; ring
    _ ≤ n := hn

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

theorem eventually_schedule_search_exponent (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤ binaryScale n := by
  have hmain := eventually_logSize_power_le (q + 1)
    (show 0 < C * (3 : ℝ) ^ q by positivity)
  filter_upwards [hmain] with n hn
  have ht := four_le_logSize n
  have hs : (s n : ℝ) ≤ 2 * logSize n :=
    (by exact_mod_cast s_le_L n : (s n : ℝ) ≤ L n).trans (L_le_twice_logSize n)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (s n : ℝ) + 2 by positivity)
    (show (s n : ℝ) + 2 ≤ 3 * logSize n by linarith) q
  have hl : Real.logb 2 ((n : ℝ) + 1) ≤ logSize n :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  calc
    C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤
        C * (3 * logSize n) ^ q * logSize n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hl hl0 (by positivity)
    _ = (C * (3 : ℝ) ^ q) * logSize n ^ (q + 1) := by
      rw [mul_pow, pow_succ]; ring
    _ ≤ binaryScale n := hn

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

theorem runtimeScale_nonneg (n : ℕ) : 0 ≤ runtimeScale n := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (Real.sqrt_nonneg _)

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

theorem eventually_search_exponent_target (q : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * ((s n : ℝ) + 2) ^ q * Real.logb 2 ((n : ℝ) + 1) ≤
        Statement.runtimeScale n := by
  filter_upwards [eventually_schedule_search_exponent q
    (show 0 < 16 * C by positivity)] with n hn
  have h := binaryScale_le_target n
  nlinarith

theorem eventually_variable_search_target (degree : ℕ → ℕ) (q : ℕ)
    {C : ℝ} (hC : 0 < C)
    (hdegree : ∀ᶠ n : ℕ in atTop, (degree n : ℝ) ≤ C * ((s n : ℝ) + 2) ^ q) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1) ^ degree n : ℕ) : ℝ) ≤ (2 : ℝ) ^ Statement.runtimeScale n := by
  filter_upwards [hdegree, eventually_search_exponent_target q hC] with n hd hn
  have hl0 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hexp := (mul_le_mul_of_nonneg_right hd hl0).trans hn
  have heq : (((n + 1) ^ degree n : ℕ) : ℝ) =
      (2 : ℝ) ^ ((degree n : ℝ) * Real.logb 2 ((n : ℝ) + 1)) := by
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_natCast]
    exact SubexpExponentArithmetic.rpow_eq_two_rpow_logb (by positivity) _
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticResidualJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The support cutoff uses residual spectral parameters and original
ambient precision. This numerical bound keeps the two dimensions distinct. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_ambient_support_scale_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_L_power_le_n 1 (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with n hLn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL1 : (1 : ℝ) ≤ L n := by exact_mod_cast L_pos n
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hr : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hroot : Real.sqrt (L n : ℝ) ≤ n :=
    (show Real.sqrt (L n : ℝ) ≤ (L n : ℝ) from
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩).trans (by simpa using hLn)
  apply (le_div_iff₀ hr).2
  nlinarith

/-- Uniform in the residual, occurrence bound, and ambient precision
envelope. This is the numerical input to the separate support-entropy proof. -/
theorem eventually_residual_jet_bound (k a q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b T : ℕ,
      m ≤ n → n ≤ 2 * m → b ≤ L m ^ q → T ≤ a * n →
      ((k * layoutCutoff m b * T / layoutQ m + 1 : ℕ) : ℝ) ≤
        ((k * a * (256 * (28 * q + 312)) : ℕ) + 1) *
          (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_residual_cutoff_ratio q,
    eventually_ambient_support_scale_ge_one] with n hn hone m b T hmn hnm hb hT
  have hratio := hn m b hmn hnm hb
  have hT' : (T : ℝ) ≤ (a : ℝ) * n := by exact_mod_cast hT
  have hdiv := Nat.cast_div_le (m := k * layoutCutoff m b * T) (n := layoutQ m) (α := ℝ)
  have hjet : ((k * layoutCutoff m b * T / layoutQ m + 1 : ℕ) : ℝ) ≤
      (k : ℝ) * ((layoutCutoff m b : ℝ) / layoutQ m) * T + 1 := by
    push_cast at hdiv ⊢
    calc
      _ ≤ (k : ℝ) * layoutCutoff m b * T / layoutQ m + 1 := by linarith
      _ = _ := by ring
  calc
    _ ≤ (k : ℝ) * ((layoutCutoff m b : ℝ) / layoutQ m) * T + 1 := hjet
    _ ≤ (k : ℝ) * ((256 * (28 * q + 312) : ℕ) * (w n : ℝ) /
        Real.sqrt (L n : ℝ)) * ((a : ℝ) * n) +
        (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by gcongr
    _ = _ := by push_cast; ring

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

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical assembly of the sparse-query costs.  `sparseWork` is an explicit
natural-valued upper cost, not a running-time oracle. Connecting an executable
program to these counters and charging coefficient arithmetic are separate
machine-refinement obligations. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Fixed polynomial overhead in n is negligible at the target scale. -/
theorem eventually_polynomial_target (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (((n+1)^d : ℕ) : ℝ) ≤
      (2 : ℝ)^Statement.runtimeScale n := by
  apply eventually_variable_search_target (fun _ => d) 0
    (show (0:ℝ) < (d:ℝ)+1 by positivity)
  filter_upwards [] with n
  simp

/-- A high-incidence branching exponent n/sqrt(L) costs at most a fixed
multiple of the requested runtime exponent. -/
theorem high_branch_exponent_le (n : ℕ) :
    (n : ℝ)/Real.sqrt (L n : ℝ) ≤ 64*Statement.runtimeScale n := by
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have h := weighted_scale_le_target n
  have hh : (n : ℝ)/Real.sqrt (L n : ℝ) ≤
      (n : ℝ)*(w n:ℝ)^2/Real.sqrt (L n:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hs : (1:ℝ) ≤ (w n:ℝ)^2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
  exact hh.trans h

/-- Pointwise assembly. The factor 17 charges the +1 support and the separate
setup. Every exponent is a constant coefficient of the same target scale. -/
theorem sparseWork_le (n J setup calls branches labels bits ordinary : ℕ)
    {T A B E : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hsetup : (setup:ℝ) ≤ (2:ℝ)^T)
    (hcalls : (calls:ℝ) ≤ (2:ℝ)^T)
    (hbranches : (branches:ℝ) ≤ (2:ℝ)^(B*T))
    (hlabels : (labels:ℝ) ≤ (2:ℝ)^(A*T))
    (hordinary : (bits:ℝ)*(ordinary+1:ℕ)^8 ≤ (2:ℝ)^T)
    (hsupport : (SupportProgram.count n J:ℝ) ≤ (2:ℝ)^(E*T)) :
    (sparseWork n J setup calls branches labels bits ordinary:ℝ) ≤
      17*(2:ℝ)^((2+B+A+4*E)*T) := by
  have hone : (1:ℝ) ≤ (2:ℝ)^(E*T) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hE hT)
  have hs : (SupportProgram.count n J:ℝ)+1 ≤ 2*(2:ℝ)^(E*T) := by linarith
  have hp : ((SupportProgram.count n J:ℝ)+1)^4 ≤
      16*(2:ℝ)^((4*E)*T) := by
    calc
      _ ≤ (2*(2:ℝ)^(E*T))^4 := by gcongr
      _ = _ := by
        have hpow : ((2:ℝ)^(E*T))^4 = (2:ℝ)^((E*T)*(4:ℝ)) := by
          exact (Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (E*T) 4).symm
        rw [mul_pow, hpow]
        norm_num
        congr 1
        ring
  have hmain : (calls:ℝ)*(branches:ℝ)*(labels:ℝ)*
      ((bits:ℝ)*(ordinary+1:ℕ)^8)*((SupportProgram.count n J:ℝ)+1)^4 ≤
      16*(2:ℝ)^((2+B+A+4*E)*T) := by
    calc
      _ ≤ (2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*
          (16*(2:ℝ)^((4*E)*T)) := by gcongr
      _ = _ := by
        rw [show (2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*
          (16*(2:ℝ)^((4*E)*T)) =
          16*((2:ℝ)^T*(2:ℝ)^(B*T)*(2:ℝ)^(A*T)*(2:ℝ)^T*(2:ℝ)^((4*E)*T)) by ring]
        simp only [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 2
        ring
  have hmono : T ≤ (2+B+A+4*E)*T := by nlinarith
  have hsetup' := hsetup.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hmono)
  unfold sparseWork
  push_cast
  calc
    _ = (setup:ℝ) + (calls:ℝ)*(branches:ℝ)*(labels:ℝ)*
        ((bits:ℝ)*(ordinary+1:ℕ)^8)*((SupportProgram.count n J:ℝ)+1)^4 := by push_cast; ring
    _ ≤ _ := by linarith

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

/-- Include up to n additional neutral factors in the literal jet-order
parameter.  They need not be removed from that parameter by the evaluator. -/
theorem linear_jet_envelope_with_neutrals (n m factors : ℕ) (hn : 2 ≤ n)
    (hm : Nat.size m ≤ n) (hf : factors ≤ 4*n+HashSelect.loopCap n m+2) :
    2*factors+3*(LeafParametersProgram.precision n m-1)+1 ≤ 30*n := by
  unfold HashSelect.loopCap at hf
  unfold LeafParametersProgram.precision
  omega

/-- A single threshold works for every resource record, hence every formula
and every retained-half branch satisfying the displayed numerical estimates.
Small inputs are deliberately left to the actual finite-fallback machine. -/
theorem eventually_assembledWork_bound (k qi ql d : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀p:Resources, Bounds qi ql d n p →
      (assembledWork k n p:ℝ) ≤
        17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  let C : ℝ := ((k*30*(256*(28*ql+312)):ℕ):ℝ)+1
  have hC : 1 ≤ C := by
    dsimp [C]
    have : (0:ℝ) ≤ (k*30*(256*(28*ql+312)):ℕ) := by positivity
    linarith
  filter_upwards [eventually_support_bound hC,eventually_hashCalls_bound qi,
    eventually_sparse_parameter_bounds qi,eventually_residual_jet_bound k 30 ql,
    eventually_residual_enumeration_ambient_bound,eventually_polynomial_target d,
    eventually_ge_atTop 2] with n hsup hcalls hpar hjet henum hpoly hn p hp
  have hsz := (hpar p.clauses p.initialOccurrence hp.clauses hp.initial).1
  have hT : jetNumerator n p ≤ 30*n :=
    linear_jet_envelope_with_neutrals n p.clauses p.factors hn hsz hp.factors
  have hJ : (jetOrder k n p:ℝ) ≤ entropyCutoff n C :=
    hjet p.residual p.localOccurrence (jetNumerator n p)
      hp.residual.1 hp.residual.2 hp.occurrence hT
  have hSupport := hsup (jetOrder k n p) hJ
  have hCalls := hcalls p.clauses p.initialOccurrence hp.clauses hp.initial
  have hEnum := henum p.residual p.labelBase p.labelRows p.heads p.headSize
    hp.residual.1 hp.residual.2 hp.base hp.rows hp.height hp.heads hp.headSize
  have hBranch : ((2^p.branchVars:ℕ):ℝ) ≤ (2:ℝ)^(64*Statement.runtimeScale n) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (hp.branch.trans (high_branch_exponent_le n))
  have hOrd : (p.bits:ℝ)*(p.ordinary+1:ℕ)^8 ≤ (2:ℝ)^Statement.runtimeScale n := by
    exact (show (p.bits:ℝ)*(p.ordinary+1:ℕ)^8 ≤ ((n+1)^d:ℕ) by
      exact_mod_cast hp.ordinary).trans hpoly
  have h := sparseWork_le n (jetOrder k n p) p.setup
    (hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
    (2^p.branchVars) (enumerationWork p.labelBase p.labelRows p.heads p.headSize)
    p.bits p.ordinary (Statement.runtimeScale_nonneg n)
    (by norm_num : (0:ℝ) ≤ 641) (by norm_num : (0:ℝ) ≤ 64)
    (show 0 ≤ 384*C+1 by linarith) hp.setup hCalls hBranch hEnum hOrd hSupport
  change (assembledWork k n p:ℝ) ≤ _ at h
  have heq : 2+(64:ℝ)+641+4*(384*C+1)=exponentConstant k ql := by
    unfold exponentConstant C
    ring
  rw [heq] at h
  exact h

theorem assembledWork_uniform_cutoff_oai (k qi ql d : ℕ) :
    ∃N:ℕ, ∀n ≥ N, ∀p:Resources, Bounds qi ql d n p →
      (assembledWork k n p:ℝ) ≤
        17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  exact Filter.eventually_atTop.mp (eventually_assembledWork_bound k qi ql d)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff_oai

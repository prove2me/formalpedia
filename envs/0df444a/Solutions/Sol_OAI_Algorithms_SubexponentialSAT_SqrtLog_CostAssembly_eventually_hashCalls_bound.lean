-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_hashCalls_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:22.247264+00:00
-- url     : https://prove2.me/submissions/fdc358e4-05b6-444b-8eb4-cb30cbeac8c0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S030
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_sparse_parameter_bounds

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

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem two_le_logLogSize (n : ℕ) : 2 ≤ logLogSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by have := four_le_logSize n; linarith : 0 < logSize n)).mpr
  norm_num
  exact four_le_logSize n

theorem L_le_logSize_add_one (n : ℕ) : (L n : ℝ) ≤ logSize n + 1 := by
  have h := Real.natLog_le_logb (n + 16) 2
  simpa [L, logSize, Nat.log2_eq_log_two, Nat.cast_add] using add_le_add_right h 1

theorem L_le_twice_logSize (n : ℕ) : (L n : ℝ) ≤ 2 * logSize n := by
  have := L_le_logSize_add_one n
  have := four_le_logSize n
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- A variable exponent polynomial in log n still gives negligible search
cost, even with an alphabet polynomial in n. -/
theorem eventually_polylog_degree_target (d : ℕ → ℕ) (q : ℕ) {C : ℝ}
    (hC : 0 < C) (hd : ∀ᶠ n:ℕ in atTop, (d n:ℝ) ≤ C*(L n:ℝ)^q) :
    ∀ᶠ n:ℕ in atTop, (((n+1)^d n:ℕ):ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  have hp := eventually_polylog_le_target (q+1)
    (show (0:ℝ) < C*2^q by positivity)
  filter_upwards [hd,hp] with n hdn hpn
  have hlog : Real.logb 2 ((n:ℝ)+1) ≤ logSize n :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.logb 2 ((n:ℝ)+1) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have he : (d n:ℝ)*Real.logb 2 ((n:ℝ)+1) ≤ Statement.runtimeScale n := by
    calc
      _ ≤ (C*(2*logSize n)^q)*logSize n := by
        apply mul_le_mul
        · exact hdn.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (L_le_twice_logSize n) q) hC.le)
        · exact hlog
        · exact hlog0
        · have := four_le_logSize n
          positivity
      _ = (C*2^q)*logSize n^(q+1) := by rw [mul_pow, pow_succ]; ring
      _ ≤ _ := hpn
  have heq : (((n+1)^d n:ℕ):ℝ)=(2:ℝ)^((d n:ℝ)*Real.logb 2 ((n:ℝ)+1)) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact SubexpExponentArithmetic.rpow_eq_two_rpow_logb (by positivity) _
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he

theorem hashCalls_le (n m P : ℕ) (hn : 1 ≤ n) (hm : m ≤ n^2)
    (hsize : Nat.size m ≤ n) :
    hashCalls n m P ≤ (n+1)^(3*P+7) := by
  have hsq : n ≤ n^2 := by nlinarith
  have hbase : 3*m ≤ (n+1)^3 := by nlinarith
  have hcap : HashSelect.loopCap n m ≤ (n+1)^3 := by
    unfold HashSelect.loopCap
    nlinarith
  have hm' : m ≤ (n+1)^2 := by nlinarith
  have hprod : 2*(3*m)^P*HashSelect.loopCap n m*m ≤ (n+1)^(3*P+6) := by
    calc
      _ ≤ (n+1)*((n+1)^3)^P*(n+1)^3*(n+1)^2 := by gcongr; omega
      _ = _ := by rw [← pow_mul]; ring
  have hpos : 1 ≤ (n+1)^(3*P+6) := Nat.one_le_pow _ _ (by omega)
  unfold hashCalls
  calc
    _ ≤ 2*(n+1)^(3*P+6) := by omega
    _ ≤ (n+1)*(n+1)^(3*P+6) := by gcongr; omega
    _ = _ := by rw [← pow_succ']

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

theorem eventually_hashCalls_bound_oai (q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B:ℕ, m ≤ n*B → B ≤ L n^q →
      (hashCalls n m (SparseCode.distanceDenom m B):ℝ) ≤
        (2:ℝ)^Statement.runtimeScale n := by
  have hdeg : ∀ᶠ n:ℕ in atTop,
      ((3*L n^(2*q+3)+7:ℕ):ℝ) ≤ 10*(L n:ℝ)^(2*q+3) := by
    filter_upwards [] with n
    have h : 1 ≤ L n^(2*q+3) := Nat.one_le_pow _ _ (L_pos n)
    have hh : 3*L n^(2*q+3)+7 ≤ 10*L n^(2*q+3) := by omega
    exact_mod_cast hh
  have hpow := eventually_polylog_degree_target (fun n => 3*L n^(2*q+3)+7)
    (2*q+3) (by norm_num : (0:ℝ) < 10) hdeg
  filter_upwards [eventually_sparse_parameter_bounds q,hpow,eventually_ge_atTop 1]
    with n hpar hpow hn m B hm hB
  obtain ⟨hsize,hm2,hP⟩ := hpar m B hm hB
  have hc := hashCalls_le n m (SparseCode.distanceDenom m B) hn hm2 hsize
  have hc' : hashCalls n m (SparseCode.distanceDenom m B) ≤
      (n+1)^(3*L n^(2*q+3)+7) :=
    hc.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact (show (hashCalls n m (SparseCode.distanceDenom m B):ℝ) ≤
    ((n+1)^(3*L n^(2*q+3)+7):ℕ) by exact_mod_cast hc').trans hpow

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_hashCalls_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_hashCalls_bound_oai

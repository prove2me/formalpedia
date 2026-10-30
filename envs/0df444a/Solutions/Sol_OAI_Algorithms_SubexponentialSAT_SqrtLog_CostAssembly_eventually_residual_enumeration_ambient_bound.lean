-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:40:19.060337+00:00
-- url     : https://prove2.me/submissions/801e998b-90ec-4e98-91e0-07708787b6dc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Asymptotic_eventually_residual_inverse_target

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRuntime
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticOverhead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The integer-signature and head-bucket enumeration costs, with the actual
joint-signature count rather than rank used as the exponential resource. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Natural integer signature range, converted to the exact binary exponent. -/
theorem enumerationWork_le (labelBase rows heads headSize : ℕ)
    (hbase : 0 < labelBase) {e f g : ℝ}
    (he : (rows:ℝ)*Real.logb 2 labelBase ≤ e)
    (hf : (headSize:ℝ) ≤ f)
    (hg : (heads:ℝ) ≤ (2:ℝ)^g) :
    (enumerationWork labelBase rows heads headSize:ℝ) ≤ (2:ℝ)^(e+g+f) := by
  have hb : (0:ℝ) < labelBase := by exact_mod_cast hbase
  have hlabel : ((labelBase^rows:ℕ):ℝ) ≤ (2:ℝ)^e := by
    calc
      _ = (2:ℝ)^((rows:ℝ)*Real.logb 2 labelBase) := by
        push_cast
        rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast,
          Real.rpow_logb (by norm_num) (by norm_num) hb]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have hhead : ((2^headSize:ℕ):ℝ) ≤ (2:ℝ)^f := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hf
  push_cast at hlabel hhead
  unfold enumerationWork
  push_cast
  calc
    _ ≤ (2:ℝ)^e*(2:ℝ)^g*(2:ℝ)^f := by
      exact mul_le_mul (mul_le_mul hlabel hg (by positivity) (by positivity))
        hhead (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]

/-- With epsilon=1/(32 B r L²), total rows ≤ 2 epsilon n B means
16 r L² rows ≤ n.  Combined with the integer label-height bound, the logarithm
of the full joint signature image is at most n/(2r). -/
theorem signature_log_budget (base rows : ℕ) {n r l : ℝ}
    (hr : 0 < r) (hrows : 16*r*l^2*(rows:ℝ) ≤ n)
    (hheight : Real.log (base:ℝ) ≤ 4*l^2) :
    (rows:ℝ)*Real.logb 2 base ≤ n/(2*r) := by
  have h2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 := log_two_bounds
  have hheight' := mul_le_mul_of_nonneg_left hheight (show (0:ℝ) ≤ rows by positivity)
  have hh : (rows:ℝ)*Real.log (base:ℝ)/Real.log 2 ≤ 8*(rows:ℝ)*l^2 := by
    apply (div_le_iff₀ h2p).2
    have hs : 0 ≤ (rows:ℝ)*l^2 := by positivity
    nlinarith
  unfold Real.logb
  rw [← mul_div_assoc]
  apply hh.trans
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*r)).2
  nlinarith

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyResidualEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Ambient seeds may be chosen before restricting heads to free variables.
The larger head bound still has coefficient 641: its numerator is already the
ambient dimension in the residual inverse-schedule estimate. -/
theorem eventually_residual_enumeration_ambient_bound_oai :
    ∀ᶠ n : ℕ in atTop, ∀ m base rows heads headSize: ℕ,
      m ≤ n → n ≤ 2*m → 0 < base →
      16*(layoutR m: ℝ)*(L m: ℝ)^2*(rows: ℝ) ≤ m →
      Real.log (base: ℝ) ≤ 4*(L m: ℝ)^2 →
      heads ≤ n+1 → (headSize: ℝ) ≤ 2*(n: ℝ)/layoutR m →
      (enumerationWork base rows heads headSize: ℝ) ≤
        (2: ℝ)^(641*Statement.runtimeScale n) := by
  have hpoly := eventually_polylog_le_target 1 (by norm_num : (0: ℝ) < 1)
  filter_upwards [eventually_residual_inverse_target, hpoly]
    with n hi hp m base rows heads headSize hmn hnm hb hr hh hd hs
  have hInv := hi m hmn hnm
  have hrpos : (0: ℝ) < layoutR m := by
    have := layoutR_ge_two m
    exact_mod_cast (by omega : 0 < layoutR m)
  have hmn' : (m: ℝ) ≤ n := by exact_mod_cast hmn
  have he := signature_log_budget base rows hrpos hr hh
  have hmnInv : (m: ℝ)/layoutR m ≤ (n: ℝ)/layoutR m :=
    div_le_div_of_nonneg_right hmn' hrpos.le
  have hE : (rows: ℝ)*Real.logb 2 base ≤ 128*Statement.runtimeScale n := by
    have : (m: ℝ)/(2*layoutR m) = ((m: ℝ)/layoutR m)/2 := by ring
    rw [this] at he
    linarith
  have hF : (headSize: ℝ) ≤ 512*Statement.runtimeScale n := by
    have : 2*(n: ℝ)/layoutR m = 2*((n: ℝ)/layoutR m) := by ring
    rw [this] at hs
    linarith
  have hG : (heads: ℝ) ≤ (2: ℝ)^Statement.runtimeScale n := by
    have hlog : logSize n ≤ Statement.runtimeScale n := by simpa using hp
    calc
      _ ≤ (n: ℝ)+1 := by exact_mod_cast hd
      _ ≤ (n: ℝ)+16 := by linarith
      _ = (2: ℝ)^logSize n := by
        symm
        exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  convert enumerationWork_le base rows heads headSize hb hE hF hG using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound_oai

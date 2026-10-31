-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:47:03.70306+00:00
-- url     : https://prove2.me/submissions/dac89aef-7f3e-45c5-9ecb-b49dd121474a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_ambient_commonBase_log
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_query_max_bound_rat
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ProducedQueryResources_rank_budget

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesScalars
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial numerical dimensions of every actual large-input query.
These bounds do not include serialized bucket or sparse-dictionary buffers. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology

 theorem input_ambient (q : Query) (k : ℕ) : (q.input k).ambient=ambient q := rfl

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The maximum size of an actually emitted head list is bounded directly
from a query's integer guards. Ambient owner IDs remain unchanged, while
all layout parameters use the measured free-variable count. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open SubexponentialSAT.MulticolorTypes LeafParametersProgram LeafQueryFrontend

/-- Form consumed by the produced-query resource envelope: ambient head
sizes with the free-variable layout schedule. -/
 theorem query_max_bound_real (q : Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    let p := LeafProgram.Query.packingProblem q k hg
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ) ≤
      2*(BinaryArithmetic.toNat q.ambient:ℝ)/Asymptotic.layoutR (q.input k).freeCount := by
  let p := LeafProgram.Query.packingProblem q k hg
  have hq : (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) :=
    query_max_bound_rat q k hg a tail haN haC
  have hrq : (0:ℚ) < p.r := by exact_mod_cast p.hr
  have hm := (le_div_iff₀ (by positivity : (0:ℚ) < 2*(p.r:ℚ))).mp hq
  have hmR : (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ)*(2*(p.r:ℝ)) ≤ 3*(p.n:ℝ) := by
    exact_mod_cast hm
  have hr : (0:ℝ) < p.r := by exact_mod_cast p.hr
  change (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℝ) ≤ 2*(p.n:ℝ)/(p.r:ℝ)
  apply (le_div_iff₀ hr).mpr
  nlinarith [show (0:ℝ) ≤ (p.n:ℝ) by positivity]

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform numerical envelope for the actual finite code searches.
Search dimensions occur only in the exponential factor. Encoded metadata
lengths remain in a separate fixed polynomial factor. -/
namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open Filter
open scoped Topology
open CostAssembly Asymptotic

theorem exponent_le (C A H u n q : ℕ) (hH : H ≤ A*L n^q) :
    exponent C H+6*(u+1) ≤ degreeConstant C A u * L n^(2*q) := by
  have hp : 1 ≤ L n^q := Nat.one_le_pow _ _ (L_pos n)
  have hp2 : 1 ≤ L n^(2*q) := Nat.one_le_pow _ _ (L_pos n)
  have hh : H+1 ≤ (A+1)*L n^q := by nlinarith
  have hsq : (H+1)^2 ≤ (A+1)^2*L n^(2*q) := by
    calc
      _ ≤ ((A+1)*L n^q)^2 := by gcongr
      _ = _ := by ring
  unfold exponent degreeConstant
  nlinarith

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupOuterCostMajorant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

theorem setupMajorant_target (C d q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (setupMajorant C d q n : ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  let K := C+d+CodeSetupCost.degreeConstant
    (CodeSetupCost.fixedConstant 1 1) (CodeSetupCost.heightCoefficient q) 0
  have hK : (0:ℝ) < K := by dsimp [K,CodeSetupCost.degreeConstant]; positivity
  have hd : ∀ᶠ n : ℕ in atTop,
      ((C+d+searchExponent q n:ℕ):ℝ) ≤ (K:ℝ)*(L n:ℝ)^(2*(2*q+3)) := by
    filter_upwards [] with n
    have he := CodeSetupCost.exponent_le (CodeSetupCost.fixedConstant 1 1)
      (CodeSetupCost.heightCoefficient q)
      (CodeSetupCost.heightCoefficient q * L n^(2*q+3)) 0 n (2*q+3) (by rfl)
    have hp : 1 ≤ L n^(2*(2*q+3)) := Nat.one_le_pow _ _ (L_pos n)
    have hb : C+d+searchExponent q n ≤ K*L n^(2*(2*q+3)) := by
      dsimp [K,searchExponent]
      nlinarith
    exact_mod_cast hb
  exact eventually_polylog_degree_target (fun n => C+d+searchExponent q n)
    (2*(2*q+3)) hK hd

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical constructor for an actual query. Rank and maximum head size
are its two geometry arguments; ProducedQueryRank and LayoutProducedHeads
supply them from the actual packing. This module does not assert that an
arbitrary pair of natural numbers has those geometric bounds. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology

noncomputable section

 theorem make_ordinary_bound (q : Query) (k B rows size C d qi e : ℕ)
    (hn : 1 ≤ ambient q) :
    (make q k B rows size C d qi e).bits*((make q k B rows size C d qi e).ordinary+1)^8 ≤
      (ambient q+1)^(9*e+8) := by
  let a := ambient q+1
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hp : 1 ≤ a^e := Nat.one_le_pow _ _ (by omega)
  have h : a^e+1 ≤ a^(e+1) := by rw [pow_succ]; nlinarith
  change a^e*(a^e+1)^8 ≤ a^(9*e+8)
  calc
    _ ≤ a^e*(a^(e+1))^8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; omega

 theorem heads_le_ambient (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    layoutR (q.input k).freeCount ≤ ambient q+1 := by
  have hr := layoutR_ge_two (q.input k).freeCount
  have hq := hg.2.2.2.2.2.2.1
  have hbudget := hg.2.2.2.2.2.2.2.2.2
  change 16*layoutQ (q.input k).freeCount*(layoutR (q.input k).freeCount)^2 ≤ (q.input k).freeCount at hbudget
  change 2 ≤ layoutQ (q.input k).freeCount at hq
  have hfree := hg.2.1
  rw [input_ambient] at hfree
  nlinarith [Nat.mul_le_mul_right ((layoutR (q.input k).freeCount)^2) hq]

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous Bounds for the actual query and searched packing. Neither
rank, head size, cardinalities of bucket tables, nor running times are
assumptions of this theorem. The alphabet premises describe the output of
the native complete-alphabet enumeration. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem headSize_budget (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
    (headSize q k hg a tail:ℝ) ≤ 2*(ambient q:ℝ)/layoutR (q.input k).freeCount :=
  LayoutProducedHeads.query_max_bound_real q k hg a tail haN haC

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original explicit resource record for the actual packing has the
sqrt-log bound from the new literal scope estimates. No identity with the old
selector history is used. These are numerical bounds on that record; a caller
still composes and bounds the actual streamed execution. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets

open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources
  OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open scoped Topology

noncomputable section

/-- Every sharp resource field follows from the actual scan and the two
geometric quantities. The cutoff is independent of all query inputs. -/
theorem eventually_make_bounds_of_scan (k qi ql C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B rows size : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      (16 * (layoutR (q.input k).freeCount : ℝ) *
        (L (q.input k).freeCount : ℝ)^2 * (rows : ℝ) ≤ (q.input k).freeCount) →
      ((size : ℝ) ≤ 2 * (n : ℝ) / layoutR (q.input k).freeCount) →
      Bounds qi ql (9*e+8) n (make q k B rows size C d qi e) := by
  filter_upwards [eventually_ambient_commonBase_log ql,
    CodeSetupOuterCost.setupMajorant_target C d qi, eventually_ge_atTop (1 : ℕ)]
    with n hbase hsetup hn q B rows size hqn hs hc hBL hrows hsize
  have hb := hs.guard.2.2.2.1
  have hnfree : n ≤ 2 * (q.input k).freeCount := by
    simpa only [hqn] using hs.residual.2
  refine ⟨?_, hc, hBL, hs.occurrence, ?_, ?_, by dsimp [make]; omega,
    hrows, ?_, ?_, hsize, ?_, ?_⟩
  · simpa only [make, hqn] using hs.residual
  · simpa only [make, hqn] using hs.factors
  · simpa only [make, hqn] using hs.branch
  · simpa only [make, matrixHeight, hqn] using
      hbase (q.input k).freeCount (q.input k).occurrence hnfree hb hs.occurrence
  · simpa only [make, hqn] using heads_le_ambient q k hs.guard
  · simpa only [make, hqn] using hsetup
  · simpa only [hqn] using make_ordinary_bound q k B rows size C d qi e (by omega)

/-- The searched complete alphabet supplies both actual selected-rank and
balanced-head bounds; neither number is an additional certificate input. -/
theorem eventually_ofPacking_bounds_of_scan_oai (k qi ql C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
        Bounds qi ql (9*e+8) n (ofPacking q k B C d qi e hg a tail) := by
  filter_upwards [eventually_make_bounds_of_scan k qi ql C d e]
    with n hbound q B hqn hs hc hBL hg a tail haN haC
  apply hbound q B _ _ hqn hs hc hBL
  · exact rank_budget q k hg a tail haN haC
  · simpa only [hqn] using headSize_budget q k hg a tail haN haC

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan_oai

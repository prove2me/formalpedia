-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:19:07.173666+00:00
-- url     : https://prove2.me/submissions/b137e91e-623c-456e-8cbe-249a75fff518

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_assembledWork_uniform_cutoff
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds_physicalCap_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets_high_loop_budget_polynomial

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

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

theorem runtimeBound_mono_exponent {constant a b : ℝ} (hc : 0 ≤ constant)
    (hab : a ≤ b) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant b degree inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hab (runtimeScale_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry LeafParametersProgram CostAssembly.Polynomial
open NativeQueryPreparation ProducedQueryResources

/-- Actual Setup uses a smaller frontend cost than the uniform literal-query
allowance, so its retained local bound fits the same preparedCap. -/
theorem setup_local_bound_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
      (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp) ≤
        preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
  dsimp only [HighQuerySetup.localBound, preparedCap]
  gcongr

/-- The measured frontend/preparation/seed cost uses the same actual
local bound; it never uses the collector's physical length. -/
theorem setup_time_le (Cp dp Cn dn Cl dl Cf df N L k f : ℕ)
    (hf : f ≤ frontendCap Cf df L k) :
    f + Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp +
      110*HighQuerySetup.localBound (sourceCap Cn dn Cl dl N L k+f)
        (Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp)+81 ≤
      frontendCap Cf df L k+111*preparedCap Cp dp Cn dn Cl dl Cf df N L k+81 := by
  have hp := setup_local_bound_le Cp dp Cn dn Cl dl Cf df N L k f hf
  have hc : Cp*(sourceCap Cn dn Cl dl N L k+f+1)^dp ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N L k := by
    have h := Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left
      (show sourceCap Cn dn Cl dl N L k+f+1 ≤
        sourceCap Cn dn Cl dl N L k+frontendCap Cf df L k+1 by omega) dp)
    dsimp only [preparedCap,HighQuerySetup.localBound]
    omega
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionRuntime
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical closure lemmas for the actual cutoff and identifier wrappers.
These assign no running time to an unimplemented operation. -/
namespace SubexponentialSAT.SqrtLog.Execution

open Statement

theorem runtimeBound_mono_degree {C A : ℝ} (hC : 0 ≤ C)
    {d e : ℕ} (hde : d ≤ e) (L n : ℕ) :
    runtimeBound C A d L n ≤ runtimeBound C A e L n := by
  unfold runtimeBound
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hde) hC)
    (by positivity)

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect


open SqrtLog SqrtLog.Statement
 theorem work_polynomial_runtime (coefficient e K p inputLength n U work H : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hU : U ≤ K*(inputLength+1)^p)
    (hwork : (work : ℝ) ≤ 17*(2 : ℝ)^(A*runtimeScale n))
    (hH : (H : ℝ) ≤ 64*runtimeScale n) :
    ((coefficient*(U+1)^e*(work+1)^2*2^H : ℕ) : ℝ) ≤
      runtimeBound ((coefficient : ℝ)*((K : ℝ)+1)^e*324)
        (2*A+64) (p*e) inputLength n := by
  have hinput : 1 ≤ (inputLength+1)^p := Nat.one_le_pow' _ _
  have huNat : U+1 ≤ (K+1)*(inputLength+1)^p := by nlinarith only [hU,hinput]
  have hu : (U : ℝ)+1 ≤ ((K : ℝ)+1)*((inputLength : ℝ)+1)^p := by exact_mod_cast huNat
  have hE : (1 : ℝ) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
  have hw : (work : ℝ)+1 ≤ 18*(2 : ℝ)^(A*runtimeScale n) := by linarith
  have hh : ((2^H : ℕ) : ℝ) ≤ (2 : ℝ)^(64*runtimeScale n) := by
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hH
  have hm := mul_le_mul (mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu e)
      (show (0 : ℝ) ≤ coefficient by positivity))
    (pow_le_pow_left₀ (by positivity) hw 2) (by positivity) (by positivity))
    hh (by positivity) (by positivity)
  push_cast at hm ⊢
  apply hm.trans_eq
  unfold runtimeBound
  rw [mul_pow, ← pow_mul, mul_pow,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [Nat.cast_ofNat]
  rw [show A*runtimeScale n*(2 : ℝ) = (2*A)*runtimeScale n by ring]
  rw [show (coefficient : ℝ)*(((K : ℝ)+1)^e*((inputLength : ℝ)+1)^(p*e))*
      (324*(2 : ℝ)^((2*A)*runtimeScale n))*(2 : ℝ)^(64*runtimeScale n) =
      ((coefficient : ℝ)*((K : ℝ)+1)^e*324)*((inputLength : ℝ)+1)^(p*e)*
        ((2 : ℝ)^((2*A)*runtimeScale n)*(2 : ℝ)^(64*runtimeScale n)) by ring]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  congr 2
  ring

/-- Uniform over all genuine resource records satisfying the sharp fields.
The caller derives those fields from the actual produced packing. -/
theorem high_loop_runtimeBound (k qi ql recordDegree K p : ℕ) :
    ∃ C A : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ A ∧ 1 ≤ degree ∧
      ∀ ambient ≥ cutoff, ∀ r : CostAssembly.Resources,
      CostAssembly.Bounds qi ql recordDegree ambient r →
      ∀ n t d Q J bankA S U L H inputLength : ℕ,
      n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → bankA ≤ U → S ≤ U →
      L ≤ U → H ≤ U → H = r.branchVars → U ≤ K*(inputLength+1)^p →
      ((2^H*(QueryStreamCorrect.budget n t d Q J bankA S
          (CostAssembly.assembledWork k ambient r)+11*L+16*(n+2)+28*H+27)+3 : ℕ) : ℝ) ≤
        runtimeBound C A degree inputLength ambient := by
  obtain ⟨C,e,hpoly⟩ := high_loop_budget_polynomial
  obtain ⟨N,hN⟩ := CostAssembly.assembledWork_uniform_cutoff k qi ql recordDegree
  let coefficient : ℝ := (C : ℝ)*((K : ℝ)+1)^e*324
  let exponent := CostAssembly.exponentConstant k ql
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hexponent : 0 ≤ exponent := by dsimp [exponent,CostAssembly.exponentConstant]; positivity
  refine ⟨coefficient+1,2*exponent+64,p*e+1,N,by linarith,by linarith,by omega,?_⟩
  intro ambient hambient r hr n t d Q J bankA S U L H inputLength hn ht hd hQ hJ hA hS hL hH hHeq hU
  have hb := hpoly n t d Q J bankA S (CostAssembly.assembledWork k ambient r) U L H
    hn ht hd hQ hJ hA hS hL hH
  have hbranch : (H : ℝ) ≤ 64*runtimeScale ambient := by
    rw [hHeq]
    exact hr.branch.trans (CostAssembly.high_branch_exponent_le ambient)
  have h := work_polynomial_runtime C e K p inputLength ambient U
    (CostAssembly.assembledWork k ambient r) H exponent hexponent hU
    (hN ambient hambient r hr) hbranch
  have htime := (Nat.cast_le.mpr hb).trans h
  apply htime.trans
  apply (Execution.runtimeBound_mono_degree hcoefficient
    (show p*e ≤ p*e+1 by omega) inputLength ambient).trans
  unfold runtimeBound
  gcongr
  linarith



open Filter SqrtLog SqrtLog.Statement


open SqrtLog SqrtLog.Statement
/-- Adding finitely many source phases preserves the same scale. -/
theorem runtimeBound_add_bound (C D A B : ℝ) (d e inputLength n : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    runtimeBound C A d inputLength n + runtimeBound D B e inputLength n ≤
      runtimeBound (C+D) (A+B) (d+e) inputLength n := by
  have hc := (runtimeBound_mono_exponent hC (show A ≤ A+B by linarith)
    d inputLength n).trans (Execution.runtimeBound_mono_degree hC
      (show d ≤ d+e by omega) inputLength n)
  have hd := (runtimeBound_mono_exponent hD (show B ≤ A+B by linarith)
    e inputLength n).trans (Execution.runtimeBound_mono_degree hD
      (show e ≤ d+e by omega) inputLength n)
  apply (add_le_add hc hd).trans_eq
  unfold runtimeBound
  ring

/-- Polynomial preprocessing and postprocessing are paid separately from the
stream/high core, with no exponential cost used as a storage cap. -/
theorem polynomial_overhead_runtime (C A : ℝ) (d K e inputLength n core extra : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcore : (core : ℝ) ≤ runtimeBound C A d inputLength n)
    (hextra : extra ≤ K*(inputLength+1)^e) :
    ((core+extra : ℕ) : ℝ) ≤ runtimeBound (C+K) A (d+e) inputLength n := by
  have he : (extra : ℝ) ≤ runtimeBound K 0 e inputLength n := by
    simpa only [runtimeBound,zero_mul,Real.rpow_zero,mul_one,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_add,Nat.cast_one] using (Nat.cast_le.mpr hextra : (extra : ℝ) ≤ (K*(inputLength+1)^e : ℕ))
  have h := (add_le_add hcore he).trans
    (runtimeBound_add_bound C K A 0 d e inputLength n hC (by positivity) hA (by norm_num))
  simpa only [Nat.cast_add,add_zero] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Time bounds for the same actual source/prepared caps used by the literal
query provider. The resource record supplies the combinatorial exponent;
its ordinary fields are not asserted to measure the actual physical phases.
Frontend, preparation, seed and return work are paid separately below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

open SqrtLog SqrtLog.Statement CostAssembly.Polynomial NativeQueryInputBounds

/-- Both exact complete-query budgets have one uniform ETH-scale bound.
The caller supplies the actual produced resource record, its sharp fields,
and the equality between its branch count and the actual high mask. -/
theorem runtime_bound_oai (k qi ql recordDegree Cp dp Cn dn Cl dl Cf df C0 d0 : ℕ) :
    ∃ C E : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
      ∀ n ≥ cutoff, ∀ N L : ℕ, n ≤ N → L ≤ C0*(N+1)^d0 →
      ∀ r : CostAssembly.Resources, CostAssembly.Bounds qi ql recordDegree n r →
      ∀ f t d Q J h : ℕ,
      let S := sourceCap Cn dn Cl dl N L k
      let F := frontendCap Cf df L k
      let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
      let A := 12*P+4*N+6
      let T := A+S+2
      let cost := Cp*(S+f+1)^dp
      let loop := HighQueryCorrect.loopBudget n h t d Q J A T
        (CostAssembly.assembledWork k n r)
      f ≤ F → t ≤ S → d ≤ S → Q ≤ S → J ≤ S → h ≤ n → h = r.branchVars →
      (HighQueryCorrect.markedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n ∧
      (HighQueryCorrect.acceptedBudget F (S+f) cost loop (QueryHeadBudgets.compact A) : ℝ) ≤
        runtimeBound C E degree N n := by
  obtain ⟨K,p,hphysical⟩ := physicalCap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  obtain ⟨C,E,degree,cutoff,hC,hE,hdegree,hloop⟩ :=
    QueryStreamBudgets.high_loop_runtimeBound k qi ql recordDegree K p
  refine ⟨C+(10000*(K+1) : ℕ),E,degree+p,cutoff,by have := Nat.cast_nonneg (α := ℝ) (10000*(K+1)); linarith,hE,by omega,?_⟩
  intro n hn N L hN hL r hr f t d Q J h S F P A T cost loop hf ht hd hQ hJ hh heq
  let U := physicalCap Cp dp Cn dn Cl dl Cf df N L k
  have hU : U ≤ K*(N+1)^p := hphysical N L hL
  have hbase : S+F+P+4*N+6+1 ≤ U := by
    dsimp only [U,physicalCap,S,F,P]
    omega
  have hA : A ≤ U := by
    dsimp only [A,U,physicalCap,S,F,P]
    omega
  have hT : T ≤ U := by
    dsimp only [T,A,U,physicalCap,S,F,P]
    omega
  have hcompact : QueryHeadBudgets.compact A ≤ U := by
    dsimp only [A,U,physicalCap,S,F,P]
    omega
  have hcore : (loop : ℝ) ≤ runtimeBound C E degree N n :=
    hloop n hn r hr n t d Q J A T U (QueryHeadBudgets.compact A) h N
      (by omega) (by omega) (by omega) (by omega) (by omega) hA hT hcompact
      (by omega) heq hU
  let extra := F+cost+110*HighQuerySetup.localBound (S+f) cost+
    3430*QueryHeadBudgets.compact A+5229
  have hsetup := setup_time_le Cp dp Cn dn Cl dl Cf df N L k f hf
  have hextra : extra ≤ 10000*(U+1) := by
    change F+cost+110*HighQuerySetup.localBound (S+f) cost+
      3430*QueryHeadBudgets.compact A+5229 ≤ _
    change f+cost+110*HighQuerySetup.localBound (S+f) cost+81 ≤ F+111*P+81 at hsetup
    omega
  have hone : 1 ≤ (N+1)^p := Nat.one_le_pow' _ _
  have huone : U+1 ≤ (K+1)*(N+1)^p := by nlinarith only [hU,hone]
  have hextra' : extra ≤ (10000*(K+1))*(N+1)^p :=
    hextra.trans ((Nat.mul_le_mul_left 10000 huone).trans_eq (by ring))
  have htotal := QueryStreamBudgets.polynomial_overhead_runtime C E degree
    (10000*(K+1)) p N n loop extra (by linarith) (by linarith) hcore hextra'
  have hmarked : HighQueryCorrect.markedBudget F (S+f) cost loop
      (QueryHeadBudgets.compact A) ≤ loop+extra := by
    dsimp only [HighQueryCorrect.markedBudget,extra]
    omega
  have haccepted : HighQueryCorrect.acceptedBudget F (S+f) cost loop
      (QueryHeadBudgets.compact A) = loop+extra := by
    dsimp only [HighQueryCorrect.acceptedBudget,extra]
    omega
  exact ⟨(Nat.cast_le.mpr hmarked).trans htotal,by simpa only [haccepted] using htotal⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound_oai

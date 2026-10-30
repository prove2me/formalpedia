-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:44:52.128472+00:00
-- url     : https://prove2.me/submissions/64e2dc85-f7a2-42bc-88ee-982c8c78c186

import Mathlib
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S030

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

theorem eventually_absorb_L_coefficient (b : ℕ → ℕ) (C q : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ C * L n ^ q) :
    ∀ᶠ n : ℕ in atTop, b n ≤ L n ^ (q + 1) := by
  filter_upwards [hb, eventually_L_ge C] with n hn hC
  exact hn.trans (by simpa [pow_succ, mul_comm] using Nat.mul_le_mul_right (L n ^ q) hC)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameters
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

/-- Sparse clauses have only logarithmic binary length. The upper bound here
is intentionally elementary; it is enough for the linear precision budget. -/
theorem sparse_clause_size_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    Nat.size m ≤ (q+1)*L n+1 := by
  have hn : n ≤ 2^L n := by
    have hh : n+16 < 2^L n := by simpa [L] using (Nat.lt_log2_self (n:=n+16))
    omega
  have hL : L n ≤ 2^L n := (Nat.lt_two_pow_self).le
  have hpow : m ≤ 2^((q+1)*L n) := by
    calc
      m ≤ n*B := hm
      _ ≤ 2^L n*(2^L n)^q := Nat.mul_le_mul hn (hB.trans (Nat.pow_le_pow_left hL q))
      _ = 2^((q+1)*L n) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  apply Nat.size_le.mpr
  exact hpow.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyCodeParameters
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

theorem code_logSize_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.logSize m ≤ (q+2)*L n := by
  have hL : 1 ≤ L n := L_pos n
  by_cases hz : m=0
  · subst m
    simp only [SparseCode.logSize, Nat.log_zero_right, zero_add]
    nlinarith
  have hs := sparse_clause_size_le n m B q hm hB
  have he : SparseCode.logSize m=Nat.size m := by
    rw [LeafParametersProgram.size_eq_log2_add_one hz]
    simp [SparseCode.logSize, Nat.log2_eq_log_two]
  rw [he]
  nlinarith

theorem code_distanceDenom_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.distanceDenom m B ≤ 20000*(q+2)^2*L n^(2*q+2) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.distanceDenom
  calc
    _ ≤ 20000*(L n^q)^2*((q+2)*L n)^2 := by gcongr
    _ = _ := by ring

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


theorem eventually_sparse_parameter_bounds_oai (q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B:ℕ, m ≤ n*B → B ≤ L n^q →
      Nat.size m ≤ n ∧ m ≤ n^2 ∧ SparseCode.distanceDenom m B ≤ L n^(2*q+3) := by
  have hs := eventually_L_power_le_n 1 (show (0:ℝ) < (q:ℝ)+2 by positivity)
  have hb := eventually_L_power_le_n q (by norm_num : (0:ℝ) < 1)
  have hc := eventually_absorb_L_coefficient
    (fun n => 20000*(q+2)^2*L n^(2*q+2)) (20000*(q+2)^2) (2*q+2)
    (Filter.Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [hs,hb,hc] with n hsn hbn hcn m B hm hB
  have hsize := sparse_clause_size_le n m B q hm hB
  have hL : 1 ≤ L n := L_pos n
  have hsn' : (q+2)*L n ≤ n := by
    exact_mod_cast (by simpa using hsn : ((q:ℝ)+2)*(L n:ℝ) ≤ n)
  have hbn' : L n^q ≤ n := by exact_mod_cast (by simpa using hbn : (L n:ℝ)^q ≤ n)
  refine ⟨by nlinarith,by nlinarith,?_⟩
  exact (code_distanceDenom_le n m B q hm hB).trans hcn

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds_oai

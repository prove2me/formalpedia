-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:40:30.901466+00:00
-- url     : https://prove2.me/submissions/29604977-274e-4246-8946-0a2478d9f139

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSetupCost_eventually_envelope_with_words
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_chosen_preparation_time_envelope
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets_prepared_common_bound_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_prepare_raw
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_canonicalParameterTime_polynomial

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

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

theorem runtimeScale_nonneg (n : ℕ) : 0 ≤ runtimeScale n := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (Real.sqrt_nonneg _)

theorem runtimeBound_mul_constant (factor constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) :
    runtimeBound (factor * constant) exponentConstant degree inputBits numVars =
      factor * runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  ring

/-- A fixed polynomial simulation overhead preserves the specified scale. -/
theorem runtimeBound_pow (constant exponentConstant : ℝ)
    (degree inputBits numVars power : ℕ) :
    runtimeBound constant exponentConstant degree inputBits numVars ^ power =
      runtimeBound (constant ^ power) ((power : ℝ) * exponentConstant)
        (degree * power) inputBits numVars := by
  unfold runtimeBound
  rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num)]
  congr 2
  ring

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Asymptotics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical parameters for the disjoint counting reduction. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem sparsifyLambda_eq_ceil (n : ℕ) :
    sparsifyLambda n = ⌈Real.logb 2 n⌉₊ :=
  (Real.natCeil_logb_natCast 2 n).symm

theorem sparsifyNu_eq_ceil (n : ℕ) :
    sparsifyNu n = ⌈Real.logb 2 (sparsifyLambda n)⌉₊ :=
  (Real.natCeil_logb_natCast 2 (sparsifyLambda n)).symm

theorem sparsifyNu_pos {n : ℕ} (hn : 20 ≤ n) : 0 < sparsifyNu n := by
  have hLambda : 2 ≤ sparsifyLambda n := by
    have h := (Nat.pow_lt_iff_lt_clog (by norm_num : 1 < (2 : ℕ))).mp
      (show 2 ^ 1 < n by omega)
    exact h
  exact Nat.clog_pos (by norm_num) hLambda

theorem le_sparsifySchedule_iff {n : ℕ} (hn : 20 ≤ n) (a : ℕ) :
    a ≤ sparsifySchedule n ↔ a ^ 2 * sparsifyNu n ^ 4 ≤ sparsifyLambda n := by
  rw [sparsifySchedule, Nat.le_div_iff_mul_le (pow_pos (sparsifyNu_pos hn) 2),
    Nat.le_sqrt']
  ring_nf

theorem sparsifySchedule_le_lambda (n : ℕ) : sparsifySchedule n ≤ sparsifyLambda n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem sparsifyLambda_le_log2_shift (n : ℕ) :
    sparsifyLambda n ≤ Nat.log2 (n + 16) + 1 := by
  apply (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp
  exact (Nat.le_add_right n 16).trans Nat.lt_log2_self.le

theorem sparsify_parameters_le_input (n : ℕ) :
    sparsifyLambda n ≤ n ∧ sparsifyNu n ≤ n ∧ sparsifySchedule n ≤ n := by
  have hLambda : sparsifyLambda n ≤ n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  have hNu : sparsifyNu n ≤ sparsifyLambda n :=
    (Nat.le_pow_iff_clog_le (by norm_num : 1 < (2 : ℕ))).mp Nat.lt_two_pow_self.le
  exact ⟨hLambda, hNu.trans hLambda, (sparsifySchedule_le_lambda n).trans hLambda⟩

theorem four_le_logb {n : ℕ} (hn : 20 ≤ n) : 4 ≤ Real.logb 2 n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < n by omega))).mpr
  norm_num
  exact_mod_cast (show 16 ≤ n by omega)

theorem sparsifyLambda_bounds {n : ℕ} (hn : 20 ≤ n) :
    Real.logb 2 n ≤ (sparsifyLambda n : ℝ) ∧
      (sparsifyLambda n : ℝ) ≤ 2 * Real.logb 2 n := by
  rw [sparsifyLambda_eq_ceil]
  have h := four_le_logb hn
  exact ⟨Nat.le_ceil _, by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.logb 2 n)
    linarith⟩

theorem sparsifyNu_le {n : ℕ} (hn : 20 ≤ n) :
    (sparsifyNu n : ℝ) ≤ 2 * Real.logb 2 (Real.logb 2 n) := by
  have hl := four_le_logb hn
  have hl0 : 0 < Real.logb 2 n := by linarith
  have hLambda := sparsifyLambda_bounds hn
  have hLambda0 : 0 < (sparsifyLambda n : ℝ) := by linarith
  have hv : 2 ≤ Real.logb 2 (Real.logb 2 n) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hl0).mpr
    norm_num
    exact hl
  have hlog : Real.logb 2 (sparsifyLambda n) ≤ 1 + Real.logb 2 (Real.logb 2 n) := by
    calc
      _ ≤ Real.logb 2 (2 * Real.logb 2 n) :=
        Real.logb_le_logb_of_le (by norm_num) hLambda0 hLambda.2
      _ = _ := by rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) hl0.ne']; norm_num
  have hlog0 : 0 ≤ Real.logb 2 (sparsifyLambda n) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  rw [sparsifyNu_eq_ceil]
  have := Nat.ceil_lt_add_one hlog0
  linarith

theorem sparsifySchedule_tendsto :
    Filter.Tendsto sparsifySchedule Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro a
  have hc : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : 0 < Real.log (2 : ℝ) ^ 4 / (16 * ((a : ℝ) + 1) ^ 2) := by positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound he
  have ht : Filter.Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually hsmall, Filter.eventually_ge_atTop (20 : ℕ)] with n hb hn
  have hl := four_le_logb hn
  have hl0 : 0 ≤ Real.logb 2 n := by linarith
  have hlog0 : 0 ≤ Real.log (Real.logb 2 n) := Real.log_nonneg (by linarith)
  have hb' : Real.log (Real.logb 2 n) ^ 4 ≤
      Real.log (2 : ℝ) ^ 4 / (16 * ((a : ℝ) + 1) ^ 2) * Real.logb 2 n := by
    simpa only [Function.id_def, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 4), abs_of_nonneg hl0] using hb
  have hnu := sparsifyNu_le hn
  have hnu4 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (sparsifyNu n)) hnu 4
  have heq : (2 * Real.logb 2 (Real.logb 2 n)) ^ 4 =
      16 * Real.log (Real.logb 2 n) ^ 4 / Real.log (2 : ℝ) ^ 4 := by
    unfold Real.logb
    ring_nf
  rw [heq] at hnu4
  have hmul : 16 * ((a : ℝ) + 1) ^ 2 * Real.log (Real.logb 2 n) ^ 4 ≤
      Real.log (2 : ℝ) ^ 4 * Real.logb 2 n := by
    have := (le_div_iff₀ (by positivity :
      0 < 16 * ((a : ℝ) + 1) ^ 2)).mp
      (show Real.log (Real.logb 2 n) ^ 4 ≤
        (Real.log (2 : ℝ) ^ 4 * Real.logb 2 n) /
          (16 * ((a : ℝ) + 1) ^ 2) by convert hb' using 1 <;> first | rfl | ring)
    nlinarith
  have ha : (a : ℝ) ^ 2 * (sparsifyNu n : ℝ) ^ 4 ≤ Real.logb 2 n := by
    apply (mul_le_mul_iff_right₀ (pow_pos hc 4)).mp
    have hp := mul_le_mul_of_nonneg_left
      ((le_div_iff₀ (pow_pos hc 4)).mp hnu4) (sq_nonneg (a : ℝ))
    have haa : (a : ℝ) ^ 2 ≤ ((a : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) a]
    nlinarith [mul_le_mul_of_nonneg_right haa
      (pow_nonneg hlog0 4)]
  apply (le_sparsifySchedule_iff hn a).2
  exact_mod_cast ha.trans (sparsifyLambda_bounds hn).1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le_bound (m B : ℕ) : degree m B ≤ degreeBound m B := min_le_right _ _

theorem eight_mul_le_degreeBound (m : ℕ) {B : ℕ} (hB : 0 < B) :
    8 * B ≤ degreeBound m B := by
  have hL : 1 ≤ logSize m := logSize_pos m
  have hq : B ≤ gapDenom m B := by unfold gapDenom; nlinarith
  have hqpos := gapDenom_pos m hB
  have hsq : gapDenom m B ≤ gapDenom m B ^ 2 := by nlinarith
  unfold degreeBound
  nlinarith

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_self {m : ℕ} (hm : 0 < m) : dimensionFor m m = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dimensionFor_le m hm (by simp)

theorem dimensionFor_lt_logSize (m : ℕ) {D : ℕ} (hD : 2 ≤ D) :
    dimensionFor m D < logSize m := by
  have hm := lt_two_pow_logSize m
  have hw : m ≤ D * 2 ^ (Nat.log 2 m) := by
    unfold logSize at hm
    rw [pow_succ] at hm
    nlinarith
  have hd := dimensionFor_le m (by omega : 0 < D) hw
  unfold logSize
  omega

theorem dimension_lt_logSize {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    dimension m B < logSize m := by
  by_cases h : degreeBound m B ≤ m
  · have hD : 2 ≤ degreeBound m B := by
      have := eight_mul_le_degreeBound m hB
      omega
    simpa [dimension, degree, min_eq_right h] using dimensionFor_lt_logSize m hD
  · have hd : degree m B = m := min_eq_left (by omega)
    simpa [dimension, hd, dimensionFor_self hm] using logSize_pos m

end SubexponentialSAT.SqrtLog.SparseCode

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

theorem code_degreeBound_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.degreeBound m B ≤ 320000*(q+2)^3*L n^(2*q+3) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.degreeBound SparseCode.gapDenom
  calc
    _ ≤ 8*(200*(L n^q)*((q+2)*L n))^2*((q+2)*L n) := by gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

open SparseCharging

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseExponent_le (k a b e : ℕ) (ha : 0 < a)
    (he : parameterTest k a b e = true) : chooseExponent k a b ha ≤ e :=
  Nat.find_min' (exists_parameter k a b ha) he

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha

/-- The first successful candidate inherits the sharp witness bound. Constants
are chosen before the rational budget numerator and denominator. -/
theorem choose_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a),
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 (inverseIndex a b) + 1) := by
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  let q := k - 2
  let T := 2 * (rightConstant k * (A + 2 + 4 * (q + 1) + 1) + 1)
  refine ⟨4 * 2 ^ T, T, ?_⟩
  intro a b ha
  let s := inverseIndex a b
  obtain ⟨T', e, _, hγ, hM, hbudget, hsize, hindex, hT⟩ :=
    dyadic_witness (depthConstant k) A q (rightConstant k) s
      (by exact Nat.zero_lt_succ _) (fun M hM => depthConstant_le k M hM)
  have he : parameterTest k a b e = true := by
    simp only [parameterTest, decide_eq_true_eq]
    refine ⟨hM, hγ, ?_⟩
    calc
      rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * b ≤
          rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * (a * s) :=
        Nat.mul_le_mul_left _ (inverseIndex_mul a b ha)
      _ = a * (rightConstant k * Nat.clog 2 (4 * depthConstant k (2 ^ e) * 2 ^ e) * s) := by ring
      _ ≤ a * 2 ^ e := Nat.mul_le_mul_left a hbudget
  have hmin := chooseExponent_le k a b e ha he
  have hT' : T' = T := hT
  subst T'
  exact ⟨(Nat.pow_le_pow_right (by decide) hmin).trans hsize, hmin.trans hindex⟩

theorem inverseIndex_le_denominator (a b : ℕ) (hb : 0 < b) : inverseIndex a b ≤ b := by
  have := Nat.div_le_self (b - 1) a
  dsimp [inverseIndex]
  omega

/-- Search length is logarithmic in the positive rational denominator; candidate
values remain polynomial in it. This exposes the uniform parameter-size budget. -/
theorem choose_encoding_bounds (k : ℕ) :
    ∃ K T : ℕ, ∀ a b (ha : 0 < a), 0 < b →
      chooseM k a b ha ≤ K * b ^ 2 ∧
      chooseExponent k a b ha ≤ T + 2 * (Nat.log 2 b + 1) := by
  obtain ⟨K, T, h⟩ := choose_bounds k
  refine ⟨K, T, ?_⟩
  intro a b ha hb
  have hs := inverseIndex_le_denominator a b hb
  have hlog : Nat.log 2 (inverseIndex a b) + 1 ≤ inverseIndex a b :=
    Nat.succ_le_of_lt (Nat.log_lt_self 2 (by exact Nat.succ_ne_zero _))
  constructor
  · calc
      chooseM k a b ha ≤ K * inverseIndex a b * (Nat.log 2 (inverseIndex a b) + 1) :=
        (h a b ha).1
      _ ≤ K * b * b := Nat.mul_le_mul (Nat.mul_le_mul_left K hs) (hlog.trans hs)
      _ = K * b ^ 2 := by ring
  · exact (h a b ha).2.trans (by have := Nat.log_mono_right (b := 2) hs; omega)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeSearchNativeBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical bounds for the actual graph-then-local code stage, including
all physical routing, saved outputs, and reused-bank cleanup. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
open SqrtLog SqrtLog.Asymptotic
open Filter
open scoped Topology

/-- The actual four code dimensions satisfy the original numerical height
estimate, uniformly over every leaf with the chosen occurrence cap. -/
theorem produced_dimensions_le (n m B q : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hmn : m ≤ n * B) (hBn : B ≤ L n ^ q) :
    let H := (320000 * (q + 2) ^ 3 + q + 4) * L n ^ (2 * q + 3)
    SparseCode.localRows m B ≤ H ∧ SparseCode.degree m B ≤ H ∧
      SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1 ≤ H ∧
      SparseCode.dimension m B ≤ H := by
  have hd := (SparseCode.degree_le_bound m B).trans
    (CostAssembly.code_degreeBound_le n m B q hmn hBn)
  have hl := CostAssembly.code_logSize_le n m B q hmn hBn
  have hp : L n ≤ L n ^ (2 * q + 3) := by
    simpa using Nat.pow_le_pow_right (L_pos n) (by omega : 1 ≤ 2 * q + 3)
  have hpos : 1 ≤ L n ^ (2 * q + 3) := Nat.one_le_pow _ _ (L_pos n)
  have height : SparseCode.degree m B + SparseCode.logSize m + 2 ≤
      (320000 * (q + 2) ^ 3 + q + 4) * L n ^ (2 * q + 3) := by nlinarith
  have ht := Nat.div_le_self (SparseCode.degree m B) (8 * B)
  have hdist := Nat.div_le_self (SparseCode.degree m B) (100 * B * SparseCode.logSize m)
  have hr := SparseCode.dimension_lt_logSize hm hB
  dsimp only
  unfold SparseCode.localRows
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeSearchNativeBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

theorem clauseRecords_body {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (clauseRecords F) = ExecQuantitativeSparsify.encodeRawFormula F := by
  simp only [clauseRecords, ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  rfl


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ResourceBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-degree numerical closure for measured streaming costs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog.Statement

/-- A fixed polynomial in an old measured cost and the input length preserves
exactly the supplied runtime scale. This assigns no cost to an implementation. -/
theorem fixedPolynomialCost_bound {C A K : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hK : 0 ≤ K) {d : ℕ} (hd : 1 ≤ d) (L n p oldCost newCost : ℕ)
    (hold : (oldCost : ℝ) ≤ runtimeBound C A d L n)
    (hnew : (newCost : ℝ) ≤ K * ((oldCost : ℝ) + L + 1) ^ p) :
    (newCost : ℝ) ≤ runtimeBound (K * (2 * C) ^ p) ((p : ℝ) * A) (d * p) L n := by
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hinput : (L : ℝ) + 1 ≤ runtimeBound C A d L n := by
    have hp : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) ^ d := by
      simpa using pow_le_pow_right₀ hbase hd
    have he : 1 ≤ (2 : ℝ) ^ (A * runtimeScale n) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
    exact hp.trans ((le_mul_of_one_le_left (by positivity) hC).trans
      (le_mul_of_one_le_right (by positivity) he))
  have hsum : (oldCost : ℝ) + L + 1 ≤ runtimeBound (2 * C) A d L n := by
    rw [runtimeBound_mul_constant]
    linarith
  calc
    (newCost : ℝ) ≤ K * ((oldCost : ℝ) + L + 1) ^ p := hnew
    _ ≤ K * runtimeBound (2 * C) A d L n ^ p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum p) hK
    _ = _ := by rw [runtimeBound_pow, runtimeBound_mul_constant]

/-- The native dyadic parameter program returns exactly this larger cap,
which bounds leaf occurrences and remains polynomial in the ceiling log. -/
theorem chosen_sparseBound_le_lambda (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        C * sparsifyLambda n ^ (2 * (k - 1)) := by
  obtain ⟨K, T, hK⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  refine ⟨4 * K ^ (k - 1), ?_⟩
  intro n hs
  have hM := (hK 1 (sparsifySchedule n) (by omega) (by omega)).1
  calc
    _ ≤ 4 * (K * sparsifySchedule n ^ 2) ^ (k - 1) := by gcongr
    _ ≤ 4 * (K * sparsifyLambda n ^ 2) ^ (k - 1) := by
      gcongr
      exact sparsifySchedule_le_lambda n
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The chosen occurrence cap satisfies the original incidence algorithm's
integer logarithm hypothesis above a cutoff depending only on the width. -/
theorem chosen_sparseBound_eventually_le_log2_power (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
          (Nat.log2 (n + 16) + 1) ^ (2 * (k - 1) + 1) := by
  obtain ⟨C, hC⟩ := chosen_sparseBound_le_lambda k
  filter_upwards [sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1),
    Filter.eventually_ge_atTop (2 ^ C)] with n hs hn
  have hlog : C ≤ Nat.log2 (n + 16) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le (by norm_num) (hn.trans (Nat.le_add_right n 16))
  calc
    _ ≤ C * sparsifyLambda n ^ (2 * (k - 1)) := hC n hs
    _ ≤ (Nat.log2 (n + 16) + 1) *
        (Nat.log2 (n + 16) + 1) ^ (2 * (k - 1)) :=
      Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left (sparsifyLambda_le_log2_shift n) _)
    _ = _ := by rw [pow_succ]; ac_rfl

theorem formulaBound_polynomial (n k : ℕ) :
    DisjointReuse.SparseCountProgram.formulaBound n k ≤
      (2 + (4 + 8 * k) * (k + 1) * 2 ^ k) * (n + 1) ^ (k + 1) := by
  have hbase : 1 ≤ n + 1 := by omega
  have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ k + 1 by omega)
  have hcoef : 4 + (8 * n + 8) * k ≤ (4 + 8 * k) * (n + 1) := by nlinarith
  have hpow : (2 * n + 1) ^ k ≤ 2 ^ k * (n + 1) ^ k := by
    simpa [mul_pow] using Nat.pow_le_pow_left (show 2 * n + 1 ≤ 2 * (n + 1) by omega) k
  unfold DisjointReuse.SparseCountProgram.formulaBound
  calc
    _ ≤ 2 * (n + 1) ^ (k + 1) +
        ((4 + 8 * k) * (n + 1)) * ((k + 1) * (2 ^ k * (n + 1) ^ k)) := by
      apply Nat.add_le_add
      · omega
      · exact Nat.mul_le_mul hcoef (Nat.mul_le_mul_left (k + 1) hpow)
    _ = _ := by rw [pow_succ]; ring


/-- The actual disjoint occurrence choice is bounded in original input
length, with coefficients and degree fixed by the width. -/
theorem chosen_sparseBound_le_input (k : ℕ) :
    ∃ K : ℕ, ∀ n inputLength : ℕ, n ≤ inputLength → 1 ≤ sparsifySchedule n →
      4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1) ≤
        K * (inputLength + 1) ^ (2 * (k - 1)) := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_lambda k
  refine ⟨K, ?_⟩
  intro n inputLength hn hs
  apply (hK n hs).trans
  apply Nat.mul_le_mul_left K
  apply Nat.pow_le_pow_left
  exact (sparsify_parameters_le_input n).1.trans (by omega)

/-- The complete ordinary size used by native leaf preparation is a fixed
input polynomial for the actual occurrence choice and sparse leaf count.
Physical input words remain independently bounded by their proved producer. -/
theorem chosen_leaf_input_cap (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      n + m + B + W + 16 ≤ C * (inputLength + 1) ^ degree := by
  obtain ⟨K, hK⟩ := chosen_sparseBound_le_input k
  refine ⟨2 * K + wordCoefficient + 17, 2 * (k - 1) + wordDegree + 1, ?_⟩
  intro n inputLength m W hn hs B hm hW
  let X := inputLength + 1
  let degree := 2 * (k - 1) + wordDegree + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B ≤ K * X ^ (2 * (k - 1)) := hK n inputLength hn hs
  have hm' : m ≤ K * X ^ (2 * (k - 1) + 1) := by
    calc
      _ ≤ n * B := hm
      _ ≤ X * (K * X ^ (2 * (k - 1))) :=
        Nat.mul_le_mul (by dsimp [X]; omega) hB
      _ = _ := by rw [pow_succ']; ring
  have hB' : B ≤ K * X ^ degree := hB.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hm'' : m ≤ K * X ^ degree := hm'.trans
    (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hW' : W ≤ wordCoefficient * X ^ degree := hW.trans
    (Nat.mul_le_mul_left wordCoefficient (Nat.pow_le_pow_right hX (by dsimp [degree]; omega)))
  have hlin : X ≤ X ^ degree := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ degree by dsimp [degree]; omega)
  have h1 : 1 ≤ X ^ degree := Nat.one_le_pow _ _ hX
  change _ ≤ (2 * K + wordCoefficient + 17) * X ^ degree
  have hn' : n ≤ X := by dsimp [X]; omega
  nlinarith only [hB', hm'', hW', hlin, h1, hn']

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_LeafPreparationBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Numerical resources of the actual full leaf-preparation command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
open SqrtLog SqrtLog.LeafOuterProgram NativeLeafPreparation NativeCodeAssembly
open CodeSearchNativeBudgets


/-- The actual disjoint choice and loaded input-word cap fix one polynomial
common selector boundary in original input length before all leaf calls. -/
theorem chosen_prepared_common_bound (k wordCoefficient wordDegree : ℕ) :
    ∃ C degree : ℕ, ∀ n inputLength m W : ℕ,
      0 < n → 0 < m → n ≤ inputLength → 1 ≤ sparsifySchedule n →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : StructuredCalls.State 40 896, (∀ i, (a.stacks i).length ≤ L) →
      LeafOuterProgram.Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      max (max (L + 1) (continuationSpace m B L a prepared))
        (NativeLeafRun.commonBound n m B (retainedBound m B L a prepared)) ≤
          C * (inputLength + 1) ^ degree := by
  obtain ⟨C, degree, hprep⟩ := prepared_common_bound_polynomial
  obtain ⟨K, exponent, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  refine ⟨C * K ^ degree, exponent * degree, ?_⟩
  intro n inputLength m W hn hm hinput hs B hmb hW L a prepared ha hmeta hp
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have h := hprep n m B W hn hm hB hmb a prepared ha hmeta hp
  have hcap := hsize n inputLength m W hinput hs hmb hW
  apply h.trans
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hcap degree)
  simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hh


open SqrtLog.CodeSetupCost

open Filter SqrtLog.Asymptotic SqrtLog.Statement
open scoped Topology

private theorem preparation_envelope_runtimeBound
    (K e C p inputLength n A E newCost : ℕ)
    (hA : A + 1 ≤ K * (inputLength + 1) ^ e)
    (hE : (E : ℝ) ≤ ((A : ℝ) + 1) ^ 6 * (2 : ℝ) ^ runtimeScale n)
    (hnew : newCost ≤ C * (inputLength + E + 1) ^ p) :
    (newCost : ℝ) ≤ runtimeBound
      (((C : ℝ) + 1) * (2 * ((K : ℝ) + 1) ^ 6) ^ p)
      p ((e * 6 + 1) * p) inputLength n := by
  have hK : (1 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 K
  have hbase : (1 : ℝ) ≤ (inputLength : ℝ) + 1 := by
    exact_mod_cast Nat.le_add_left 1 inputLength
  have hword : ((A : ℝ)+1)^6 ≤ ((K : ℝ)+1)^6 *
      ((inputLength : ℝ)+1)^(e*6+1) := by
    have hAR : (A : ℝ)+1 ≤ (K : ℝ)*((inputLength : ℝ)+1)^e := by exact_mod_cast hA
    have hpow := pow_le_pow_left₀ (by positivity) hAR 6
    rw [mul_pow, ←pow_mul] at hpow
    exact hpow.trans (mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith) 6)
      (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity))
  have hEbound : (E : ℝ) ≤ runtimeBound (((K : ℝ)+1)^6) 1 (e*6+1) inputLength n := by
    apply hE.trans
    simpa only [runtimeBound,one_mul] using
      mul_le_mul_of_nonneg_right hword (Real.rpow_nonneg (by norm_num) _)
  have hnewR : (newCost : ℝ) ≤ ((C : ℝ)+1)*((E : ℝ)+inputLength+1)^p := by
    have hR : (newCost : ℝ) ≤ (C : ℝ)*((inputLength : ℝ)+E+1)^p := by
      exact_mod_cast hnew
    apply hR.trans
    rw [show (inputLength : ℝ)+E+1=(E : ℝ)+inputLength+1 by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hfinal := fixedPolynomialCost_bound (one_le_pow₀ hK (n := 6))
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (C : ℝ)+1)
    (show 1 ≤ e*6+1 by omega) inputLength n p E newCost hEbound hnewR
  simpa only [mul_one] using hfinal

/-- All actual preparation costs satisfy the unchanged runtime scale above a
fixed cutoff. Both the dimension envelope and its physical word factor are
derived from the chosen occurrence bound and actual metadata producer caps. -/
theorem chosen_preparation_runtimeBound (k wordCoefficient wordDegree : ℕ) :
    ∃ C : ℝ, ∃ exponent degree cutoff : ℕ, 1 ≤ C ∧
      ∀ n inputLength m W : ℕ, cutoff ≤ n → 0 < m → n ≤ inputLength →
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B → W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree →
      let L := W + NativeLeafSetup.canonicalStartTime n m W
      ∀ a prepared : Data, (∀ i, (a.stacks i).length ≤ L) →
      Metadata m B prepared →
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime m B L
        (a.stacks 782).length (a.stacks 786).length) →
      ((NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared : ℕ) : ℝ) ≤
        runtimeBound C exponent degree inputLength n := by
  obtain ⟨Ct, dt, htime⟩ := chosen_preparation_time_envelope k wordCoefficient wordDegree
  obtain ⟨Cs, ds, hsize⟩ := chosen_leaf_input_cap k wordCoefficient wordDegree
  obtain ⟨Cm, dm, hmetaSize⟩ := NativeLeafSetup.canonicalParameterTime_polynomial
  let qi := 2*(k-1)+1
  let heightCoefficient := 320000*(qi+2)^3+qi+4
  obtain ⟨cutoff,hcutoff⟩ := Filter.eventually_atTop.mp
    (((chosen_sparseBound_eventually_le_log2_power k).and
      (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))).and
      (eventually_envelope_with_words 3000000000000 heightCoefficient (2*qi+3)))
  let K := Cm * Cs ^ dm
  let codeDegree := ds*dm*6+1
  let codeCoefficient : ℝ := ((K : ℝ)+1)^6
  refine ⟨((Ct : ℝ)+1)*(2*codeCoefficient)^dt,dt,codeDegree*dt,cutoff,?_,?_⟩
  · have hK : 1 ≤ codeCoefficient := by dsimp [codeCoefficient]; exact one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 K)
    have hpow : 1 ≤ (2*codeCoefficient)^dt := one_le_pow₀ (by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) Ct]
  intro n inputLength m W hn hm hinput B hmb hW L a prepared ha hmeta hp
  obtain ⟨⟨hBn,hs⟩,hcode⟩ := hcutoff n hn
  have hB : 0 < B := by
    have hM := (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    dsimp [B]
    positivity
  have hBpoly : B ≤ Asymptotic.L n ^ qi := by simpa only [B,qi,Asymptotic.L] using hBn
  let H := heightCoefficient * Asymptotic.L n ^ (2*qi+3)
  let A := L + NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  have hordinary := hsize n inputLength m W hinput hs hmb hW
  have hmetaOrd := hmetaSize n m B W _ _ hm hB (ha 782) (ha 786)
  have hX : n+m+W+16 ≤ Cs*(inputLength+1)^ds := by
    change n+m+B+W+16 ≤ _ at hordinary
    omega
  have hA : A+1 ≤ K*(inputLength+1)^(ds*dm) := by
    apply hmetaOrd.trans
    have h := Nat.mul_le_mul_left Cm (Nat.pow_le_pow_left hX dm)
    simpa only [K,mul_pow,←pow_mul,Nat.mul_assoc] using h
  obtain ⟨ht,hD,hd,hr⟩ := produced_dimensions_le n m B qi hm hB hmb hBpoly
  have htimeNat := htime n inputLength m W H A hm hinput hs hmb hW a prepared
    ha hmeta hp ht hD hd hr (hp 800) (hp 801)
  let E := envelope 3000000000000 H A
  have hE := hcode H A le_rfl
  exact preparation_envelope_runtimeBound K (ds*dm) Ct dt inputLength n A E
    (NativeLeafSetup.canonicalStartTime n m W + continuationTime m B L a prepared)
    hA hE htimeNat
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

/-- The actual loader uses exactly the body, ambient word and independent
setup-parameter cap. Their sum is polynomial in the original input length,
with coefficients and degree fixed before the input is chosen. -/
theorem loaded_input_bound (k parameterCoefficient parameterDegree n inputLength parameterBound : ℕ)
    (hn : n ≤ inputLength)
    (hp : parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree) :
    SparseCountProgram.formulaBound n k + (n + 1) + parameterBound ≤
      (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) *
        (inputLength + 1) ^ (k + 1 + parameterDegree) := by
  let P := (inputLength + 1) ^ (k + 1 + parameterDegree)
  have hb : 1 ≤ inputLength + 1 := by omega
  have hformula := formulaBound_polynomial n k
  have hbase : (n + 1) ^ (k + 1) ≤ P :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ inputLength + 1) (k + 1)).trans
      (Nat.pow_le_pow_right hb (by omega))
  have hparameter : (inputLength + 1) ^ parameterDegree ≤ P :=
    Nat.pow_le_pow_right hb (by omega)
  have hlinear : n + 1 ≤ P := by
    apply (show n + 1 ≤ inputLength + 1 by omega).trans
    simpa only [pow_one] using Nat.pow_le_pow_right hb
      (show 1 ≤ k + 1 + parameterDegree by omega)
  have hf := hformula.trans (Nat.mul_le_mul_left _ hbase)
  have hp' := hp.trans (Nat.mul_le_mul_left parameterCoefficient hparameter)
  change _ ≤ (3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient) * P
  nlinarith only [hf, hp', hlinear]

open SqrtLog Filter
open scoped Topology

/-- Execute preparation on the actual three loaded words and bind its time,
retained common bound and all-prefix storage to constants chosen before the
input. Both code matrices and the first-query blank workspace are produced
by this run, rather than provided by a successful-code hypothesis. -/
theorem prepared_loaded_oai (k parameterCoefficient parameterDegree : ℕ) :
    ∃ C degree : ℕ, ∃ Ct : ℝ, ∃ exponent timeDegree cutoff : ℕ, 1 ≤ Ct ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ (steps : ℕ) (started prepared base : State 40 896)
        (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
        let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
        let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
        let L := NativeLeafRun.commonBound n F.length B R
        Eval NativeLeafPreparation.command steps a base ∧
        (steps : ℝ) ≤ Statement.runtimeBound Ct exponent timeDegree inputLength n ∧
        (∀ i, (started.stacks i).length ≤ startup) ∧
        LeafOuterProgram.Metadata F.length B prepared ∧
        (∀ i, (prepared.stacks i).length ≤ startup +
          NativeLeafSetup.parameterTime F.length B startup
            (started.stacks 782).length (started.stacks 786).length) ∧
        NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base ∧
        WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
        SparseCode.HasDistance Q (SparseCode.degree F.length B /
          (100 * B * SparseCode.logSize F.length) + 1) ∧
        base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
        BinaryArithmetic.toNat (base.stacks 785) = n ∧
        (∀ i, (base.stacks i).length ≤ R) ∧
        (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
          base.stacks i = []) ∧
        L ≤ C * (inputLength + 1) ^ degree ∧
        ∀ t z, t ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) t
          (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
          ∀ i, (z.stacks i).length ≤ C * (inputLength + 1) ^ degree := by
  let wordCoefficient := 3 + (4 + 8 * k) * (k + 1) * 2 ^ k + parameterCoefficient
  let wordDegree := k + 1 + parameterDegree
  obtain ⟨C, degree, hcommon⟩ :=
    LeafPreparationBudgets.chosen_prepared_common_bound k wordCoefficient wordDegree
  obtain ⟨Ct, exponent, timeDegree, cutoff₁, hCt, htime⟩ :=
    LeafPreparationBudgets.chosen_preparation_runtimeBound k wordCoefficient wordDegree
  obtain ⟨cutoff₂, hschedule⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨C, degree, Ct, exponent, timeDegree, max (max cutoff₁ cutoff₂) 1, hCt, ?_⟩
  intro n inputLength parameterBound hcut hnI hp B W F a hne hmB ha hempty hformula hn hBword
  have hnpos : 0 < n := by omega
  have hm : 0 < F.length := List.length_pos_iff.mpr hne
  have hs : 1 ≤ sparsifySchedule n := hschedule n (by omega)
  have hB : 0 < B := by
    dsimp only [B]
    have hM := (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
    positivity
  have hW : W ≤ wordCoefficient * (inputLength + 1) ^ wordDegree :=
    loaded_input_bound k parameterCoefficient parameterDegree n inputLength parameterBound hnI hp
  obtain ⟨steps, started, prepared, base, shifts, Q, hsteps, he, hstarted, _hmword,
    _hmodulus, hmetadata, hprepared, hready, hgood, hdistance, hframe, hbound, hprefix, hupper⟩ :=
    NativeLeafRun.prepare_raw F a ha hempty hformula hne hB hn hBword
  have hc := hcommon n inputLength F.length W hnpos hm hnI hs hmB hW
    started prepared hstarted hmetadata hprepared
  have ht := htime n inputLength F.length W (by omega) hm hnI hmB hW
    started prepared hstarted hmetadata hprepared
  refine ⟨steps, started, prepared, base, shifts, Q, he, ?_, hstarted, hmetadata,
    hprepared, hready, hgood, hdistance, ?_, ?_, hbound, hupper,
    (Nat.le_max_right _ _).trans hc, ?_⟩
  · exact (Nat.cast_le.mpr hsteps).trans ht
  · exact (hframe 784 (by decide) (by decide)).trans
      (hformula.trans (NativeTerminal.clauseRecords_body F).symm)
  · rw [hframe 785 (by decide) (by decide)]
    exact hn
  · intro t z htz hz i
    exact (hprefix t z htz hz i).trans ((Nat.le_max_left _ _).trans hc)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded_oai

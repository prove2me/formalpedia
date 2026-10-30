-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:47:52.451324+00:00
-- url     : https://prove2.me/submissions/9e8c9037-8f58-41e4-95e0-9259d636f77f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem log_log_shift_pos (n : ℕ) : 0 < Real.log (Real.log ((n : ℝ) + 16)) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) (two_le_log_shift n))

theorem runtimeScale_nonneg (n : ℕ) : 0 ≤ runtimeScale n := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (Real.sqrt_nonneg _)

theorem runtimeBound_nonneg {constant : ℝ} (hc : 0 ≤ constant)
    (exponentConstant : ℝ) (degree inputBits numVars : ℕ) :
    0 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  positivity

theorem one_le_runtimeBound {constant exponentConstant : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant)
    (degree inputBits numVars : ℕ) :
    1 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le hc
      (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) inputBits; linarith))
  · exact Real.one_le_rpow (by norm_num) (mul_nonneg ha (runtimeScale_nonneg numVars))

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Asymptotics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem sparsifySchedule_maximal {n : ℕ} (hn : 20 ≤ n) :
    sparsifyLambda n < (sparsifySchedule n + 1) ^ 2 * sparsifyNu n ^ 4 := by
  have h := (le_sparsifySchedule_iff hn (sparsifySchedule n + 1)).not
  exact Nat.lt_of_not_ge (h.mp (by omega))

theorem sparsifySchedule_le_lambda (n : ℕ) : sparsifySchedule n ≤ sparsifyLambda n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

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

theorem inverse_sparsifySchedule_le {n : ℕ} (hn : 20 ≤ n)
    (hs : 1 ≤ sparsifySchedule n) : (n : ℝ) / sparsifySchedule n ≤ 8 * rho n := by
  have hl := four_le_logb hn
  have hl0 : 0 < Real.logb 2 n := by linarith
  have hLambda := (sparsifyLambda_bounds hn).1
  have hm : (sparsifyLambda n : ℝ) <
      ((sparsifySchedule n : ℝ) + 1) ^ 2 * (sparsifyNu n : ℝ) ^ 4 := by
    exact_mod_cast sparsifySchedule_maximal hn
  have hroot : Real.sqrt (Real.logb 2 n) ≤
      ((sparsifySchedule n : ℝ) + 1) * (sparsifyNu n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (sparsifyLambda n : ℝ) := hLambda
      _ ≤ ((sparsifySchedule n : ℝ) + 1) ^ 2 * (sparsifyNu n : ℝ) ^ 4 := hm.le
      _ = _ := by ring_nf
  have hv : 0 ≤ Real.logb 2 (Real.logb 2 n) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hnu := sparsifyNu_le hn
  have hnu2 : (sparsifyNu n : ℝ) ^ 2 ≤
      4 * (Real.logb 2 (Real.logb 2 n)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (sparsifyNu n)]
  have hs' : (1 : ℝ) ≤ sparsifySchedule n := by exact_mod_cast hs
  have hroot' : Real.sqrt (Real.logb 2 n) ≤
      8 * (sparsifySchedule n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hnu2
      (show 0 ≤ (sparsifySchedule n : ℝ) + 1 by positivity)
    nlinarith [sq_nonneg (Real.logb 2 (Real.logb 2 n))]
  unfold rho
  rw [show 8 * ((n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2 /
      Real.sqrt (Real.logb 2 n)) =
    (8 * (n : ℝ) * (Real.logb 2 (Real.logb 2 n)) ^ 2) /
      Real.sqrt (Real.logb 2 n) by ring_nf]
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < sparsifySchedule n)
    (Real.sqrt_pos.2 hl0)).2
  have := mul_le_mul_of_nonneg_left hroot' (Nat.cast_nonneg n)
  nlinarith

theorem rho_le_thirtyTwo_runtimeScale {n : ℕ} (hn : 20 ≤ n) :
    rho n ≤ 32 * SqrtLog.Statement.runtimeScale n := by
  let c : ℝ := Real.log 2
  let l : ℝ := Real.logb 2 n
  let v : ℝ := Real.logb 2 l
  let y : ℝ := Real.log ((n : ℝ) + 16)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc1 : c ≤ 1 := by
    simpa [c] using (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      |>.trans (by norm_num))
  have hc2 : (1 : ℝ) / 2 ≤ c := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    dsimp [c]
    linarith
  have hl : 4 ≤ l := four_le_logb hn
  have hl0 : 0 < l := by linarith
  have hy0 : 0 < y := SqrtLog.Statement.log_shift_pos n
  have hy2 : 2 ≤ y := SqrtLog.Statement.two_le_log_shift n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hcl : c * l = Real.log n := by dsimp [c, l, Real.logb]; field_simp
  have hcv : c * v = Real.log l := by dsimp [c, v, Real.logb]; field_simp
  have hyl : c * l ≤ y := by
    rw [hcl]
    exact Real.log_le_log hn0 (by linarith)
  have hly : l ≤ 2 * y := by nlinarith
  have hyu : y ≤ 2 * l := by
    have hm : y ≤ Real.log ((2 : ℝ) * n) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne', ← hcl] at hm
    change y ≤ c + c * l at hm
    nlinarith
  have hlogyc : c ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  have hlogy0 : 0 ≤ Real.log y := (SqrtLog.Statement.log_log_shift_pos n).le
  have hv : 0 ≤ v := Real.logb_nonneg (by norm_num) (by linarith)
  have hvu : v ≤ 4 * Real.log y := by
    have h : Real.log l ≤ Real.log (2 * y) := Real.log_le_log hl0 hly
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy0.ne', ← hcv] at h
    change c * v ≤ c + Real.log y at h
    nlinarith
  have hroot : Real.sqrt y ≤ 2 * Real.sqrt l := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hl0.le]
    nlinarith
  have hvsq : v ^ 2 ≤ 16 * Real.log y ^ 2 := by nlinarith
  change (n : ℝ) * v ^ 2 / Real.sqrt l ≤
    32 * ((n : ℝ) * Real.log y ^ 2 / Real.sqrt y)
  rw [show 32 * ((n : ℝ) * Real.log y ^ 2 / Real.sqrt y) =
    (32 * (n : ℝ) * Real.log y ^ 2) / Real.sqrt y by ring_nf]
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hl0) (Real.sqrt_pos.2 hy0)).2
  calc
    (n : ℝ) * v ^ 2 * Real.sqrt y ≤
        (n : ℝ) * (16 * Real.log y ^ 2) * (2 * Real.sqrt l) := by gcongr
    _ = _ := by ring_nf

theorem inverse_sparsifySchedule_target {n : ℕ} (hn : 20 ≤ n)
    (hs : 1 ≤ sparsifySchedule n) :
    (n : ℝ) / sparsifySchedule n ≤ 256 * SqrtLog.Statement.runtimeScale n := by
  have := inverse_sparsifySchedule_le hn hs
  have := rho_le_thirtyTwo_runtimeScale hn
  linarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ResourceBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-degree numerical closure for measured streaming costs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog.Statement

/-- The depth factor in the disjoint tree bound is a fixed-degree input
polynomial for the actual selected threshold. -/
theorem chosen_depth_polynomial (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ sparsifySchedule n →
      DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 ≤
          C * (n + 1) ^ (2 * (k - 2) + 1) := by
  obtain ⟨K, T, hK⟩ := DisjointReuse.SparseBudget.choose_encoding_bounds k
  let A := 4 * (k - 1) * 3 ^ (k - 2)
  refine ⟨A * K ^ (k - 2) + 1, ?_⟩
  intro n hs
  have hM := (hK 1 (sparsifySchedule n) (by omega) (by omega)).1
  have hsle : sparsifySchedule n ≤ n + 1 := (sparsify_parameters_le_input n).2.2.trans
    (Nat.le_succ n)
  have hM' : DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ≤
      K * (n + 1) ^ 2 := hM.trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hsle 2))
  have hdepth := DisjointReuse.SparseBudget.depthConstant_le k
    (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega))
    (DisjointReuse.SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
  have hpow : 1 ≤ (n + 1) ^ (2 * (k - 2) + 1) := Nat.one_le_pow' _ n
  calc
    _ ≤ (A * (K * (n + 1) ^ 2) ^ (k - 2)) * (n + 1) + 1 := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul (hdepth.trans (Nat.mul_le_mul_left A
        (Nat.pow_le_pow_left hM' _))) (Nat.le_succ n)
    _ = A * K ^ (k - 2) * (n + 1) ^ (2 * (k - 2) + 1) + 1 := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring
    _ ≤ _ := by nlinarith

/-- Numerical tree size for the actual reciprocal schedule. The result is
an envelope for visits; each native visit still needs its measured cost. -/
theorem chosen_treeBudget_runtimeBound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n inputBits : ℕ, 20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ inputBits →
      (((DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n)) ≤
        runtimeBound C 256 (4 * (k - 2) + 2) inputBits n := by
  obtain ⟨C, hC⟩ := chosen_depth_polynomial k
  refine ⟨((C : ℝ) + 1) ^ 2, by nlinarith [Nat.cast_nonneg (α := ℝ) C], ?_⟩
  intro n inputBits hn hs hinput
  have hdepth :
      ((DisjointReuse.SparseCharging.depthConstant k
        (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 : ℕ) : ℝ) ≤
          ((C : ℝ) + 1) * ((inputBits : ℝ) + 1) ^ (2 * (k - 2) + 1) := by
    have h := hC n hs
    have h' :
        DisjointReuse.SparseCharging.depthConstant k
          (DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega)) * n + 1 ≤
            (C + 1) * (inputBits + 1) ^ (2 * (k - 2) + 1) :=
      h.trans (Nat.mul_le_mul (Nat.le_succ C)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) _))
    exact_mod_cast h'
  unfold runtimeBound
  calc
    _ ≤ (((C : ℝ) + 1) * ((inputBits : ℝ) + 1) ^ (2 * (k - 2) + 1)) ^ 2 *
        (2 : ℝ) ^ (256 * runtimeScale n) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hdepth 2
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (inverse_sparsifySchedule_target hn hs)
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow, ← pow_mul, show (2 * (k - 2) + 1) * 2 = 4 * (k - 2) + 2 by omega]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionFinalCostAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.FinalCost
open SubexponentialSAT.SqrtLog.Statement

theorem runtimeBound_product (C A D B : ℝ) (d e L n : ℕ) :
    runtimeBound C A d L n * runtimeBound D B e L n =
      runtimeBound (C*D) (A+B) (d+e) L n := by
  unfold runtimeBound
  rw [pow_add]
  rw [show (A+B)*runtimeScale n=A*runtimeScale n+B*runtimeScale n by ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  ring

end SubexponentialSAT.SqrtLog.Execution.FinalCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact large-entry arithmetic join: paid canonical frontend, fixed
cutoff test, actual setup, disjoint DFS, full-word positivity and factor-seven
primitive compilation. These numerical bounds introduce no run contract. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse

/-- The actual reciprocal-sparsification visits multiply the actual leaf
budget. Their exponents add; the ETH square-root-log scale stays unchanged. -/
theorem runtime_of_tree_and_leaf_oai (k coefficient degree : ℕ)
    (leafConstant leafExponent : ℝ) (hC : 1≤leafConstant) (hA : 0≤leafExponent)
    (leafDegree : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ n L visits leafTime primitiveTime : ℕ,
      20 ≤ n → 1 ≤ sparsifySchedule n → n ≤ L →
      (visits : ℝ)≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide))*n+1 : ℕ) : ℝ)^2*
          (2 : ℝ)^((n : ℝ)/sparsifySchedule n) →
      (leafTime : ℝ) ≤ runtimeBound leafConstant leafExponent leafDegree L n →
      primitiveTime ≤ coefficient*(L+1)^degree*(visits+1)*(leafTime+1) →
      (primitiveTime : ℝ) ≤ runtimeBound C (256+leafExponent)
        (degree+(4*(k-2)+2)+leafDegree) L n := by
  obtain ⟨T,hT,htree⟩ := chosen_treeBudget_runtimeBound k
  refine ⟨4*((coefficient : ℝ)+1)*T*leafConstant,?_,?_⟩
  · have hcoeff : 1≤(coefficient : ℝ)+1 := by
      have := Nat.cast_nonneg (α := ℝ) coefficient
      linarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hcoeff) hT) hC
  intro n L visits leafTime primitiveTime hn hs hLn hvisits hleaf htime
  have hv := hvisits.trans (htree n L hn hs hLn)
  have hv1 := one_le_runtimeBound hT (by norm_num : (0 : ℝ)≤256)
    (4*(k-2)+2) L n
  have hl1 := one_le_runtimeBound hC hA leafDegree L n
  have hvplus : (visits : ℝ)+1≤2*runtimeBound T 256 (4*(k-2)+2) L n := by linarith
  have hlplus : (leafTime : ℝ)+1≤2*runtimeBound leafConstant leafExponent leafDegree L n := by linarith
  have hcast : (primitiveTime : ℝ)≤(coefficient : ℝ)*((L : ℝ)+1)^degree*
      ((visits : ℝ)+1)*((leafTime : ℝ)+1) := by exact_mod_cast htime
  calc
    _ ≤ (coefficient : ℝ)*((L : ℝ)+1)^degree*
      (2*runtimeBound T 256 (4*(k-2)+2) L n)*
      (2*runtimeBound leafConstant leafExponent leafDegree L n) := by
        apply hcast.trans
        gcongr
    _ ≤ 4*((coefficient : ℝ)+1)*((L : ℝ)+1)^degree*
      (runtimeBound T 256 (4*(k-2)+2) L n*
        runtimeBound leafConstant leafExponent leafDegree L n) := by
      have h := Nat.cast_nonneg (α := ℝ) coefficient
      have hp : 0≤((L : ℝ)+1)^degree := by positivity
      have ht0 := runtimeBound_nonneg (by linarith : 0≤T) 256 (4*(k-2)+2) L n
      have hl0 := runtimeBound_nonneg (by linarith : 0≤leafConstant) leafExponent leafDegree L n
      nlinarith only [mul_nonneg hp (mul_nonneg ht0 hl0)]
    _ = runtimeBound (4*((coefficient : ℝ)+1)*T*leafConstant) (256+leafExponent)
        (degree+(4*(k-2)+2)+leafDegree) L n := by
      rw [SqrtLog.Execution.FinalCost.runtimeBound_product]
      unfold runtimeBound
      rw [pow_add,pow_add]
      ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets.runtime_of_tree_and_leaf_oai

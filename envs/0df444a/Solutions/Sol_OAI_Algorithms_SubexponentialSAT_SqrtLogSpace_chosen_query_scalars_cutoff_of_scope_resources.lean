-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:00:02.981018+00:00
-- url     : https://prove2.me/submissions/93ca61e2-53d9-409e-bf96-8d2990637fac

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_sparse_parameter_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_eventually_scan_bounds_of_scope_resources

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

theorem chooseExponent_le (k a b e : ℕ) (ha : 0 < a)
    (he : parameterTest k a b e = true) : chooseExponent k a b ha ≤ e :=
  Nat.find_min' (exists_parameter k a b ha) he

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

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

end SubexponentialSAT.SqrtLog.Asymptotic

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

theorem totals_incidences (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).incidences =
      t.incidences + scanSum (fun i => max 1 (degree scopes i)) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem incidences_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).incidences = totalScope (completedScope scopes mask) := by
  rw [totals_incidences, scanSum_eq_free_sum]
  simp only [zero, Nat.zero_add]
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [completed_degree]

theorem occurrence_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).occurrence =
      Finset.univ.sup (Incidence.degree (completedScope scopes mask)) := by
  apply Nat.le_antisymm
  · rw [totals_occurrence_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i hi
    simp only [List.get_eq_getElem] at hi
    let v : Free mask := ⟨i, by simp [hi]⟩
    simpa only [Nat.zero_add, completed_degree] using
      (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v))
  · apply Finset.sup_le
    intro v _
    have h := (totals_occurrence_le_iff scopes 0 mask zero
      (variableTotals scopes 0 mask zero).occurrence).mp le_rfl
    simpa only [Nat.zero_add, completed_degree] using h.2 v.val (free_bit mask v)

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputStats
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The address stream and the native statistics use the same mask scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats
open SubexponentialSAT.Subexp
open LeafStatisticsProgram

theorem native_incidence_count (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Loop.plans scopes n 0 scopes.length mask).length =
      (variableTotals scopes 0 mask zero).incidences := by
  rw [Semantics.plans_eq,List.length_map]
  simpa [zero] using entries_agree scopes mask 0 scopes.length zero
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramControllerResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary sizes of the actual all-row bucket input.  The row count here
is the length of the emitted incidence plan, and is never replaced by rank. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

open scoped BigOperators
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem native_rows_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (PackingIncidenceInput.Loop.plans scopes n 0 scopes.length mask).length ≤
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).free *
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).occurrence := by
  rw [PackingIncidenceInput.Stats.native_incidence_count]
  change (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).incidences ≤ _
  rw [LeafStatisticsSemantics.incidences_exact, LeafStatisticsSemantics.free_exact,
    LeafStatisticsSemantics.occurrence_exact, HighIncidence.totalScope, ← Incidence.sum_degrees]
  calc
    _ ≤ ∑ _v : LeafStatisticsSemantics.Free mask,
        Finset.univ.sup (Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.le_sup (f := Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask))
        (Finset.mem_univ v)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

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

 theorem input_mass_le (q : Query) (k : ℕ) :
    (q.input k).incidences ≤ (q.input k).freeCount*(q.input k).occurrence := by
  have h := BucketProgram.Controller.Resources.native_rows_le q.scopeRows (ambient q) q.forward
  rw [PackingIncidenceInput.Stats.native_incidence_count] at h
  exact h

 theorem input_ambient (q : Query) (k : ℕ) : (q.input k).ambient=ambient q := rfl
 theorem input_width (q : Query) (k : ℕ) : (q.input k).width=k := rfl
 theorem input_clauses (q : Query) (k : ℕ) (hv : q.Valid) :
    (q.input k).clauses=q.clauses.length := hv.2.2.2.2.2.1

 theorem small_inputs (k n qi ql : ℕ) (q : Query) (B : ℕ)
    (hv : q.Valid) (hn : ambient q=n) (hn16 : 16 ≤ n) (hk : k ≤ n)
    (hscan : ScanBounds q k ql) (hcl : q.clauses.length ≤ n*B) (hB : B ≤ L n^qi)
    (hLn : L n^qi ≤ n)
    (hLm : L (q.input k).freeCount^ql ≤ (q.input k).freeCount)
    (hsz : Nat.size q.clauses.length ≤ n) : SmallInputs q k n := by
  have hf : (q.input k).freeCount ≤ n := by simpa only [hn] using hscan.residual.1
  have ho : (q.input k).occurrence ≤ n := (hscan.occurrence.trans hLm).trans hf
  have ha : (q.input k).arity ≤ n := (hscan.arity.trans hLm).trans hf
  have hc : (q.input k).clauses ≤ n^2 := by
    rw [input_clauses q k hv]
    exact hcl.trans (by simpa only [pow_two] using Nat.mul_le_mul_left n (hB.trans hLn))
  have hfac : (q.input k).factors ≤ n^2 := by
    have hh := hscan.factors
    rw [hn] at hh
    unfold HashSelect.loopCap at hh
    nlinarith
  have hmass : (q.input k).incidences ≤ n^2 :=
    (input_mass_le q k).trans (by simpa only [pow_two] using Nat.mul_le_mul hf ho)
  refine ⟨hf,hc,ho,ha,hfac,hmass,hk,?_⟩
  have hn2 : n ≤ n^2 := by nlinarith
  have hm : LeafParametersProgram.magnitude (q.input k) ≤ 8*n^2+16 := by
    unfold LeafParametersProgram.magnitude
    rw [input_ambient,input_width,hn]
    omega
  exact hm.trans (by nlinarith [sq_nonneg (n*n)])

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryParameterBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform input-polynomial numeric caps for every actually produced query.
These bounds quantify over every physical padding, while physical word-length
bounds are supplied separately by the concrete producers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources
  SqrtLog.LeafQueryFrontend SqrtLog.LeafScopeResourceBounds in
/-- The same raw structural bounds also supply the small scalar inputs;
all cutoffs are fixed before the query, mark, and candidate history. -/
theorem eventually_small_inputs_of_scope_resources (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      ScanBounds q k (resourceExponent qi + 1) ∧ SmallInputs q k n := by
  let ql := resourceExponent qi + 1
  filter_upwards [eventually_scan_bounds_of_scope_resources k qi,
    CostAssembly.eventually_sparse_parameter_bounds qi,
    eventually_L_power_le_n qi (by norm_num : (0 : ℝ) < 1),
    eventually_uniform_half (eventually_L_power_le_n ql (by norm_num : (0 : ℝ) < 1)),
    Filter.eventually_ge_atTop (max 16 k)] with n hscan hpar hLn hLm hn q B hv hqn hm hmb hB hlen hmass har
  have hs := hscan q B hv hqn hm hmb hB hlen hmass har
  have hhalf : n ≤ 2 * (q.input k).freeCount := by simpa only [hqn] using hs.residual.2
  have hlm : L (q.input k).freeCount ^ ql ≤ (q.input k).freeCount := by
    exact_mod_cast (by simpa using hLm (q.input k).freeCount hhalf :
      (L (q.input k).freeCount : ℝ) ^ ql ≤ (q.input k).freeCount)
  have hln : L n ^ qi ≤ n := by exact_mod_cast (by simpa using hLn : (L n : ℝ) ^ qi ≤ n)
  exact ⟨hs, small_inputs k n qi ql q B hv hqn (by omega) (by omega) hs hmb hB hln hlm
    (hpar q.clauses.length B hmb hB).1⟩

open SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources in
/-- The actual reciprocal sparsification choice satisfies the existing query
scalar estimates above one fixed cutoff. The three literal raw-scope bounds cover every attained history and trial;
no old selector provenance is required. -/
theorem chosen_query_scalars_cutoff_of_scope_resources_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      20 ≤ n ∧ 2 ≤ sparsifySchedule n ∧
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : LeafQueryFrontend.Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n := by
  have hq : LeafScopeResourceBounds.resourceExponent (2 * (k - 1) + 1) + 1 =
      4 * k + 3 := by unfold LeafScopeResourceBounds.resourceExponent; omega
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp
    ((((eventually_small_inputs_of_scope_resources k (2 * (k - 1) + 1)).and
      (chosen_sparseBound_eventually_le_log2_power k)).and
      (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 2))).and
      (Filter.eventually_ge_atTop 20))
  refine ⟨cutoff, ?_⟩
  intro n hn
  obtain ⟨⟨⟨hsmall, hBbound⟩, hs⟩, hlarge⟩ := hcutoff n hn
  refine ⟨hlarge, hs, ?_⟩
  intro B q hvalid hambient hnonempty hclauses hlen hmass harity
  simpa only [hq] using hsmall q B hvalid hambient hnonempty hclauses hBbound hlen hmass harity


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources_oai

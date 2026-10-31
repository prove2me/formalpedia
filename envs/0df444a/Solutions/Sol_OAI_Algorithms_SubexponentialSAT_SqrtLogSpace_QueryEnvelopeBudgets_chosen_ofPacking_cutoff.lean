-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:44:15.530108+00:00
-- url     : https://prove2.me/submissions/4b16960e-0ddf-4949-b047-e8c3175d2fcc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_nativeEnvelope_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets_eventually_ofPacking_bounds_of_scan
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_chosen_query_scalars_cutoff_of_scope_resources

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

/-- One width-dependent cutoff closes every sharp field and its fixed-power
bound for every literal history, losing trial, optional mark, and complete
alphabet. Physical padding and measured execution costs are separate. -/
theorem chosen_ofPacking_cutoff_oai (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B +
            SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4*k+3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2*(k-1)+1) e hg a tail
          Bounds (2*(k-1)+1) (4*k+3) (9*e+8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ)^power * (2 : ℝ)^((1 + (power : ℝ) * exponentConstant k (4*k+3)) *
              Statement.runtimeScale n) := by
  obtain ⟨N, hN⟩ := chosen_query_scalars_cutoff_of_scope_resources k hk
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (((eventually_ofPacking_bounds_of_scan k (2*(k-1)+1) (4*k+3) C d e).and
      (eventually_nativeEnvelope_bound k (2*(k-1)+1) (4*k+3) (9*e+8) power ordinaryPower)).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨max N M, ?_⟩
  intro n hn B q hv hqn hm hc hlen hmass har
  obtain ⟨hs, hsmall⟩ := (hN n (by omega)).2.2 q hv hqn hm hc hlen hmass har
  obtain ⟨⟨hrecord, hbound⟩, hB⟩ := hM n (by omega)
  refine ⟨hs, hsmall, ?_⟩
  intro hg a tail haN haC
  have hb : B ≤ L n ^ (2*(k-1)+1) := by simpa only [B, L] using hB
  have hp := hrecord q B hqn hs hc hb hg a tail haN haC
  exact ⟨hp, hbound _ hp⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff_oai

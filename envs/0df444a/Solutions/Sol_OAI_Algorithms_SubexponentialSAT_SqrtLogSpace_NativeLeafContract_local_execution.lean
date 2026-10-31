-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:37:11.460361+00:00
-- url     : https://prove2.me/submissions/fde8982b-93c6-44dc-99f3-4d892a01a2b0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_hashCalls_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_accepted
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_marked
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_chosen_loaded_local_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_local_from_runs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_prepared_loaded
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_staged_rounds_time_hashCalls
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_common_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafRun_ready_rounds

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

private theorem workPort_ne (i : Fin 891) (j : Fin 896) (hj : 320 ≤ j.val ∧ j.val ≤ 324) :
    workPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

@[simp] theorem workspace_recordState (a : Data) (v pr f : Bool) (src payload : List Bool) :
    workspace (RecordPrograms.state recordPorts a v pr f src payload) = workspace a := by
  funext i
  have hs := workPort_ne i 320 (by decide)
  have hp := workPort_ne i 321 (by decide)
  simp [workspace, RecordPrograms.state, recordPorts, hs, hp]

variable {X Row : Type*} [Fintype X] {m : ℕ}



/-- Equality of the retained workspace frames every port outside the five
physical collector words, including all high query and selector ports. -/
theorem workspace_frame (a b : Data) (h : workspace b = workspace a)
    (i : Fin 896) (h320 : i ≠ 320) (h321 : i ≠ 321) (h322 : i ≠ 322)
    (h323 : i ≠ 323) (h324 : i ≠ 324) : b.stacks i = a.stacks i := by
  have h320' : i.val ≠ 320 := by intro hh; exact h320 (Fin.ext hh)
  have h321' : i.val ≠ 321 := by intro hh; exact h321 (Fin.ext hh)
  have h322' : i.val ≠ 322 := by intro hh; exact h322 (Fin.ext hh)
  have h323' : i.val ≠ 323 := by intro hh; exact h323 (Fin.ext hh)
  have h324' : i.val ≠ 324 := by intro hh; exact h324 (Fin.ext hh)
  by_cases hlow : i.val < 320
  · let j : Fin 891 := ⟨i.val, by omega⟩
    have hj : workPort j = i := by simp [workPort, j, hlow]
    simpa only [workspace, hj] using congrFun h j
  · let j : Fin 891 := ⟨i.val - 5, by omega⟩
    have hj : workPort j = i := by
      apply Fin.ext
      simp [workPort, j, show ¬i.val - 5 < 320 by omega]
      omega
    simpa only [workspace, hj] using congrFun h j


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

theorem finalStaged_sources (a : Data) :
    (finalStaged a).stacks 700=a.stacks 784 ∧
    (finalStaged a).stacks 701=a.stacks 777 ∧
    (finalStaged a).stacks 707=a.stacks 782 ∧
    (finalStaged a).stacks 708=a.stacks 783 ∧
    (finalStaged a).stacks 709=a.stacks 785 := by
  simp [finalStaged,masterRoutes,routesState,routed]

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

theorem trialStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h2 : i≠702) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (trialStaged a).stacks i=a.stacks i :=
  (prefixed_frame _ i h1 h2).trans (finalStaged_frame a i h0 h1 h7 h8 h9)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

theorem staged_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ stagedPorts) :
    (LeafOuterNative.trialStaged a).stacks i = a.stacks i := by
  have hne : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [stagedPorts] using hi
  exact LeafOuterNative.trialStaged_frame a i hne.1 hne.2.1 hne.2.2.1
    hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

theorem temporary_frame (a : State 40 896) (i : Fin 896) (hi : i ≠ 767) :
    (temporaryCleared a).stacks i = a.stacks i := clearStacks_frame _ _ _ hi

theorem temporary_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((temporaryCleared a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = 767
  · subst i; simp [temporaryCleared]
  · simpa only [temporary_frame a i hi] using ha i

theorem staged_sources (a : State 40 896) :
    (staged a).stacks 700 = a.stacks 784 ∧
    (staged a).stacks 701 = a.stacks 777 ∧
    (staged a).stacks 707 = a.stacks 782 ∧
    (staged a).stacks 708 = a.stacks 783 ∧
    (staged a).stacks 709 = a.stacks 785 := by
  simpa only [staged, temporary_frame _ 784 (by decide), temporary_frame _ 777 (by decide),
    temporary_frame _ 782 (by decide), temporary_frame _ 783 (by decide),
    temporary_frame _ 785 (by decide)] using LeafOuterNative.finalStaged_sources (temporaryCleared a)

theorem staged_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((staged a).stacks i).length ≤ B := by
  intro i
  have h := staged_sources a
  by_cases h0 : i = 700
  · subst i; rw [h.1]; exact ha 784
  by_cases h1 : i = 701
  · subst i; rw [h.2.1]; exact ha 777
  by_cases h7 : i = 707
  · subst i; rw [h.2.2.1]; exact ha 782
  by_cases h8 : i = 708
  · subst i; rw [h.2.2.2.1]; exact ha 783
  by_cases h9 : i = 709
  · subst i; rw [h.2.2.2.2]; exact ha 785
  change ((LeafOuterNative.finalStaged (temporaryCleared a)).stacks i).length ≤ B
  rw [LeafOuterNative.finalStaged_frame _ i h0 h1 h7 h8 h9]
  exact temporary_bound a B ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
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

theorem runtimeBound_mono_exponent {constant a b : ℝ} (hc : 0 ≤ constant)
    (hab : a ≤ b) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant b degree inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hab (runtimeScale_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPrimeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

private theorem terminal_trace_steps_unique {α : Type*} {step : α → Option α}
    {n m : ℕ} {a b c : α} (h₁ : Computation.Trace step n a b)
    (h₂ : Computation.Trace step m a c) (hb : step b = none) (hc : step c = none) :
    n = m := by
  induction h₁ generalizing m c with
  | refl a =>
      cases h₂ with
      | refl => rfl
      | cons hs ht => simp [hb] at hs
  | @cons n a a' b hs ht ih =>
      cases h₂ with
      | refl => simp [hc] at hs
      | @cons m _ a'' c hs' ht' =>
          have haa : a' = a'' := Option.some.inj (hs.symm.trans hs')
          subst a''
          exact congrArg Nat.succ (ih ht' hb hc)

/-- The exact instruction count of a terminating structured execution is
unique as well as its result. This allows proved execution bounds to be used
for every actual occurrence of a subroutine in a larger trace. -/
theorem eval_steps_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : n = m := by
  have h := terminal_trace_steps_unique
    (StructuredCalls.compiled_halt_trace h₁ input output)
    (StructuredCalls.compiled_halt_trace h₂ input output) rfl rfl
  omega

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

/-- The actual marked-record entry bounds its five retained words from the
real caller and collector fields. No candidate/history bound is needed here:
trial normalization changes768 and source staging changes only its six ports. -/
theorem record_hidden_bound (d a : Data) (m depth L : ℕ)
    (word tail bits : List Bool)
    (hd : ∀ i, (d.stacks i).length ≤ L)
    (hready : HashMassAdapter.Ready
      (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d m depth word))) a)
    (hread : (HashMassAdapter.read a).length ≤ 3 * L + 2)
    (htail : tail.length ≤ 3 * L + 2) :
    ∀ i, i ∈ HighQueryProgram.Carried.words →
      ((RecordPrograms.state HashMassAdapter.recordPorts a false true false
        tail bits.reverse).stacks i).length ≤ 3 * L + 2 := by
  have frame (i : Fin 896) (hi : i = 770 ∨ i = 771 ∨ i = 781) :
      a.stacks i = d.stacks i := by
    have hn (j : Fin 896) (hj : j.val < 770) : i ≠ j := by
      intro he
      rcases hi with rfl | rfl | rfl <;> subst j <;> norm_num [Fin.coe_ofNat_eq_mod] at hj
    rw [HashMassAdapter.workspace_frame _ a hready.workspace_ready i
      (hn 320 (by decide)) (hn 321 (by decide)) (hn 322 (by decide))
      (hn 323 (by decide)) (hn 324 (by decide))]
    rw [HashMassStaged.staged_frame _ i (by rcases hi with rfl | rfl | rfl <;> decide)]
    exact Function.update_of_ne (hn 768 (by decide)) _ _
  intro i hi
  simp only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using htail
  · simpa [RecordPrograms.state, HashMassAdapter.recordPorts, HashMassAdapter.read] using hread
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (770 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (770 : Fin 896) ≠ 320),
      frame 770 (Or.inl rfl)] using (hd 770).trans (by omega : L ≤ 3 * L + 2)
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (771 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (771 : Fin 896) ≠ 320),
      frame 771 (Or.inr (Or.inl rfl))] using (hd 771).trans (by omega : L ≤ 3 * L + 2)
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (781 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (781 : Fin 896) ≠ 320),
      frame 781 (Or.inr (Or.inr rfl))] using (hd 781).trans (by omega : L ≤ 3 * L + 2)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual prepared selector boundary supplies the literal marked and
history-only frontend, packing, arithmetic and high-counter initialization.
The common bound is unchanged. Suspended caller words have a separate bound
which never occurs in the measured setup time. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem hiddenCap_bound (a : Data) : ∀ i, H i → (a.stacks i).length ≤ hiddenCap a :=
  fun _ hi => Finset.le_sup (f := fun i => (a.stacks i).length) hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
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

theorem input_le_runtimeBound {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    {d : ℕ} (hd : 0 < d) (L n : ℕ) :
    (L : ℝ)+1 ≤ runtimeBound C A d L n := by
  have hCn : 0 ≤ C := by linarith
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hp := le_self_pow₀ hbase (Nat.ne_of_gt hd)
  have he : (1 : ℝ) ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hA (runtimeScale_nonneg n))
  calc
    (L : ℝ)+1 ≤ ((L : ℝ)+1)^d := hp
    _ ≤ C*((L : ℝ)+1)^d := le_mul_of_one_le_left (by positivity) hC
    _ ≤ runtimeBound C A d L n := le_mul_of_one_le_right (by positivity) he

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

/-- Rounding is used only for a proof-side time bound, never to supply code. -/
theorem ceil_runtimeBound_le {C A : ℝ} (hC : 1 ≤ C) (hA : 0 ≤ A)
    (d L n : ℕ) :
    (Nat.ceil (runtimeBound C A d L n) : ℝ) ≤ 2*runtimeBound C A d L n := by
  have h := one_le_runtimeBound hC hA d L n
  have hc := Nat.ceil_lt_add_one (show 0 ≤ runtimeBound C A d L n by linarith)
  linarith

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



open Filter SqrtLog SqrtLog.Statement
/-- A rounded uniform query envelope and the actual chosen hash family stay
within one fixed power of the unchanged runtime scale. -/
theorem chosen_hash_query_polynomial_runtime (k coefficient power : ℕ)
    (C A : ℝ) (d : ℕ) (hC : 1 ≤ C) (hA : 1 ≤ A) (hd : 1 ≤ d) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff, ∀ m inputLength oldQuery measuredTime : ℕ,
      let B := 4*DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n)
        (by omega)^(k-1)
      m ≤ n*B → oldQuery ≤ Nat.ceil (runtimeBound C A d inputLength n) →
      measuredTime ≤ coefficient*(CostAssembly.hashCalls n m
        (SparseCode.distanceDenom m B)+oldQuery+inputLength+1)^power →
      (measuredTime : ℝ) ≤ runtimeBound ((coefficient : ℝ)*(4*C)^power)
        ((power : ℝ)*A) (d*power) inputLength n := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    ((CostAssembly.eventually_hashCalls_bound (2*(k-1)+1)).and
      (chosen_sparseBound_eventually_le_log2_power k))
  refine ⟨N,?_⟩
  intro n hn m inputLength oldQuery measuredTime B hm hquery htime
  obtain ⟨hcalls,hB⟩ := hN n hn
  have hB' : B ≤ Asymptotic.L n^(2*(k-1)+1) := by
    simpa only [B,Asymptotic.L] using hB
  have hh := hcalls m B hm hB'
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 ≤ A := by linarith
  have he : (2 : ℝ)^runtimeScale n ≤ (2 : ℝ)^(A*runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [runtimeScale_nonneg n])
  have hpoly : 1 ≤ C*((inputLength : ℝ)+1)^d :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) inputLength; linarith))
  have hh' : (CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) : ℝ) ≤
      runtimeBound C A d inputLength n := hh.trans
    (he.trans (le_mul_of_one_le_left (by positivity) hpoly))
  have hquery' : (oldQuery : ℝ) ≤ 2*runtimeBound C A d inputLength n :=
    (Nat.cast_le.mpr hquery).trans (Execution.ceil_runtimeBound_le hC hA0 d inputLength n)
  have hinput := Execution.input_le_runtimeBound hC hA0 (show 0<d by omega) inputLength n
  have hsum : ((CostAssembly.hashCalls n m (SparseCode.distanceDenom m B)+
      oldQuery+inputLength+1 : ℕ) : ℝ) ≤ 4*runtimeBound C A d inputLength n := by
    push_cast
    linarith
  have hcast : (measuredTime : ℝ) ≤ (coefficient : ℝ)*
      (((CostAssembly.hashCalls n m (SparseCode.distanceDenom m B)+oldQuery+inputLength+1 : ℕ) : ℝ))^power := by
    exact_mod_cast htime
  calc
    _ ≤ (coefficient : ℝ)*(4*runtimeBound C A d inputLength n)^power :=
      hcast.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsum power) (by positivity))
    _ = _ := by
      rw [← runtimeBound_mul_constant, runtimeBound_pow, runtimeBound_mul_constant]


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

open SqrtLog HashGreedyProgram.NativeRound in
/-- A uniform bound on each actual marked query pays every staged greedy
round at the chosen occurrence threshold. The common physical cap and the
query envelope are fixed before the input and all reached caller states. -/
theorem chosen_rounds_runtimeBound (k commonCoefficient commonDegree : ℕ)
    (queryCoefficient queryExponent : ℝ) (queryDegree : ℕ)
    (hC : 1 ≤ queryCoefficient) (hA : 1 ≤ queryExponent) (hd : 1 ≤ queryDegree) :
    ∃ C A : ℝ, ∃ degree cutoff : ℕ, 1 ≤ C ∧ 1 ≤ A ∧ 1 ≤ degree ∧
      ∀ n inputLength m R : ℕ, cutoff ≤ n →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      m ≤ n * B →
      ∀ (initial : List (List Bool)) (base : State 40 896),
      NativeLeafPreparation.Ready n m B initial base → 0 < m →
      ∀ (queryCost : List Bool → ℕ) (queryTime : ℕ),
      (∀ i, (base.stacks i).length ≤ NativeLeafRun.commonBound n m B R) →
      NativeLeafRun.commonBound n m B R ≤ commonCoefficient * (inputLength + 1) ^ commonDegree →
      (∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ queryTime) →
      queryTime ≤ Nat.ceil (Statement.runtimeBound queryCoefficient queryExponent queryDegree inputLength n) →
      (NativeLeafRun.roundsTime base n m (SparseCode.distanceDenom m B) queryCost
        (NativeLeafRun.commonBound n m B R) : ℝ) ≤
        Statement.runtimeBound C A degree inputLength n := by
  obtain ⟨coefficient, power, hpoly⟩ :=
    staged_rounds_time_hashCalls 1 1 commonCoefficient commonDegree
  obtain ⟨cutoff, htime⟩ := QueryStreamBudgets.chosen_hash_query_polynomial_runtime
    k (coefficient + 1) (power + 1) queryCoefficient queryExponent queryDegree hC hA hd
  refine ⟨((coefficient + 1 : ℕ) : ℝ) * (4 * queryCoefficient) ^ (power + 1),
    ((power + 1 : ℕ) : ℝ) * queryExponent, queryDegree * (power + 1), cutoff, ?_, ?_, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 coefficient)
      (one_le_pow₀ (by linarith))
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 power) hA
  · exact Nat.mul_pos (by omega) (by omega)
  · intro n inputLength m R hn B hmB initial base hr hm queryCost queryTime hb hL hq ht
    apply htime n hn m inputLength queryTime _ hmB ht
    have hp := hpoly base hr hm queryCost inputLength queryTime queryTime hb hL hq (by
      simp only [pow_one, one_mul]
      omega)
    let X := CostAssembly.hashCalls n m (SparseCode.distanceDenom m B) + queryTime + inputLength + 1
    have hX : 1 ≤ X := by dsimp only [X]; omega
    exact hp.trans (Nat.mul_le_mul (Nat.le_succ coefficient)
      (Nat.pow_le_pow_right hX (Nat.le_succ power)))

open SqrtLog SqrtLog.Statement in
/-- The exact four phase costs used by local_from_runs share one runtime
scale, including the separate accepted query and paid final source staging. -/
theorem local_time_runtimeBound
    {Cp Cr Cq Ap Ar Aq : ℝ} (dp dr dq W dw inputLength n : ℕ)
    (prepareSteps roundSteps querySteps whole L : ℕ)
    (hCp : 0 ≤ Cp) (hCr : 0 ≤ Cr) (hCq : 1 ≤ Cq)
    (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar) (hAq : 0 ≤ Aq)
    (hp : (prepareSteps : ℝ) ≤ runtimeBound Cp Ap dp inputLength n)
    (hr : (roundSteps : ℝ) ≤ runtimeBound Cr Ar dr inputLength n)
    (hq : querySteps ≤ Nat.ceil (runtimeBound Cq Aq dq inputLength n))
    (hL : L ≤ W * (inputLength + 1) ^ dw)
    (hwhole : whole ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71) :
    (whole : ℝ) ≤ runtimeBound (Cp + Cr + 2 * Cq + (61 * W + 71 : ℕ))
      (Ap + Ar + Aq) (dp + dr + dq + dw) inputLength n := by
  have hq' : (querySteps : ℝ) ≤ runtimeBound (2 * Cq) Aq dq inputLength n := by
    rw [runtimeBound_mul_constant]
    exact (Nat.cast_le.mpr hq).trans (Execution.ceil_runtimeBound_le hCq hAq dq inputLength n)
  have hpr := (add_le_add hp hr).trans
    (QueryStreamBudgets.runtimeBound_add_bound Cp Cr Ap Ar dp dr inputLength n hCp hCr hAp hAr)
  have hcore : ((prepareSteps + roundSteps + querySteps : ℕ) : ℝ) ≤
      runtimeBound (Cp + Cr + 2 * Cq) (Ap + Ar + Aq) (dp + dr + dq) inputLength n := by
    simpa only [Nat.cast_add] using (add_le_add hpr hq').trans
      (QueryStreamBudgets.runtimeBound_add_bound (Cp + Cr) (2 * Cq) (Ap + Ar) Aq
        (dp + dr) dq inputLength n (by positivity) (by linarith) (by positivity) hAq)
  have hextra : 61 * L + 71 ≤ (61 * W + 71) * (inputLength + 1) ^ dw := by
    have hpower : 1 ≤ (inputLength + 1) ^ dw := Nat.one_le_pow' _ _
    nlinarith only [hL, hpower]
  have htime := QueryStreamBudgets.polynomial_overhead_runtime
    (Cp + Cr + 2 * Cq) (Ap + Ar + Aq) (dp + dr + dq) (61 * W + 71) dw
    inputLength n (prepareSteps + roundSteps + querySteps) (61 * L + 71)
    (by linarith) (by positivity) hcore hextra
  exact (Nat.cast_le.mpr (show whole ≤ (prepareSteps + roundSteps + querySteps) +
    (61 * L + 71) by omega)).trans htime

open SqrtLog Filter
open scoped Topology


open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- Every staged greedy round now invokes the genuine fixed marked query.
Time uses an arbitrary finite opaque-word frame; the independent space proof
uses the actual caller/collector cap and the same measured execution. -/
theorem marked_rounds (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
      ∀ n inputLength R : ℕ, cutoff ≤ n → n ≤ inputLength →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n), Valid k F → 0 < F.length → F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (base : State 40 896),
      NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      let L := NativeLeafRun.commonBound n F.length B R
      L ≤ C0 * (inputLength + 1) ^ d0 →
      let queryTime := Nat.ceil (Statement.runtimeBound C E degree inputLength n)
      let K := max (Cs * (inputLength + 1) ^ es) (3 * L + 2)
      ∃ steps selected,
        steps ≤ NativeLeafRun.roundsTime base n F.length (SparseCode.distanceDenom F.length B)
          (fun _ => queryTime) L ∧
        Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) steps base selected ∧
        RowBoundary base (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (HashGreedyCode.initial shifts Q)
          (HashSelect.loopCap n F.length)) selected ∧
        (∀ i, (selected.stacks i).length ≤ L) ∧
        StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) (steps + 1) base
          (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) := by
  obtain ⟨C, E, degree, Cs, es, cutoff, hC, hE, hdegree, hquery⟩ :=
    NativeHashQueries.marked k C0 d0 hk
  refine ⟨C, E, degree, Cs, es, cutoff, hC, hE, hdegree, ?_⟩
  intro n inputLength R hn hnI B F hv hm hmB shifts Q base hr hb hformula hamb hupper L hL
    queryTime K
  obtain ⟨hR, hrounds, hCwidth, hcounter, hbytes, href, hgrowth, _hnL⟩ :=
    NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
  obtain ⟨steps, selected, ht, he, hselected, _h781, _h9, hbound, hs⟩ :=
    NativeLeafRun.ready_rounds (NativeLeafSemantics.indexed F) hm
      (HashGreedyCode.initial shifts Q) (SparseCode.distanceDenom F.length B) rfl
      (HighQueryProgram.marked k) (fun _ => queryTime) base hr L K
      (fun i => (hb i).trans hR) hrounds hcounter href hgrowth hCwidth hbytes (by
        intro rows word d _hrows hattained _hbytes hword hframe hhistory hcounter hscratch
          e tail a hready
        obtain ⟨rounds, hrounds, rfl⟩ := hattained
        let input := HashQueryEntry.recordState a tail (Encoding.encodeNat e.val)
        obtain ⟨t, out, he, ht, hcount, hws, hread, hreset, h324, hlen, _hp⟩ :=
          hquery n inputLength R hn hnI F hv hm hmB shifts Q rounds hrounds
            word base d a e tail (NativeHashQuerySetup.hiddenCap input)
            hr hb hformula hamb hL hupper hword hframe hhistory hcounter hscratch hready
            (NativeHashQuerySetup.hiddenCap_bound input)
        have hsrc : input.stacks 320 = tail := by
          simp [input, HashQueryEntry.recordState, RecordPrograms.state, HashMassAdapter.recordPorts]
        have hreset' : RecordPrograms.state HashMassAdapter.recordPorts out
            false true false tail [] = out :=
          (congrArg (fun word => RecordPrograms.state HashMassAdapter.recordPorts out
            false true false word []) hsrc.symm).trans hreset
        refine ⟨t, out, ?_, ?_, ?_, ?_, hlen, h324, ?_⟩
        · change t ≤ Nat.ceil (Statement.runtimeBound C E degree inputLength n)
          omega
        · exact hws.trans ((HashMassAdapter.workspace_recordState a false true false tail
            (Encoding.encodeNat e.val).reverse).trans hready.workspace_ready)
        · simpa [input, HashQueryEntry.recordState, RecordPrograms.state,
            HashMassAdapter.recordPorts, HashMassAdapter.read] using hread
        · rw [hcount, countWord_toNat]
        · rw [hreset']
          exact he) (by
        intro rows word d _hrows hattained _hbytes hword hframe hhistory hcounter hscratch hd
          e tail a t middle hready hread htail _hindex _hn hactual
        obtain ⟨rounds, hrounds, rfl⟩ := hattained
        obtain ⟨steps, out, he, _ht, _hcount, _hws, _hread, _hreset, _h324, _hlen, hp⟩ :=
          hquery n inputLength R hn hnI F hv hm hmB shifts Q rounds hrounds
            word base d a e tail (3 * L + 2)
            hr hb hformula hamb hL hupper hword hframe hhistory hcounter hscratch hready
            (HighQueryEntryShadow.record_hidden_bound d a F.length
              (SparseCode.distanceDenom F.length B) L word tail (Encoding.encodeNat e.val)
              hd hready hread htail)
        have ht := SubexpPrimeProgram.eval_steps_unique hactual he 778 777
        exact ⟨fun j z hj hz i => hp.bound j z (by omega) hz i⟩)
  exact ⟨steps, selected, ht, he, hselected, hbound, hs⟩


open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- The fixed local program executes preparation, every staged greedy round
and the separate accepted-history query. All constants precede the original
input; storage is polynomial and the full canonical count retains ambient n. -/
theorem local_execution_oai (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      let W := SparseCountProgram.formulaBound n k + (n + 1) + parameterBound
      ∀ (F : RawCNF n) (a : State 40 896), Valid k F → F ≠ [] → F.length ≤ n * B →
      (∀ i, (a.stacks i).length ≤ W) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = []) →
      a.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (a.stacks 785) = n →
      BinaryArithmetic.toNat (a.stacks 786) = B →
      ∃ steps ≤ Nat.ceil (Statement.runtimeBound Ct At timeDegree inputLength n), ∃ out,
        Eval (NativeLeafProgram.localCommand k) steps a out ∧
        out.stacks 788 = countWord (rawCount F) ∧
        ∀ t z, t ≤ steps → Trace (NativeLeafProgram.localProgram k) t
          (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ Cs * (inputLength + 1) ^ spaceDegree := by
  obtain ⟨C0, d0, Cp, Ap, dp, Np, hCp, hprepare⟩ :=
    prepared_loaded k parameterCoefficient parameterDegree
  obtain ⟨Cm, Em, dm, Csm, esm, Nm, hCm, hEm, hdm, hmarked⟩ := marked_rounds k C0 d0 hk
  obtain ⟨Ca, Ea, da, Csa, esa, Na, hCa, hEa, hda, haccepted⟩ :=
    NativeHashQueries.accepted k C0 d0 hk
  obtain ⟨Cr, Er, dr, Nr, hCr, hEr, hdr, hroundTime⟩ :=
    chosen_rounds_runtimeBound k C0 d0 Cm Em dm hCm hEm hdm
  obtain ⟨Cl, dl, hspace⟩ := chosen_loaded_local_space k parameterCoefficient parameterDegree
  obtain ⟨Ns, hschedule⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 1))
  let Ck := Csm + Csa + 3 * C0 + 2
  let dk := esm + esa + d0
  refine ⟨Ck + Cl, dk + dl, Cp + Cr + 2 * Ca + (61 * C0 + 71 : ℕ),
    (Ap : ℝ) + Er + Ea, dp + dr + da + d0,
    max (max (max Np Nm) (max Na Nr)) (max Ns 1), ?_, ?_, by omega, ?_⟩
  · have := Nat.cast_nonneg (α := ℝ) (61 * C0 + 71)
    linarith
  · have := Nat.cast_nonneg (α := ℝ) Ap
    linarith
  · intro n inputLength parameterBound hncut hnI hp B W F a hv hne hmB ha hempty hformula hn hBword
    have hnpos : 0 < n := by omega
    have hm : 0 < F.length := List.length_pos_iff.mpr hne
    have hB : 0 < B := by
      dsimp only [B]
      have hM := (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1
      positivity
    obtain ⟨prepareSteps, started, prepared, base, shifts, Q, ep, tp, hstarted, hmetadata,
      hprepared, hr, hgood, hdistance, hbody, hamb, hbase, hupper, hL, sp⟩ :=
      hprepare n inputLength parameterBound (by omega) hnI hp F a hne hmB ha hempty hformula hn hBword
    let startup := W + NativeLeafSetup.canonicalStartTime n F.length W
    let R := NativeLeafPreparation.retainedBound F.length B startup started prepared
    let L := NativeLeafRun.commonBound n F.length B R
    let queryTime := Nat.ceil (Statement.runtimeBound Cm Em dm inputLength n)
    let K := Ck * (inputLength + 1) ^ dk
    have component (C d : ℕ) (hc : C ≤ Ck) (hd : d ≤ dk) :
        C * (inputLength + 1) ^ d ≤ K :=
      Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)
    have hLpower : L ≤ C0 * (inputLength + 1) ^ dk :=
      hL.trans (Nat.mul_le_mul_left C0 (Nat.pow_le_pow_right (by omega) (by dsimp [dk]; omega)))
    have hframeK : 3 * L + 2 ≤ K := by
      have hone : 1 ≤ (inputLength + 1) ^ dk := Nat.one_le_pow' _ _
      change 3 * L + 2 ≤ Ck * (inputLength + 1) ^ dk
      dsimp only [Ck]
      nlinarith only [hLpower, hone,
        Nat.zero_le ((Csm + Csa) * (inputLength + 1) ^ dk)]
    have hmarkedK : max (Csm * (inputLength + 1) ^ esm) (3 * L + 2) ≤ K :=
      max_le (component Csm esm (by dsimp [Ck]; omega) (by dsimp [dk]; omega)) hframeK
    have hacceptedK : max (Csa * (inputLength + 1) ^ esa) L ≤ K :=
      max_le (component Csa esa (by dsimp [Ck]; omega) (by dsimp [dk]; omega)) (by omega)
    obtain ⟨hR, _hloop, _hC, _hc, _hbytes, _href, _hgrowth, hnL⟩ :=
      NativeLeafRun.common_bounds (NativeLeafSemantics.indexed F) shifts Q R
    have hbaseL : ∀ i, (base.stacks i).length ≤ L := fun i => (hbase i).trans hR
    obtain ⟨roundSteps, selected, tr, er, hselected, hselectedBound, sr⟩ :=
      hmarked n inputLength R (by omega) hnI F hv hm hmB shifts Q base hr hbase hbody hamb hupper hL
    obtain ⟨querySteps, middle, eq, tq, hword, _hwordLength, sq⟩ :=
      haccepted n inputLength R (by omega) hnI F hv hm hmB shifts Q (HashSelect.loopCap n F.length)
        le_rfl base selected L hr hbase hbody hamb hL hupper hselected
        (fun i _ => AcceptedQueryStage.staged_bound selected L hselectedBound i)
    have sr' : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
        (roundSteps + 1) base
        (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) := by
      constructor
      intro t z ht hz i
      apply (sr.bound t z ht hz i).trans
      change max (max _ _) _ ≤ max (max K _) _
      exact max_le_max (max_le_max hmarkedK le_rfl) le_rfl
    have sq' : StageSpace (HighQueryProgram.accepted k) querySteps
        (AcceptedQueryStage.staged selected) K :=
      ⟨fun t z ht hz i => (sq.bound t z (by omega) hz i).trans hacceptedK⟩
    obtain ⟨steps, out, ht, he, _hout, hcount, _hbound, hprefix⟩ :=
      local_from_runs k F hm hB shifts Q hgood hdistance a base selected middle
        prepareSteps roundSteps querySteps L (C0 * (inputLength + 1) ^ d0)
        (NativeLeafRun.roundsSpace base n F.length (SparseCode.distanceDenom F.length B) L K) K
        ep sp hr hselected hselectedBound hnL er sr' eq hword sq'
    have tr' : (roundSteps : ℝ) ≤ Statement.runtimeBound Cr Er dr inputLength n :=
      (Nat.cast_le.mpr tr).trans (hroundTime n inputLength F.length R (by omega) hmB
        (HashGreedyCode.initial shifts Q) base hr hm (fun _ => queryTime) queryTime
        hbaseL hL (fun _ => le_rfl) le_rfl)
    have tt := local_time_runtimeBound (Cp := Cp) (Cr := Cr) (Cq := Ca)
      (Ap := (Ap : ℝ)) (Ar := Er) (Aq := Ea) dp dr da C0 d0 inputLength n
      prepareSteps roundSteps querySteps steps L (by linarith) (by linarith) hCa
      (Nat.cast_nonneg Ap) (by linarith) (by linarith) tp tr' (by omega) hL (by omega)
    have hs := hspace n inputLength F.length parameterBound K hnpos hm hnI
      (hschedule n (by omega)) hp hmB started prepared base hstarted hmetadata hprepared
      (by rw [CounterPrograms.value_eq_toNat]; exact hr.clauses) hbase
    have hfirst : C0 * (inputLength + 1) ^ d0 ≤ K :=
      component C0 d0 (by dsimp [Ck]; omega) (by dsimp [dk]; omega)
    have hfinal : max K (Cl * (inputLength + 1) ^ dl) ≤
        (Ck + Cl) * (inputLength + 1) ^ (dk + dl) := by
      apply max_le
      · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨steps, ?_, out, he, hcount, ?_⟩
    · exact Nat.cast_le.mp (tt.trans (Nat.le_ceil _))
    · intro t z htz hz i
      apply (hprefix t z (by omega) hz i).trans
      apply (max_le (hfirst.trans (Nat.le_max_left _ _))
        ((Nat.le_max_right _ _).trans hs)).trans hfinal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution_oai

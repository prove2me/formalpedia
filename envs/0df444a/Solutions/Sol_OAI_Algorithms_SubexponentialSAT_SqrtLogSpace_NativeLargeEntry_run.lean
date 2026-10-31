-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:36:22.924329+00:00
-- url     : https://prove2.me/submissions/b9dd581d-3c14-466a-b0e9-5d239a472772

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_canonical_normalized_body_length
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_counting_primitive_from_entry
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_entry_large_bounded_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_frontend_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_outer_from_setup
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_setupAfterFrontend_prepared_execution
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_uniform_contract
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets_runtime_of_tree_and_leaf

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

end SubexponentialSAT.Encoding

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem boundedEval_mono {code : Code} {t a b small large}
    (h : BoundedEval code t a b small) (hle : small ≤ large) : BoundedEval code t a b large :=
  ⟨h.eval, fun p c hp hc i => (h.space p c hp hc i).trans hle⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

open StructuredCalls

theorem cutoffScanned_word (a : State 80 1220) (flag : Bool) :
    (cutoffScanned a flag).stacks 270 = [flag] :=
  embedState_stack _ _ _ _ (fun _ _ _ => Subsingleton.elim _ _) 0

theorem cutoffScanned_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hi : i ≠ 270) : (cutoffScanned a flag).stacks i = (cutoffCopied a).stacks i :=
  embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi hj.symm)

@[simp] theorem cutoffResult_flag (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).regs 75 = flag := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word, readRegs]

@[simp] theorem cutoffResult_work (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 270 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word]

@[simp] theorem cutoffResult_scratch (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 271 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    cutoffScanned_frame a flag 271 (by decide), cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState]

theorem cutoffResult_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hw : i ≠ 270) (hs : i ≠ 271) : (cutoffResult a flag).stacks i = a.stacks i := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, hw,
    cutoffScanned_frame a flag i hw, cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState, hs]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem frontendBound_polynomial {n : ℕ} (F : SAT.CNF (Fin n)) :
    frontendBound F ≤ 4000 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  have hn := Encoding.numVariables_le_formulaBitLength F
  have hb : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
    rw [Encoding.formulaBitLength_eq]
    omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hb2 := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  dsimp [frontendBound, FrontendProgram.initializeBound]
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The canonical frontend and actual fixed-cutoff dispatcher share one finite
program. The large command is supplied by the subsequent concrete integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem FrontendReady.cutoff {n : ℕ} {F : SAT.CNF (Fin n)} {binary : List Bool}
    {a : State 80 1220} (ready : FrontendReady F binary a) (flag : Bool) :
    FrontendReady F binary (FiniteFallback.cutoffResult a flag) := by
  constructor
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.input
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.header
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.body
  · exact (FiniteFallback.cutoffResult_frame a flag _ (by decide) (by decide)).trans ready.dimension
  · intro i hc hu hb hn
    by_cases hw : i = 270
    · subst i
      exact FiniteFallback.cutoffResult_work a flag
    by_cases hs : i = 271
    · subst i
      exact FiniteFallback.cutoffResult_scratch a flag
    exact (FiniteFallback.cutoffResult_frame a flag i hw hs).trans (ready.blank i hc hu hb hn)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
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

/-- Polynomial source-stack bounds remain polynomial under the actual guarded
compiler's all-tape, all-prefix visited-cell envelope. -/
theorem compiledSpace_polynomial (tapeCount bound inputBits C d : ℕ)
    (hbound : bound ≤ C * (inputBits + 1) ^ d) :
    tapeCount * (bound + inputBits + 15) ≤
      tapeCount * (C + 16) * (inputBits + 1) ^ (d + 1) := by
  have hbase : 1 ≤ inputBits + 1 := by omega
  have hp : (inputBits + 1) ^ d ≤ (inputBits + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hi : inputBits + 1 ≤ (inputBits + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ d + 1 by omega)
  have hinner : bound + inputBits + 15 ≤ (C + 16) * (inputBits + 1) ^ (d + 1) := by
    nlinarith [Nat.mul_le_mul_left C hp]
  exact (Nat.mul_le_mul_left tapeCount hinner).trans_eq (by ring)

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

private theorem dfs_fields_polynomial (k K e : ℕ) :
    ∃ A D : ℕ, ∀ n m inputBits threshold : ℕ,
      n ≤ inputBits → m ≤ inputBits → threshold ≤ K * (inputBits + 1) ^ e →
      let P := A * (inputBits + 1) ^ D
      DisjointReuse.SparseCountProgram.formulaBound n k ≤ P ∧ m * k ≤ P ∧
        threshold ≤ P ∧ n + 1 ≤ P := by
  let c := 2 + (4 + 8 * k) * (k + 1) * 2 ^ k
  let A := c + k + K + 1
  let D := k + e + 2
  refine ⟨A, D, ?_⟩
  intro n m inputBits threshold hn hm ht
  let P := A * (inputBits + 1) ^ D
  have hbase : 1 ≤ inputBits + 1 := by omega
  have hinput : inputBits + 1 ≤ (inputBits + 1) ^ D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1 ≤ D by dsimp [D]; omega)
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hnP : n + 1 ≤ P := by
    exact (Nat.add_le_add_right hn 1).trans
      (hinput.trans (Nat.le_mul_of_pos_left _ hA))
  have hbody : DisjointReuse.SparseCountProgram.formulaBound n k ≤ P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul (show c ≤ A by dsimp [A]; omega)
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right hbase (show k + 1 ≤ D by dsimp [D]; omega))
  have hdepth : m * k ≤ P := by
    rw [Nat.mul_comm m k]
    exact Nat.mul_le_mul (show k ≤ A by dsimp [A]; omega)
      (hm.trans ((Nat.le_succ inputBits).trans hinput))
  have hthreshold : threshold ≤ P := ht.trans
    (Nat.mul_le_mul (show K ≤ A by dsimp [A]; omega)
      (Nat.pow_le_pow_right hbase (show e ≤ D by dsimp [D]; omega)))
  exact ⟨hbody, hdepth, hthreshold, hnP⟩

/-- The exact four summands of `DFSCountProgram.visitSpace`. The selector
coefficient is fixed by the clause width; no exponential visit count appears. -/
theorem dfsVisitSpace_le_fourth (coefficient n body depth threshold S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (hd : depth ≤ S) (ht : threshold ≤ S) :
    let Q := DisjointReuse.SparseDFSBoundarySpace.frontierBound body depth
    (n + 1 + Q + 11 * body + 13) + (coefficient + 24) * (body + threshold + 1) ^ 4 +
      (Q + (n + 1) + 620001 * (4 * body + 3) ^ 2) + 100 * (n + 1) ≤
        32000000 * (coefficient + 1) * S ^ 4 := by
  have hS : 1 ≤ S := by omega
  have h1 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hQ : DisjointReuse.SparseDFSBoundarySpace.frontierBound body depth ≤ 13 * S ^ 2 := by
    have hprod : (2 * body + 2) * (depth + 2) ≤ 12 * S ^ 2 := by
      calc
        _ ≤ (4 * S) * (3 * S) := Nat.mul_le_mul (by omega) (by omega)
        _ = _ := by ring
    unfold DisjointReuse.SparseDFSBoundarySpace.frontierBound
    nlinarith
  have hselect : (coefficient + 24) * (body + threshold + 1) ^ 4 ≤
      81 * (coefficient + 24) * S ^ 4 := by
    calc
      _ ≤ (coefficient + 24) * (3 * S) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = _ := by ring
  have hsplit : 620001 * (4 * body + 3) ^ 2 ≤ 30380049 * S ^ 2 := by
    calc
      _ ≤ 620001 * (7 * S) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  dsimp only
  nlinarith

theorem dfsVisitSpace_polynomial (k coefficient K e : ℕ) :
    ∃ C d : ℕ, ∀ n m inputBits threshold : ℕ,
      n ≤ inputBits → m ≤ inputBits → threshold ≤ K * (inputBits + 1) ^ e →
      let P := DisjointReuse.SparseCountProgram.formulaBound n k
      let Q := DisjointReuse.SparseDFSBoundarySpace.frontierBound P (m * k)
      (n + 1 + Q + 11 * P + 13) + (coefficient + 24) * (P + threshold + 1) ^ 4 +
        (Q + (n + 1) + 620001 * (4 * P + 3) ^ 2) + 100 * (n + 1) ≤
          C * (inputBits + 1) ^ d := by
  obtain ⟨A, D, h⟩ := dfs_fields_polynomial k K e
  refine ⟨32000000 * (coefficient + 1) * A ^ 4, D * 4, ?_⟩
  intro n m inputBits threshold hn hm ht
  obtain ⟨hb, hd, ht, hn⟩ := h n m inputBits threshold hn hm ht
  calc
    _ ≤ 32000000 * (coefficient + 1) * (A * (inputBits + 1) ^ D) ^ 4 :=
      dfsVisitSpace_le_fourth _ _ _ _ _ _ hn hb hd ht
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The actual DFS visit budget is polynomial in its retained fields times
the leaf budget, including splitter maxima and all cleanup passes. -/
theorem dfsVisitTime_le (coefficient n body threshold leafTime bound S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (ht : threshold ≤ S) (hbound : bound ≤ S) :
    9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1))) ≤
      32000000 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by
  have hS : 1 ≤ S := by omega
  have h1 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have hselect : coefficient * (body + threshold + 1) ^ 4 ≤ 81 * coefficient * S ^ 4 := by
    calc
      _ ≤ coefficient * (3 * S) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = _ := by ring
  have hsplit : 621000 * (4 * body + 3) ^ 2 ≤ 30429000 * S ^ 2 := by
    calc
      _ ≤ 621000 * (7 * S) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  have hmax : max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) ≤
      30429000 * S ^ 2 + leafTime + 100 * S := max_le (by omega) (by omega)
  have hbig : 1 ≤ 32000000 * (coefficient + 1) * S ^ 4 := by
    have hp : 1 ≤ S ^ 4 := one_le_pow₀ hS
    nlinarith
  have hpay : leafTime ≤ 32000000 * (coefficient + 1) * S ^ 4 * leafTime :=
    Nat.le_mul_of_pos_left _ hbig
  calc
    _ ≤ leafTime + (81 * coefficient + 31000000) * S ^ 4 := by nlinarith
    _ ≤ _ := by nlinarith


/-- Startup, all visits and full count-word export fit the product of the
visit count, the leaf budget and one fixed retained-field polynomial. -/
theorem dfsCommandTime_le (coefficient n body threshold leafTime bound visits S : ℕ)
    (hn : n + 1 ≤ S) (hb : body ≤ S) (ht : threshold ≤ S) (hbound : bound ≤ S) :
    let visitTime := 9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1)))
    8 * body + 16 + (visits * (visitTime + 1) + 1) + (2 * bound + 7 * n + 18) ≤
      32000100 * (coefficient + 1) * S ^ 4 * (visits + 1) * (leafTime + 1) := by
  have hS : 1 ≤ S := by omega
  have hp : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have hpow : 1 ≤ S ^ 4 := one_le_pow₀ hS
  have hv := dfsVisitTime_le coefficient n body threshold leafTime bound S hn hb ht hbound
  have hcap : S ≤ (coefficient + 1) * S ^ 4 * (leafTime + 1) :=
    hp.trans ((Nat.le_mul_of_pos_left _ (by omega)).trans
      (Nat.le_mul_of_pos_right _ (by omega)))
  have hcap0 : 1 ≤ (coefficient + 1) * S ^ 4 * (leafTime + 1) := hS.trans hcap
  have hvisit : 9 * body + 11 +
      (coefficient * (body + threshold + 1) ^ 4 + 1 +
        (max (621000 * (4 * body + 3) ^ 2) (leafTime + 100 * (n + 1)) + 1 +
          ((2 * bound + 3) * 257 + 1))) + 1 ≤
      32000001 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by nlinarith
  have hstartup : 8 * body + 16 + 1 + (2 * bound + 7 * n + 18) ≤
      100 * (coefficient + 1) * S ^ 4 * (leafTime + 1) := by
    have hstart : 8 * body + 16 + 1 + (2 * bound + 7 * n + 18) ≤ 100 * S := by omega
    exact hstart.trans ((Nat.mul_le_mul_left 100 hcap).trans_eq (by ring))
  dsimp only
  have hpaid := Nat.mul_le_mul_left visits hvisit
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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

theorem entrySpace_requirements (n L inputBound bound : ℕ) :
    L+4000*(L+1)^2≤entrySpace n L inputBound bound ∧
    1224*(L+1)+10*n+28≤entrySpace n L inputBound bound ∧
    Native.outerSpace inputBound bound n≤entrySpace n L inputBound bound := by
  unfold entrySpace
  exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

private theorem boundary_le (n inputBound bound S : ℕ)
    (hn : n+1≤S) (hi : inputBound≤S) (hb : bound≤S) :
    Native.outerBoundary inputBound bound n≤1250*S := by
  unfold Native.outerBoundary
  exact max_le (by omega) (by omega)

/-- Space is polynomial in the original input word, independently of all
visit and leaf-runtime counts. The canonical entry is included. -/
theorem entrySpace_polynomial (K e : ℕ) :
    ∃ C d : ℕ, ∀ n L inputBound bound : ℕ,
      n≤L → inputBound≤K*(L+1)^e → bound≤K*(L+1)^e →
      entrySpace n L inputBound bound≤C*(L+1)^d := by
  refine ⟨2000000*(K+1),e+2,?_⟩
  intro n L inputBound bound hn hi hb
  let S := (K+1)*(L+1)^(e+2)
  have he : (L+1)^e≤(L+1)^(e+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hx : L+1≤S := (Nat.le_self_pow (by omega) _).trans
    (Nat.le_mul_of_pos_left _ (by omega))
  have hx2 : (L+1)^2≤S :=
    (Nat.pow_le_pow_right (by omega) (show 2≤e+2 by omega)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have hiS : inputBound≤S := hi.trans (Nat.mul_le_mul (Nat.le_succ K) he)
  have hbS : bound≤S := hb.trans (Nat.mul_le_mul (Nat.le_succ K) he)
  have hboundary := boundary_le n inputBound bound S (by omega) hiS hbS
  have houter : Native.outerSpace inputBound bound n≤2000000*S := by
    unfold Native.outerSpace
    omega
  have hresult : entrySpace n L inputBound bound≤2000000*S := by
    unfold entrySpace
    exact max_le (by omega) (max_le (by omega) houter)
  simpa only [S,Nat.mul_assoc] using hresult

/-- The exact compiler envelope counts every primitive tape and every
visited prefix, including blank crossings and its fixed control overhead. -/
theorem primitiveSpace_polynomial (K e : ℕ) :
    ∃ C d : ℕ, ∀ n L inputBound bound : ℕ,
      n≤L → inputBound≤K*(L+1)^e → bound≤K*(L+1)^e →
      1220*(entrySpace n L inputBound bound+L+15)≤C*(L+1)^d := by
  obtain ⟨C,d,h⟩ := entrySpace_polynomial K e
  refine ⟨1220*(C+16),d+1,?_⟩
  intro n L inputBound bound hn hi hb
  exact compiledSpace_polynomial 1220 _ L C d (h n L inputBound bound hn hi hb)

/-- The startup body can be shorter than formulaBound. Every visit still
uses the genuine formulaBound budget, including losing selector scans. -/
theorem entryTime_le (k n L body threshold leafTime inputBound bound visits setupSteps S : ℕ)
    (hL : L+1≤S) (hn : n≤L)
    (hbody : body≤SparseCountProgram.formulaBound n k)
    (hformula : SparseCountProgram.formulaBound n k≤S)
    (ht : threshold≤S) (hi : inputBound≤S) (hb : bound≤S) (hsetup : setupSteps≤S) :
    entryTime k n L body threshold leafTime inputBound bound visits setupSteps≤
      225000000*(SparsePriorityProgram.Selector.selectorCoefficient k+1)*S^4*
        (visits+1)*(leafTime+1) := by
  let coefficient := SparsePriorityProgram.Selector.selectorCoefficient k
  have hS : 1≤S := by omega
  have hpow : S≤S^4 := Nat.le_self_pow (by decide) _
  have h1 : 1≤S^4 := one_le_pow₀ hS
  have hfront : 4000*(L+1)^2≤4000*S^4 := Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left hL 2).trans (Nat.pow_le_pow_right hS (by decide)))
  have hboundary := boundary_le n inputBound bound S (by omega) hi hb
  have hdfs := dfsCommandTime_le coefficient n (SparseCountProgram.formulaBound n k)
    threshold leafTime bound visits S (by omega) hformula ht hb
  dsimp only [coefficient] at hdfs
  have hactual : Native.dfsTime k n body threshold leafTime bound visits≤
      32000100*(coefficient+1)*S^4*(visits+1)*(leafTime+1) := by
    apply le_trans ?_ hdfs
    unfold Native.dfsTime DFSVisit.visitTime
    omega
  have hother : 4000*(L+1)^2+10*n+29+setupSteps+
      12*Native.outerBoundary inputBound bound n+14+1≤20000*S^4 := by omega
  have hR : 1≤(visits+1)*(leafTime+1) := Nat.mul_pos (by omega) (by omega)
  have hpaid : 20000*S^4≤20000*S^4*((visits+1)*(leafTime+1)) :=
    (Nat.mul_one _).symm.le.trans (Nat.mul_le_mul_left _ hR)
  unfold entryTime
  calc
    _ = 7*((4000*(L+1)^2+10*n+29+setupSteps+
      12*Native.outerBoundary inputBound bound n+14+1)+
      Native.dfsTime k n body threshold leafTime bound visits) := by ring
    _ ≤ 7*(20000*S^4*((visits+1)*(leafTime+1))+
      32000100*(coefficient+1)*S^4*(visits+1)*(leafTime+1)) :=
        Nat.mul_le_mul_left 7 (Nat.add_le_add (hother.trans hpaid) hactual)
    _ = (140000+224000700*(coefficient+1))*S^4*(visits+1)*(leafTime+1) := by ring
    _ ≤ _ := by dsimp only [coefficient]; gcongr; omega

/-- Constants and degree depend only on fixed width and the ordinary source
cap, before any formula, visited node, leaf or primitive run is selected. -/
theorem entryTime_polynomial (k K e : ℕ) :
    ∃ C d : ℕ, ∀ n L body threshold leafTime inputBound bound visits setupSteps : ℕ,
      n≤L → body≤SparseCountProgram.formulaBound n k →
      threshold≤K*(L+1)^e → inputBound≤K*(L+1)^e →
      bound≤K*(L+1)^e → setupSteps≤K*(L+1)^e →
      entryTime k n L body threshold leafTime inputBound bound visits setupSteps≤
        C*(L+1)^d*(visits+1)*(leafTime+1) := by
  let c := 2+(4+8*k)*(k+1)*2^k
  let A := c+K+1
  let D := k+e+2
  refine ⟨225000000*(SparsePriorityProgram.Selector.selectorCoefficient k+1)*A^4,D*4,?_⟩
  intro n L body threshold leafTime inputBound bound visits setupSteps hn hbody ht hi hb hsetup
  let S := A*(L+1)^D
  have hA : 1≤A := by dsimp [A]; omega
  have hL : L+1≤S := (Nat.le_self_pow (by dsimp [D]; omega) _).trans
    (Nat.le_mul_of_pos_left _ hA)
  have hcommon : K*(L+1)^e≤S := Nat.mul_le_mul (by dsimp [A]; omega)
    (Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega))
  have hformula : SparseCountProgram.formulaBound n k≤S := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul (show c≤A by dsimp [A]; omega)
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega))
  have h := entryTime_le k n L body threshold leafTime inputBound bound visits setupSteps S
    hL hn hbody hformula (ht.trans hcommon) (hi.trans hcommon) (hb.trans hcommon)
    (hsetup.trans hcommon)
  simpa only [S,mul_pow,←pow_mul,Nat.mul_assoc] using h

/-- One fixed cap simultaneously satisfies actual startup, visits, the local
leaf, classification and power setup. It is chosen before any input or run. -/
theorem globalBound_polynomial (k Ki ei Kl el : ℕ) :
    ∃ C e : ℕ, 1≤C ∧ ∀ n m L body inputBound threshold localBound : ℕ,
      n≤L → m≤L → body≤SparseCountProgram.formulaBound n k →
      inputBound≤Ki*(L+1)^ei → threshold ≤ inputBound →
      localBound≤Kl*(L+1)^el →
      1220*inputBound+8*body+17≤C*(L+1)^e ∧
      DFSCountProgram.visitSpace k n m threshold≤C*(L+1)^e ∧
      localBound≤C*(L+1)^e ∧
      101*SparseCountProgram.formulaBound n k+103≤C*(L+1)^e ∧
      5*n+6≤C*(L+1)^e := by
  obtain ⟨Cv,dv,hv⟩ := dfsVisitSpace_polynomial k
    (SparsePriorityProgram.Selector.selectorCoefficient k) Ki ei
  let c := 2+(4+8*k)*(k+1)*2^k
  let C := 1220*Ki+109*c+Cv+Kl+131
  let e := ei+el+dv+k+2
  refine ⟨C,e,by dsimp [C]; omega,?_⟩
  intro n m L body inputBound threshold localBound hn hm hbody hi ht hl
  let P := (L+1)^e
  have h1 : 1≤P := Nat.one_le_pow' _ _
  have hnP : n≤P := hn.trans ((Nat.le_succ L).trans
    (Nat.le_self_pow (by dsimp [e]; omega) _))
  have hiP : inputBound≤Ki*P := hi.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)))
  have hlP : localBound≤Kl*P := hl.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)))
  have hf : SparseCountProgram.formulaBound n k ≤ c*P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul_left c
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega))
  have hvP : DFSCountProgram.visitSpace k n m threshold≤Cv*P := by
    apply (hv n m L threshold hn hm (ht.trans hi)).trans
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega))
  have hstart : 1220*inputBound+8*body+17≤(1220*Ki+8*c+17)*P := by
    rw [add_mul,add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hclass : 101*SparseCountProgram.formulaBound n k+103≤(101*c+103)*P := by
    rw [add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hpower : 5*n+6≤11*P := by omega
  exact ⟨hstart.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hvP.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hlP.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hclass.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega)),
    hpower.trans (Nat.mul_le_mul_right P (by dsimp [C]; omega))⟩

/-- The actual leaf wrapper's linear global-cap work and rounded local time
preserve the same exponential scale. The chosen cap depends only on input
length, and the rounding is confined to this proof-side time bound. -/
theorem leafTime_runtimeBound (k K globalDegree : ℕ) (C A : ℝ)
    (hC : 1≤C) (hA : 0≤A) (degree : ℕ) :
    ∃ D : ℝ, ∃ e : ℕ, 1≤D ∧ ∀ n L bound : ℕ,
      n≤L → bound≤K*(L+1)^globalDegree →
      ((3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+
        Nat.ceil (runtimeBound C A degree L n)+5479 : ℕ) : ℝ)≤
        runtimeBound D A e L n := by
  let c := 2+(4+8*k)*(k+1)*2^k
  let overhead := 3624*K+100*c+5590
  let power := globalDegree+k+1
  refine ⟨2*C+overhead,degree+power,?_,?_⟩
  · have := Nat.cast_nonneg (α := ℝ) overhead
    linarith
  intro n L bound hn hb
  let P := (L+1)^power
  have h1 : 1≤P := Nat.one_le_pow' _ _
  have hnP : n≤P := hn.trans ((Nat.le_succ L).trans
    (Nat.le_self_pow (by dsimp [power]; omega) _))
  have hbP : bound≤K*P := hb.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (by dsimp [power]; omega)))
  have hf : SparseCountProgram.formulaBound n k ≤ c*P := by
    apply (formulaBound_polynomial n k).trans
    apply Nat.mul_le_mul_left c
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [power]; omega))
  have hextra : 3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+5479≤
      overhead*(L+1)^power := by
    change _≤overhead*P
    dsimp only [overhead]
    rw [add_mul,add_mul]
    simp only [Nat.mul_assoc]
    omega
  have hcore : (Nat.ceil (runtimeBound C A degree L n) : ℝ)≤
      runtimeBound (2*C) A degree L n := by
    simpa only [runtimeBound_mul_constant] using
      SqrtLog.Execution.ceil_runtimeBound_le hC hA degree L n
  have h := QueryStreamBudgets.polynomial_overhead_runtime (2*C) A degree overhead power
    L n (Nat.ceil (runtimeBound C A degree L n))
    (3624*bound+100*(SparseCountProgram.formulaBound n k+1)+11*n+5479)
    (by linarith) hA hcore hextra
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLargeEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical large-input run. All leaf services are constructed
internally, and the fixed program has both full physical outputs and a single
primitive trace for its time and every-prefix visited-space bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry

open BitProgram StructuredCalls DisjointReuse SqrtLog.Statement NativeOuterBudgets

theorem run_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∃ C A : ℝ, ∃ d S e : ℕ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F → cutoff < n →
      ∃ time : ℕ, ∃ final : LocatedCfg
        (GuardedCompiler.primitive (Native.countingProgram cutoff k (NativeLeafProgram.command k))),
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) time
          (locatedInit (GuardedCompiler.primitive
            (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
            (Encoding.encodeCNF F)) final ∧
        final.config.state = .inl (decide (0 < SAT.count F)) ∧
        final.config.tapes ABI.countStack =
          Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
        final.config.tapes ABI.answerStack =
          Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
        (time : ℝ) ≤ runtimeBound C A d (Encoding.formulaBitLength F) n ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ time →
          Computation.Trace
            (locatedStep (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))) prefixSteps
            (locatedInit (GuardedCompiler.primitive
              (Native.countingProgram cutoff k (NativeLeafProgram.command k)))
              (Encoding.encodeCNF F)) intermediate →
          visitedSpace intermediate ≤ S * (Encoding.formulaBitLength F + 1) ^ e := by
  obtain ⟨Cp, _hCp, hsetup⟩ := Native.setupAfterFrontend_prepared_execution k hk
  let Ki := Cp + 1220
  obtain ⟨Cl, el, Ct, At, dt, Nleaf, hCt, hAt, _hdt, hleaf⟩ :=
    NativeLeafContract.uniform_contract k Ki 3 hk
  obtain ⟨Cg, eg, _hCg, hglobal⟩ := globalBound_polynomial k Ki 3 Cl el
  let K := Ki + Cg
  let E := 3 + eg
  obtain ⟨Cb, db, hbudget⟩ := entryTime_polynomial k K E
  obtain ⟨Cf, df, hCf, hleafTime⟩ := leafTime_runtimeBound k Cg eg Ct At hCt
    (by linarith) dt
  obtain ⟨C, hC, htime⟩ := runtime_of_tree_and_leaf k Cb db Cf At hCf (by linarith) df
  obtain ⟨S, e, hspace⟩ := primitiveSpace_polynomial K E
  obtain ⟨Ns, hs⟩ := Filter.eventually_atTop.mp
    (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 2))
  let cutoff := max 20 (max Nleaf Ns)
  refine ⟨cutoff, C, 256 + At, db + (4 * (k - 2) + 2) + df, S, e,
    hC, by linarith, ?_⟩
  intro n F hw hn
  let L := Encoding.formulaBitLength F
  let inputBound := Ki * (L + 1) ^ 3
  let bound := Cg * (L + 1) ^ eg
  let localTime := Nat.ceil (runtimeBound Ct At dt L n)
  let leafTime := NativeLeafContract.time n k localTime bound
  have hn20 : 20 ≤ n := by dsimp [cutoff] at hn; omega
  have hnleaf : Nleaf ≤ n := by dsimp [cutoff] at hn; omega
  have hscheduleTwo : 2 ≤ sparsifySchedule n := hs n (by dsimp [cutoff] at hn; omega)
  have hschedule : 1 ≤ sparsifySchedule n := by omega
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hmL : F.card ≤ L := by have := Encoding.formulaBitLength_lower F; omega
  have hbody := Native.canonical_normalized_body_length F hw
  have hiK : inputBound ≤ K * (L + 1) ^ E := Nat.mul_le_mul
    (by dsimp [K]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  have hbK : bound ≤ K * (L + 1) ^ E := Nat.mul_le_mul
    (by dsimp [K]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  obtain ⟨binary, frontSteps, a, hbinary, hlen, hfrontTime, hfront, ready⟩ := Native.frontend_eval F
  obtain ⟨setupSteps, b, hsetupRun, _prepared, setupReady, hsetupTime⟩ :=
    hsetup F binary (FiniteFallback.cutoffResult a false) (ready.cutoff false)
      hbinary hlen hn20 hschedule
  have hthreshold : (b.stacks 259).length ≤ inputBound := hsetupRun.final_bound 259
  obtain ⟨hstartup, hvisit, hlocal, hclassifier, hpower⟩ :=
    hglobal n F.card L (SubexpNormalizationCorrectness.normalizedBody F).length
      inputBound (b.stacks 259).length (Cl * (L + 1) ^ el) hnL hmL hbody
      le_rfl hthreshold le_rfl
  have hcontract := hleaf n L inputBound bound hnleaf hnL le_rfl (b.stacks 259)
    setupReady.threshold hlocal hclassifier hpower
  obtain ⟨visits, outerSteps, out, houterTime, houter, hcount, hanswer, _hsat, hvisits⟩ :=
    Native.outer_from_setup k hk F hw (FiniteFallback.cutoffResult a false) b
      hsetupRun setupReady hschedule (NativeLeafProgram.command k) leafTime
      hstartup hvisit hcontract
  let sourceBound := entrySpace n L inputBound bound
  obtain ⟨hfrontBudget, hdispatchBudget, houterBudget⟩ :=
    entrySpace_requirements n L inputBound bound
  have hentry := Native.entry_large_bounded_eval
    (Native.outerCommand k (NativeLeafProgram.command k)) F binary a out hn
    hfront hfrontTime ready hlen hfrontBudget hdispatchBudget
    (DFSCountProgram.boundedEval_mono houter houterBudget)
  obtain ⟨time, final, htrace, hhalt, hcountTape, hanswerTape, hprimitiveTime, hprefix⟩ :=
    Native.counting_primitive_from_entry (NativeLeafProgram.command k) F out hentry hcount hanswer
  have hfrontPolynomial := hfrontTime.trans (Native.frontendBound_polynomial F)
  change frontSteps ≤ 4000 * (L + 1) ^ 2 at hfrontPolynomial
  change outerSteps ≤ setupSteps +
    Native.dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
      (b.stacks 259).length leafTime bound visits +
    12 * Native.outerBoundary inputBound bound n + 14 at houterTime
  have hmeasured : time ≤ entryTime k n L
      (SubexpNormalizationCorrectness.normalizedBody F).length (b.stacks 259).length
      leafTime inputBound bound visits setupSteps := by
    dsimp [entryTime]
    omega
  have hsetupK : setupSteps ≤ K * (L + 1) ^ E := by
    apply le_trans (Nat.le_succ setupSteps |>.trans hsetupTime)
    apply le_trans (Nat.mul_le_mul_right ((L + 1) ^ 3) (show Cp ≤ Ki by dsimp [Ki]; omega)) hiK
  have hpoly := hbudget n L (SubexpNormalizationCorrectness.normalizedBody F).length
    (b.stacks 259).length leafTime inputBound bound visits setupSteps hnL hbody
    (hthreshold.trans hiK) hiK hbK hsetupK
  have hleafReal : (leafTime : ℝ) ≤ runtimeBound Cf At df L n :=
    hleafTime n L bound hnL le_rfl
  have htotal := htime n L visits leafTime time hn20 hschedule hnL hvisits hleafReal
    (hmeasured.trans hpoly)
  refine ⟨time, final, htrace, hhalt, hcountTape, hanswerTape, htotal, ?_⟩
  intro t z ht hz
  exact (hprefix t z ht hz).trans (hspace n L inputBound bound hnL hiK hbK)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run_oai

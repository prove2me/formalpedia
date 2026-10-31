-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:45.825789+00:00
-- url     : https://prove2.me/submissions/84dd50a9-5a87-4da5-a902-5fe13d881054

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact zero bytes for the native padded-polynomial constructors. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem toNat_false (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_cache_bits (p t : ℕ) [Fact p.Prime] (cache : RingProgram.ScalarCache p t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t) :
    cache.zero.val = List.replicate (baseWidth p t) false := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [cache.zero.property]
  · have hv := congrArg ZMod.val cache.zero_correct
    have hnum : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val = 0 := by
      simpa only [wordValue,ZMod.val_natCast,Nat.mod_eq_of_lt hz,ZMod.val_zero] using hv
    rw [hnum,toNat_false]

private theorem flatten_replicate_false (d B : ℕ) :
    (List.replicate d (List.replicate B false)).flatten = List.replicate (d*B) false := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
      congr 1
      ring

theorem flat_constant_zero {B : ℕ} (z : Word B)
    (hz : z.val = List.replicate B false) (d : ℕ) :
    RingProgram.flat (fun _ : Fin d => z) = List.replicate (d*B) false := by
  simp only [RingProgram.flat,hz,List.ofFn_const]
  exact flatten_replicate_false d B

theorem model_zero_bits (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t) :
    RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false := by
  change RingProgram.flat (fun _ : Fin d => cache.zero) = _
  exact flat_constant_zero cache.zero (zero_cache_bits 3 t cache hz) d

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact extraction of the native executor context from the source worker.
The four dispatcher ports are excluded from this context. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore)
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The executor context discards its source and saved controls. Thus a new
postfix source on333 does not change any arithmetic readiness premise. -/
theorem executionContext_evaluation (s : Store) :
    executionContext (evaluationInput s)=executionContext (Function.update s 21 []) := by
  funext i
  let p := executorPorts (ports (Fin.natAdd 4 i))
  have hp : p.val < 256 := (ports (Fin.natAdd 4 i)).isLt
  have h26 : p≠26 := by
    intro h
    have he : ports (Fin.natAdd 4 i)=26 := by
      apply Fin.ext
      have hh := congrArg (fun k : Fin 340 => k.val) h
      change (ports (Fin.natAdd 4 i)).val=26 at hh
      exact hh
    have hi : Fin.natAdd 4 i=(0 : Fin 256) := by
      simpa using congrArg ports.symm he
    have hh := congrArg Fin.val hi
    simp at hh
  have h333 : p≠333 := by intro h; rw [h] at hp; norm_num at hp
  have h335 : p≠335 := by intro h; rw [h] at hp; norm_num at hp
  have h336 : p≠336 := by intro h; rw [h] at hp; norm_num at hp
  change evaluationInput s p=Function.update s 21 [] p
  simp [evaluationInput,Function.update_apply,h26,h333,h335,h336]

theorem executionContext_evaluation_congr (s t : Store)
    (h : ∀ i : Fin 340, i.val < 256 → s i=t i) :
    executionContext (evaluationInput s)=executionContext (evaluationInput t) := by
  rw [executionContext_evaluation,executionContext_evaluation]
  funext i
  have hp : (executorPorts (ports (Fin.natAdd 4 i))).val < 256 :=
    (ports (Fin.natAdd 4 i)).isLt
  simp [executionContext,Function.update_apply,h _ hp]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram

theorem finish_frame (s : Store) (D W : ℕ) (i : Fin 256)
    (h243 : i ≠ 243) (h242 : i ≠ 242) (h192 : i ≠ 192) (h193 : i ≠ 193) :
    finish s D W i = s i := by
  simp [finish, h243, h242, h192, h193]

theorem encode_zero_array {B d : ℕ} (zero : Coeff B d)
    (hz : RingProgram.flat zero = List.replicate (d*B) false) (D : ℕ) :
    encode (List.replicate D zero) = List.replicate (D*(d*B)) false := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.replicate_succ, encode_cons, hz, ih, ← List.replicate_add]
      congr 1
      ring

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native readiness of the extracted source executor after the paid zero-array
initializer. The source dimension is the full count on210; no identification
with an earlier jet-length cache is made. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem context_value (s : LayoutSourceRowsProgram.Store) (i : Fin 256)
    (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    contextStore (executionContext s) i = s (executorPorts i) := by
  obtain ⟨j,rfl⟩ := ports.surjective i
  revert h26 h27 h28 h29
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro j
    fin_cases j
    · intro h _ _ _; exact False.elim (h (by decide))
    · intro _ _ h _; exact False.elim (h (by decide))
    · intro _ h _ _; exact False.elim (h (by decide))
    · intro _ _ _ h; exact False.elim (h (by decide))
  · intro j _ _ _ _
    exact SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_context _ _ _ _ _ _ _ _ j

theorem evaluation_value (s : LayoutSourceRowsProgram.Store) (i : Fin 256)
    (h21 : i ≠ 21) (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    contextStore (executionContext (evaluationInput s)) i = s (executorPorts i) := by
  rw [executionContext_evaluation, context_value _ i h26 h27 h28 h29]
  have hp : executorPorts i ≠ 21 := by
    intro he
    apply h21
    apply Fin.ext
    have hv := congrArg (fun j : Fin 340 => j.val) he
    change i.val = 21 at hv
    exact hv
  simp [hp]

theorem evaluation_empty21 (s : LayoutSourceRowsProgram.Store) :
    contextStore (executionContext (evaluationInput s)) 21 = [] := by
  rw [executionContext_evaluation, context_value _ 21 (by decide) (by decide)
    (by decide) (by decide)]
  simp [executorPorts]

theorem initialize_projection (s : LayoutSourceRowsProgram.Store) (D W : ℕ) :
    initializeFinish s D W ∘ executorPorts =
      LayoutSourceRowsProgramInitialize.finish (s ∘ executorPorts) D W := by
  funext i
  simp [initializeFinish,LayoutSourceRowsProgramInitialize.finish,
    Function.comp_def,executorPorts,Function.update_apply,Fin.ext_iff]

theorem initialized_value (s : LayoutSourceRowsProgram.Store) (D W : ℕ)
    (i : Fin 256) (hi : Preserved i) :
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) i =
      s (executorPorts i) := by
  rcases hi with ⟨h21,h26,h27,h28,h29,h243,h242,h192,h193⟩
  rw [evaluation_value _ i h21 h26 h27 h28 h29]
  have hp := congrFun (initialize_projection s D W) i
  change initializeFinish s D W (executorPorts i) = _ at hp
  rw [hp]
  exact LayoutSourceRowsProgramInitialize.finish_frame _ D W i h243 h242 h192 h193

theorem initialized_cache (s : LayoutSourceRowsProgram.Store) (D W : ℕ) :
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 192 =
        List.replicate (D*W) false ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 193 =
        List.replicate D true ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 242 =
        List.replicate (D*W) false ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 243 =
        List.replicate D true := by
  repeat' constructor

variable (p t : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
  {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))

omit [Fact (Nat.Prime p)] in
theorem initialized_arithmetic (s : LayoutSourceRowsProgram.Store) (D W : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (s ∘ executorPorts) width frame) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (contextStore (executionContext (evaluationInput (initializeFinish s D W)))) width frame := by
  constructor
  · intro i h8 h9
    rw [initialized_value s D W _
      ((by unfold Preserved; decide : ∀ j : Fin 32, Preserved (DensePolynomialProgram.RingCall.ports j)) i)]
    exact H.high i h8 h9
  · intro i
    rw [initialized_value s D W _
      ((by unfold Preserved; decide : ∀ j : Fin 20,
        Preserved (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts j))) i)]
    exact H.low i
  · rw [initialized_value s D W 104 (by unfold Preserved; decide)]
    exact H.width
  · exact H.scalarWidthLength
  · rw [initialized_value s D W 204 (by unfold Preserved; decide)]
    exact H.degreeLength
  · rw [initialized_value s D W 120 (by unfold Preserved; decide)]
    exact H.scratch
  · intro i hlo hhi
    have hi : Preserved i := by
      unfold Preserved
      repeat' constructor
      all_goals intro he
      all_goals subst i
      all_goals omega
    rw [initialized_value s D W i hi]
    exact H.work i hlo hhi

theorem initialized_ready
    (ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d))
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false)
    (s : LayoutSourceRowsProgram.Store) (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (s ∘ executorPorts) width frame) (E : Empty s) :
    PolynomialExecutorProgram.Ready p t M cache ops table D width frame
      (executionContext (evaluationInput (initializeFinish s D (d*baseWidth p t)))) := by
  constructor
  · exact initialized_arithmetic p t M cache table s D _ width frame H
  · exact evaluation_empty21 _
  · rw [initialized_value s D _ 99 (by unfold Preserved; decide)]; exact E.empty99
  · rw [initialized_value s D _ 121 (by unfold Preserved; decide)]; exact E.empty121
  · rw [initialized_value s D _ 122 (by unfold Preserved; decide)]; exact E.empty122
  · rw [initialized_value s D _ 240 (by unfold Preserved; decide)]; exact E.empty240
  · rw [initialized_value s D _ 241 (by unfold Preserved; decide)]; exact E.empty241
  · rw [initialized_value s D _ 244 (by unfold Preserved; decide)]; exact E.empty244
  · rw [initialized_value s D _ 245 (by unfold Preserved; decide)]; exact E.empty245
  · intro i
    rw [initialized_value s D _ _
      ((by unfold Preserved; decide : ∀ j, Preserved (SubexpConvolutionControl.bufferPorts j)) i)]
    exact E.buffers i
  · rw [(initialized_cache s D _).1]
    exact (LayoutSourceRowsProgramInitialize.encode_zero_array ops.zeroRun.1 hzero D).symm
  · rw [(initialized_cache s D _).2.1]
    simp
  · rw [(initialized_cache s D _).2.2.1]
    exact (LayoutSourceRowsProgramInitialize.encode_zero_array ops.zeroRun.1 hzero D).symm

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadinessModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary-model specialization of source-executor readiness. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram

theorem model_initialized_ready (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : LayoutSourceRowsProgram.Store) (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s) :
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput (initializeFinish s D (d*baseWidth 3 t)))) := by
  exact initialized_ready 3 t M cache (HornerProgram.modelTable t a M cache)
    (RingProgram.modelProgram t a M cache)
    (DensePolynomialProgram.model_zero_bits t a M cache hz) s D width frame H E

theorem model_ready_of_low_agreement_oai (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s after : LayoutSourceRowsProgram.Store) (D : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s)
    (hf : ∀ i : Fin 340, i.val < 256 → after i = initializeFinish s D (d*baseWidth 3 t) i) :
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput after)) := by
  rw [executionContext_evaluation_congr after (initializeFinish s D (d*baseWidth 3 t)) hf]
  exact model_initialized_ready t a M cache hz s D width frame H E

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement_oai

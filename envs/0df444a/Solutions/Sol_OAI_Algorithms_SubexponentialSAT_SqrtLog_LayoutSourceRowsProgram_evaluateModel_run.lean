-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:05:33.436596+00:00
-- url     : https://prove2.me/submissions/74abd38a-1529-432f-9c58-a841329cb9c2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_model_flat_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem ExecutesIn.seq {a b : Code} {A B : ℕ} {s t u : Store}
    (ha : ExecutesIn a A s t) (hb : ExecutesIn b B t u) :
    ExecutesIn (.seq a b) (A+B) s u := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesIn.mono {c : Code} {A B : ℕ} {s t : Store}
    (h : ExecutesIn c A s t) (hab : A ≤ B) : ExecutesIn c B s t := by
  intro regs
  obtain ⟨n,rf,hn,he⟩ := h regs
  exact ⟨n,rf,hn.trans hab,he⟩

theorem transfer_run (src dst : Fin 340) (s : Store) (h : src ≠ dst) :
    ExecutesIn (transfer src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.transfer_eval (⟨regs,s⟩ : Data) src dst 0 1 h (by decide)
  exact ⟨_,_,le_rfl,he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

theorem resetList_eval (is : List (Fin 16)) (d : StructuredProgram.State 16 128) :
    StructuredProgram.Eval (resetList is) is.length d (resetData is d) := by
  induction is generalizing d with
  | nil => simpa [resetList, resetData] using StructuredProgram.Eval.skip d
  | cons i is ih =>
      have h := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.set i false) d)
        (ih ((StructuredProgram.Atom.set i false).eval d))
      have hd : resetData is ((StructuredProgram.Atom.set i false).eval d) = resetData (i :: is) d := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = i <;> by_cases hm : j ∈ is <;>
            simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg,
              execInstr, Function.update, hj, hm]
        · rfl
      simpa only [resetList, List.length_cons, hd, Nat.add_comm] using h

theorem reset_trace (regs : Fin 16 → Bool) (stk : Fin 128 → List Bool) :
    Trace resetProgram 17 ⟨some resetProgram.entry, regs, stk⟩ ⟨none, fun _ => false, stk⟩ := by
  have h := resetList_eval (List.finRange 16) ⟨regs, stk⟩
  have he : StructuredProgram.Eval (resetList (List.finRange 16)) 16
      ⟨regs, stk⟩ ⟨fun _ => false, stk⟩ := by
    simpa [resetData] using h
  exact StructuredProgram.compiled_halt_trace he 26 15

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code ExecutesIn)

theorem smallPorts_injective : Function.Injective smallPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 256 => x.val) h)

@[simp] theorem restore_self (s : Store) : restore s (s ∘ smallPorts) = s := by
  funext j
  by_cases hj : ∃ i, smallPorts i = j
  · obtain ⟨i, rfl⟩ := hj
    exact smallPorts_injective.extend_apply _ _ i
  · exact Function.extend_apply' _ _ _ hj

theorem reset_eval (regs : Fin 16 → Bool) (s : Store) :
    Eval reset 17 (⟨regs, s⟩ : State 16 256) ⟨fun _ => false, s⟩ := by
  let a : State 16 128 := ⟨regs, s ∘ smallPorts⟩
  let b : State 16 128 := ⟨fun _ => false, s ∘ smallPorts⟩
  have hin : embedState id smallPorts (⟨regs, s⟩ : State 16 256) a = ⟨regs, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id smallPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState id smallPorts (⟨regs, s⟩ : State 16 256) b = ⟨fun _ => false, s⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id smallPorts_injective
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intros; rfl
    · intros; rfl
  have ht : Trace SubexpEvaluationProgram.resetProgram 17
      (a.withPC (some SubexpEvaluationProgram.resetProgram.entry)) (b.withPC none) :=
    SubexpEvaluationProgram.reset_trace regs (s ∘ smallPorts)
  have he := eval_call_lifted SubexpEvaluationProgram.resetProgram id smallPorts
    (⟨regs, s⟩ : State 16 256) Function.injective_id smallPorts_injective ht
  simpa only [hin, hout, reset] using he

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem executorPorts_injective : Function.Injective executorPorts := Fin.castAdd_injective _ _

theorem resetExecutor_eval (s : Store) (regs : Fin 16 → Bool) :
    Eval resetExecutor 18 (⟨regs,s⟩ : Data) (⟨fun _ => false,s⟩ : Data) := by
  let a : Data := ⟨regs,s⟩
  have h := SubexpDenseLiteralPadding.reset_eval regs (s ∘ executorPorts)
  have he := eval_liftCommand_from_state SubexpDenseLiteralPadding.reset 26 26 id executorPorts a
    Function.injective_id executorPorts_injective h
  have hout : embedState id executorPorts a
      (⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256)=(⟨fun _ => false,s⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      exact embedState_register id executorPorts a _ Function.injective_id i
    · have hb := congrArg StructuredProgram.State.stacks
        (embedState_project id executorPorts a Function.injective_id executorPorts_injective)
      change Function.extend executorPorts (s ∘ executorPorts) s=s at hb ⊢
      exact hb
  rw [hout] at he
  exact he

/-- The native executor returns the plain array on240, consumes its source26,
and preserves the entire remaining caller bank. -/
theorem execute_run {l : ℕ} (p : Program 16 256 l) (K : ℕ) (s : Store) (bits : List Bool)
    (hrun : ∃ rf, RunsIn p K
      ((⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256).withPC (some p.entry))
      ((⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240 bits⟩ :
        State 16 256).withPC none)) :
    ExecutesIn (execute p) (K+18) s
      (Function.update (Function.update s 26 []) 240 bits) := by
  intro regs
  obtain ⟨rf,n,hn,ht⟩ := hrun
  let a : Data := ⟨fun _ => false,s⟩
  let out : State 16 256 :=
    ⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240 bits⟩
  have hc := eval_call_from_state p id executorPorts a
    Function.injective_id executorPorts_injective ht
  have hs : (embedState id executorPorts a out).stacks=
      Function.update (Function.update s 26 []) 240 bits := by
    change Function.extend executorPorts out.stacks s = _
    dsimp only [out]
    rw [ProgramLinking.extend_update executorPorts_injective,
      ProgramLinking.extend_update executorPorts_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project id executorPorts a Function.injective_id executorPorts_injective)
    change Function.extend executorPorts (s ∘ executorPorts) s=s at hb
    rw [hb]
    rfl
  have hout : embedState id executorPorts a out=
      (⟨(embedState id executorPorts a out).regs,
        Function.update (Function.update s 26 []) 240 bits⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  change Eval _ n a (embedState id executorPorts a out) at hc
  rw [hout] at hc
  exact ⟨18+n,_,by omega,(resetExecutor_eval s regs).seq hc⟩

theorem evaluateRow_run {l : ℕ} (p : Program 16 256 l) (K : ℕ) (s : Store) (bits : List Bool)
    (h335 : s 335=[]) (h336 : s 336=[])
    (hcore : ExecutesIn (execute p) K (evaluationInput s)
      (Function.update (Function.update (evaluationInput s) 26 []) 240 bits)) :
    ExecutesIn (evaluateRow p) (K+6*(s 21).length+6*(s 26).length+3*(s 333).length+15) s
      (Function.update (Function.update s 333 []) 240 bits) := by
  let s1 := Function.update (Function.update s 21 []) 335 (s 21).reverse
  let s2 := Function.update (Function.update s1 26 []) 336 (s 26).reverse
  let s3 := evaluationInput s
  let s4 := Function.update (Function.update s3 26 []) 240 bits
  let s5 := Function.update (Function.update s4 335 []) 21 (s 21)
  have h1 : ExecutesIn (transfer 21 335) (3*(s 21).length+3) s s1 := by
    simpa [s1,h335] using transfer_run 21 335 s (by decide)
  have h2 : ExecutesIn (transfer 26 336) (3*(s 26).length+3) s1 s2 := by
    simpa [s1,s2,h336] using transfer_run 26 336 s1 (by decide)
  have h3 : ExecutesIn (transfer 333 26) (3*(s 333).length+3) s2 s3 := by
    simpa [s3,s2,s1,evaluationInput] using transfer_run 333 26 s2 (by decide)
  have h4 : ExecutesIn (execute p) K s3 s4 := hcore
  have h5 : ExecutesIn (transfer 335 21) (3*(s 21).length+3) s4 s5 := by
    simpa [s5,s4,s3,evaluationInput] using transfer_run 335 21 s4 (by decide)
  have h6 := transfer_run 336 26 s5 (by decide)
  have he6 : Function.update (Function.update s5 336 []) 26
      ((s5 336).reverse++s5 26)=Function.update (Function.update s 333 []) 240 bits := by
    funext i
    by_cases h21 : i=21 <;> by_cases h26 : i=26 <;> by_cases h333 : i=333 <;>
      by_cases hi335 : i=335 <;> by_cases hi336 : i=336 <;> by_cases h240 : i=240 <;>
      simp [s5,s4,s3,evaluationInput,h21,h26,h333,hi335,hi336,h240,h335,h336]
  rw [he6] at h6
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono
  simp [s5,s4,s3,evaluationInput]
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Small, extensional frame facts for the row interpreter. These proofs
split only its four control ports; they never enumerate the 256-stack frame. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram StructuredCalls
open SubexpPostfixGlobal (reindexCfg)
open SubexpPostfixInterpreter (cfg)

theorem physicalCfg_frame {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool)
    (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    (physicalCfg pc v p op code depth operands context).stacks i = contextStore context i := by
  obtain ⟨j, rfl⟩ := ports.surjective i
  revert h26 h28 h27
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k
    · intro h _ _; exact False.elim (h ports_zero)
    · intro _ h _; exact False.elim (h ports_one)
    · intro _ _ h; exact False.elim (h ports_two)
    · intro _ _ _
      simp [physicalCfg, contextStore, reindexCfg, cfg, Fin.addCases,
        SubexpPostfixControl.quadruple]
  · intro k _ _ _
    simp [physicalCfg, contextStore, reindexCfg, cfg]

theorem physicalCfg_false_regs {l : ℕ} (pc : Option (Fin l))
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc false false false code depth operands context).regs = fun _ => false := by
  funext i
  refine Fin.addCases (m := 3) (n := 13) ?_ ?_ i
  · intro j; fin_cases j <;> rfl
  · intro j; simp [physicalCfg, reindexCfg, cfg]

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stored arithmetic data for the row interpreter. Readiness is stated on
the fixed context alone, and proved invariant when source, operand, and
temporary argument ports change. No arithmetic trace is assumed here. -/

namespace SubexponentialSAT.SubexpRowPostfixContext

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Store bufferPorts)
open SubexpRowPostfixInterpreter (physicalCfg contextStore)

theorem operandStore_frame (context : Fin 252 → List Bool)
    (code depth operands : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    operandStore context code depth operands i = contextStore context i :=
  SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem executorStore_decompose (s : Store) (source : List Bool)
    (h26 : s 26=source) (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[]) :
    s ∘ executorPorts=operandStore (executionContext s) source [] [] := by
  funext i
  obtain ⟨j,rfl⟩ := ports.surjective i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k <;>
      simp [operandStore,physicalCfg,SubexpPostfixGlobal.reindexCfg,
        SubexpPostfixInterpreter.cfg,SubexpPostfixControl.quadruple,
        executorPorts,Fin.addCases,h26,h27,h28,h29]
  · intro k
    simp [operandStore,physicalCfg,SubexpPostfixGlobal.reindexCfg,
      SubexpPostfixInterpreter.cfg,executionContext]

theorem evaluationInput_decompose (s : Store) (source : List Bool)
    (hsource : s 333=source.reverse)
    (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[]) :
    evaluationInput s ∘ executorPorts=
      operandStore (executionContext (evaluationInput s)) source [] [] := by
  apply executorStore_decompose
  · simp [evaluationInput,hsource]
  · simp [evaluationInput,h27]
  · simp [evaluationInput,h28]
  · simp [evaluationInput,h29]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-sensitive costs and validity of the generic coefficient-array
interpreter, independently of its native arithmetic implementation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT

private theorem serializeCode_append {A : Type*} (encode : A → List Bool)
    (xs ys : List (Algorithm.Instr A)) :
    SubexpPostfixControl.serializeCode encode (xs ++ ys) =
      SubexpPostfixControl.serializeCode encode xs ++ SubexpPostfixControl.serializeCode encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SubexpPostfixControl.serializeCode,ih,List.append_assoc]

/-- Both source instructions and their literal payload are paid by actual
input bits: every instruction has two framing bits. -/
theorem source_length {B d : ℕ} (e : Algorithm.Expr (List (Coeff B d))) :
    (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length =
      2 * (e.size + literalBytes e) := by
  induction e with
  | lit P => simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
      SubexpPostfixControl.serializeInstr,Algorithm.Expr.size,literalBytes]; omega
  | add e f he hf =>
      simp only [Algorithm.Expr.compile,serializeCode_append,List.length_append,he,hf,
        SubexpPostfixControl.serializeCode,SubexpPostfixControl.serializeInstr,
        List.length_cons,List.length_nil,Algorithm.Expr.size,literalBytes]
      omega
  | mul e f he hf =>
      simp only [Algorithm.Expr.compile,serializeCode_append,List.length_append,he,hf,
        SubexpPostfixControl.serializeCode,SubexpPostfixControl.serializeInstr,
        List.length_cons,List.length_nil,Algorithm.Expr.size,literalBytes]
      omega

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit bounds for the fixed source interpreter. Source size and
raw literal bytes are charged separately from the retained coefficient count. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

theorem totalBudget_le_source {B d : ℕ} (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) :
    totalBudget J e ≤
      300000 * ((SubexponentialSAT.SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length+1) *
        (J+1)^3 * (d+1)^3 * (B+1)^2 := by
  have h : e.size + literalBytes e + 1 ≤
      (SubexponentialSAT.SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length + 1 := by
    rw [source_length]
    omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)))


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

private theorem clear_operandSource (context : Fin 252 → List Bool) (source : List Bool) :
    Function.update (operandStore context source [] []) 26 []=contextStore context := by
  funext i
  by_cases h26 : i=26
  · subst i; simp [contextStore]
  by_cases h28 : i=28
  · subst i; simp [operandStore,contextStore]
  by_cases h27 : i=27
  · subst i; simp [operandStore,contextStore]
  simp only [Function.update_apply,h26,ite_false]
  exact operandStore_frame context source [] [] i h26 h28 h27

private theorem input_cfg {l : ℕ} (pc : Option (Fin l))
    (context : Fin 252 → List Bool) (source : List Bool) :
    ((⟨fun _ => false,operandStore context source [] []⟩ : State 16 256).withPC pc)=
      physicalCfg pc false false false source [] [] context := by
  apply congrArg₂ (Cfg.mk pc)
  · exact (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_false_regs pc source [] [] context).symm
  · rfl

theorem executeModel_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
    (s : Store)
    (hs : s ∘ executorPorts=operandStore context
      (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] []) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
          (RingProgram.modelRing t ht hd a M cache))).eval) ∧
      ExecutesIn executeModel
        (PolynomialExecutorProgram.totalBudget J e+18*(J*(d*baseWidth 3 t))+46) s
        (Function.update (Function.update s 26 []) 240 (DensePolynomialProgram.encode out)) := by
  obtain ⟨out,rf,hrun,hlen,hmeaning⟩ :=
    PolynomialExecutorProgram.model_flat_run t ht hd a M cache hz J width frame context H e
  refine ⟨out,hlen,hmeaning,?_⟩
  have hh : ∃ rf, RunsIn PolynomialExecutorProgram.flatProgram
      (PolynomialExecutorProgram.totalBudget J e+18*(J*(d*baseWidth 3 t))+28)
      ((⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256).withPC
        (some PolynomialExecutorProgram.flatProgram.entry))
      ((⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240
        (DensePolynomialProgram.encode out)⟩ : State 16 256).withPC none) := by
    refine ⟨rf,?_⟩
    rw [hs,clear_operandSource,input_cfg]
    exact hrun
  have h := execute_run PolynomialExecutorProgram.flatProgram _ s _ hh
  simpa [executeModel,Nat.add_assoc] using h

/-- The source byte count controls the full native interpretation cost.
Both source-generation controls are restored before returning the array. -/
theorem evaluateModel_run_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (s : Store)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame
        (executionContext (evaluationInput s)))
    (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
    (hsource : s 333=(SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).reverse)
    (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[])
    (h335 : s 335=[]) (h336 : s 336=[]) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
          (RingProgram.modelRing t ht hd a M cache))).eval) ∧
      ExecutesIn (evaluateRow PolynomialExecutorProgram.flatProgram)
        (300000*((s 333).length+1)*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2+
          18*(J*(d*baseWidth 3 t))+46+6*(s 21).length+6*(s 26).length+
          3*(s 333).length+15) s
        (Function.update (Function.update s 333 []) 240 (DensePolynomialProgram.encode out)) := by
  obtain ⟨out,hlen,hmeaning,hcore⟩ := executeModel_run t ht hd a M cache hz J width frame
    (executionContext (evaluationInput s)) H e (evaluationInput s)
    (evaluationInput_decompose s _ hsource h27 h28 h29)
  refine ⟨out,hlen,hmeaning,?_⟩
  have hr := evaluateRow_run PolynomialExecutorProgram.flatProgram _ s
    (DensePolynomialProgram.encode out) h335 h336 hcore
  apply hr.mono
  have hb := PolynomialExecutorProgram.totalBudget_le_source J e
  have hl : (s 333).length=
      (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length := by
    simp [hsource]
  rw [←hl] at hb
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluateModel_run_oai

-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:39:25.203699+00:00
-- url     : https://prove2.me/submissions/ad455c6c-bb69-44a5-b4eb-a4e6ed6e23e2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S137
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual normalization of a positive binary counter word

The logarithm preparer reverses its input and removes high zeroes together
with the leading one. This wrapper physically restores that one and reverses
the remaining word. Positive inputs therefore retain their exact value and
have width log2(value)+1. All three registers and both work stacks are clean
at return, even when the incoming registers are arbitrary.
-/

namespace SubexponentialSAT.CounterNormalizeProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms

theorem normalized_value (bits : List Bool) (hp : 0 < value bits) :
    value (normalized bits) = value bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [value] at hp
  | append_singleton bits bit ih =>
    cases bit with
    | false =>
      have hp' : 0 < value bits := by
        simpa [SubexpParameterProgram.value_append, value] using hp
      simpa [normalized, List.reverse_append, SubexpParameterProgram.trimTail,
        SubexpParameterProgram.value_append, value] using ih hp'
    | true =>
      simp [normalized, List.reverse_append, SubexpParameterProgram.trimTail]

theorem normalized_length (bits : List Bool) :
    (normalized bits).length = Nat.log2 (value bits) + 1 := by
  simp [normalized, SubexpParameterProgram.trimTail_reverse_length]

theorem normalized_eq_fixedBits (bits : List Bool) (hp : 0 < value bits) :
    normalized bits = SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits) := by
  have hcap : value bits < 2 ^ (Nat.log2 (value bits) + 1) := by
    simpa only [normalized_value bits hp, normalized_length] using
      SubexpParameterProgram.value_lt_two_pow_length (normalized bits)
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [normalized_length, SubexpLiftRing.fixedBits_length]
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hcap,
      ← CounterPrograms.value_eq_toNat]
    exact normalized_value bits hp

private theorem data_ext {a b : Data} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) :
    a = b := by cases a; cases b; cases hr; cases hs; rfl

theorem reset_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    StructuredCalls.Eval reset 3 (state regs bits []) (state zeroRegs bits []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs bits [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply StructuredCalls.Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply data_ext
  · funext i
    fin_cases i <;>
      simp [state, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

theorem prepare_eval (bits : List Bool) :
    ∃ n, n ≤ 6 * bits.length + 9 ∧
      StructuredCalls.Eval (.call SubexpParameterProgram.prepareLogProgram) n
        (state zeroRegs bits [])
        (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpParameterProgram.prepareLog_runs bits
  have ha : initial SubexpParameterProgram.prepareLogProgram bits =
      (state zeroRegs bits []).withPC (some SubexpParameterProgram.prepareLogProgram.entry) := by
    simp only [initial, state, State.withPC ]
    congr 1
    first | done | (funext i; fin_cases i <;> rfl)
  have hb : terminal SubexpParameterProgram.prepareLogProgram
        (SubexpParameterProgram.trimTail bits.reverse) =
      (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)).withPC none := by
    simp only [terminal, state, State.withPC ]
    congr 1
    first | done | (funext i; fin_cases i <;> rfl)
  exact ⟨n, hn, .call _ (by simpa only [ha, hb] using ht)⟩

theorem pushTop_eval (d : Data) : StructuredCalls.Eval pushTop 2 d (pushed d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) d).seq
    (StructuredProgram.Eval.atom (.push (1 : Fin 3) 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

theorem reverse_eval (d : Data) :
    StructuredCalls.Eval (.call reverseProgram) (3 * (d.stacks 1).length + 3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 1 0 0 1 (by decide) (by decide) d.regs d.stacks)

theorem restore_eval (tail : List Bool) :
    StructuredCalls.Eval restore (3 * tail.length + 8) (state zeroRegs [] tail)
      (state zeroRegs (true :: tail).reverse []) := by
  have h := (pushTop_eval (state zeroRegs [] tail)).seq
    (reverse_eval (pushed (state zeroRegs [] tail)))
  have heq : transferred (pushed (state zeroRegs [] tail)) =
      state zeroRegs (true :: tail).reverse [] := by
    apply data_ext
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, zeroRegs, readRegs]
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, StackRoutines.transferStacks]
  convert h using 1
  · simp [pushed, state]
    omega
  · exact heq.symm

theorem command_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (normalized bits) []) ∧ n ≤ 9 * bits.length + 20 := by
  obtain ⟨n, hn, he⟩ := prepare_eval bits
  refine ⟨3 + (n + (3 * (SubexpParameterProgram.trimTail bits.reverse).length + 8)),
    (reset_eval regs bits).seq (he.seq (restore_eval _)), ?_⟩
  have hlen : (SubexpParameterProgram.trimTail bits.reverse).length ≤ bits.length := by
    simpa using SubexpParameterProgram.trimTail_length_le bits.reverse
  omega

theorem normalize_eval (regs : Fin 3 → Bool) (bits : List Bool) (hp : 0 < value bits) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []) ∧
      n ≤ 9 * bits.length + 20 := by
  simpa only [normalized_eq_fixedBits bits hp] using command_eval regs bits

end SubexponentialSAT.CounterNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical, positive encodings for exact integer row signatures.  The
added one is common to all assignments and makes the normalizer total on
all legitimate row results, including the empty head. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem normalizeRegs_injective : Function.Injective normalizeRegs := Fin.castAdd_injective _ _
theorem normalizePorts_injective : Function.Injective normalizePorts := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa [normalizePorts] using this

theorem normalizeCall_eval (regs : Fin 8 → Bool) (W out : List Bool)
    (hp : 0 < SubexponentialSAT.BinaryArithmetic.toNat out) :
    ∃ t ≤ 9*out.length+21, ∃ rf,
      Eval normalizeCall t (dotState regs W [] [] out)
        (dotState rf W [] [] (canonical (SubexponentialSAT.BinaryArithmetic.toNat out))) := by
  have hp' : 0 < SubexponentialSAT.CounterPrograms.value out := by
    simpa only [SubexponentialSAT.CounterPrograms.value_eq_toNat] using hp
  obtain ⟨t, he, ht⟩ := SubexponentialSAT.CounterNormalizeProgram.normalize_eval
    (regs ∘ normalizeRegs) out hp'
  have ha : projectState normalizeRegs normalizePorts (dotState regs W [] [] out) =
      SubexponentialSAT.CounterNormalizeProgram.state (regs ∘ normalizeRegs) out [] := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ normalizeRegs))
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [←ha] at he
  have h := eval_call_from_state SubexponentialSAT.CounterNormalizeProgram.program normalizeRegs normalizePorts
    (dotState regs W [] [] out) normalizeRegs_injective normalizePorts_injective
    (compiled_halt_trace he 0 0)
  let rf := (embedState normalizeRegs normalizePorts (dotState regs W [] [] out)
    (SubexponentialSAT.CounterNormalizeProgram.state SubexponentialSAT.CounterNormalizeProgram.zeroRegs
      (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) [])).regs
  have hend : embedState normalizeRegs normalizePorts (dotState regs W [] [] out)
      (SubexponentialSAT.CounterNormalizeProgram.state SubexponentialSAT.CounterNormalizeProgram.zeroRegs
        (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) []) =
      dotState rf W [] [] (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) := by
    apply embedState_eq_of_ports normalizeRegs normalizePorts _ _ _
      normalizeRegs_injective normalizePorts_injective
    · intro i
      exact (embedState_register normalizeRegs normalizePorts _ _ normalizeRegs_injective i)
    · intro i hi
      exact (embedState_register_frame normalizeRegs normalizePorts _ _ i hi)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0, h.symm⟩
      fin_cases i <;> simp_all [dotState]
  simp only [SubexponentialSAT.CounterPrograms.value_eq_toNat] at h
  change Eval normalizeCall (t+1) _
    (embedState normalizeRegs normalizePorts _
      (SubexponentialSAT.CounterNormalizeProgram.state _ (canonical _) [])) at h
  rw [hend] at h
  exact ⟨t+1, by omega, rf, h⟩

theorem canonicalRowCommand_eval (regs : Fin 8 → Bool) (W : List Bool)
    (coeffs : List (List Bool)) (bits : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ t ≤ canonicalRowBudget W coeffs, ∃ rf,
      Eval canonicalRowCommand t (dotState regs W coeffs bits [true])
        (dotState rf W [] [] (canonical (1+rowValue W coeffs bits))) := by
  obtain ⟨t,ht,rm,out,he,hv,hl⟩ := rowCommand_eval regs W coeffs bits [true] hlen
  have hv' : SubexponentialSAT.BinaryArithmetic.toNat out = 1+rowValue W coeffs bits := by
    simpa [SubexponentialSAT.BinaryArithmetic.toNat] using hv
  obtain ⟨u,hu,rf,hf⟩ := normalizeCall_eval rm W out (by omega)
  rw [hv'] at hf
  exact ⟨t+u, by dsimp [canonicalRowBudget]; omega, rf, he.seq hf⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem signatureStep_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (row : List (List Bool)) (rows : List (List (List Bool))) (key : List Bool)
    (hlen : row.length=bits.length) :
    ∃ t ≤ signatureStepCost W bits row, ∃ rf,
      Eval signatureStep t (signatureState regs W bits (row::rows) key)
        (signatureState rf W bits rows (Encoding.frame (rowKey W bits row)++key)) := by
  let d := signatureState regs W bits (row::rows) key
  obtain ⟨a,hea,hsa⟩ := readWord_eval (13 : Fin 15) 9 11
    (by decide) (by decide) (by decide) d (words row) (words (rows.map words)) rfl rfl rfl
  obtain ⟨b,heb,hsb⟩ := copy_eval (12 : Fin 15) 10 11
    (by decide) (by decide) (by decide) a (by rw [hsa]; rfl)
  let c : SignatureData := ⟨Function.update b.regs 0 true, Function.update b.stacks 2 [true]⟩
  have hb2 : b.stacks 2 = [] := by rw [hsb,hsa]; rfl
  have hec : Eval signatureSeed 2 b c := by
    have h := (StructuredProgram.Eval.atom (.set (0 : Fin 8) true) b).seq
      (StructuredProgram.Eval.atom (.push (2 : Fin 15) 0) _)
    exact .base (by simpa [signatureSeed,c,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC,execInstr,hb2] using h)
  have hproj : projectState id rowCallPorts c = dotState c.regs W row bits [true] := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;> simp [rowCallPorts,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks]
  obtain ⟨tc,htc,rc,hecRow⟩ := canonicalRowCommand_eval c.regs W row bits hlen
  rw [←hproj] at hecRow
  have hecall := eval_call_from_state canonicalRowProgram id rowCallPorts c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hecRow 9 2)
  let e : SignatureData := ⟨rc, Function.update (Function.update
    (Function.update c.stacks 9 []) 10 []) 2 (rowKey W bits row)⟩
  have hembed : embedState id rowCallPorts c
      (dotState rc W [] [] (rowKey W bits row)) = e := by
    apply embedState_eq_of_ports id rowCallPorts c _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i
      fin_cases i <;> simp [e,rowCallPorts,c,hsb,hsa,d,signatureState,
        dotState,StackRoutines.copyStacks] ; rfl
    · intro i hi
      have h2 : i≠2 := fun h => hi ⟨2,h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨9,h.symm⟩
      have h10 : i≠10 := fun h => hi ⟨10,h.symm⟩
      simp [e,h2,h9,h10]
  change Eval rowCall (tc+1) c (embedState id rowCallPorts c
    (dotState rc W [] [] (rowKey W bits row))) at hecall
  rw [hembed] at hecall
  obtain ⟨f,hef,hsf⟩ := emitFrame_eval (2 : Fin 15) 14 11
    (by decide) (by decide) (by decide) e (by
      simp [e,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks])
  have he2 : e.stacks 2 = rowKey W bits row := by simp [e]
  have hf : f = signatureState f.regs W bits rows
      (Encoding.frame (rowKey W bits row)++key) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i
    fin_cases i <;> simp [e,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks]
  have ha12 : a.stacks 12=bits := by rw [hsa]; rfl
  have he := hea.seq (heb.seq (hec.seq (hecall.seq hef)))
  rw [hf] at he
  refine ⟨_,?_,f.regs,he⟩
  rw [ha12,he2]
  dsimp [signatureStepCost]
  omega

theorem signaturePeek_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) :
    Eval signaturePeek 1 (signatureState regs W bits rows key)
      (signatureReady regs W bits rows key) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem signatureLoop_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row∈rows, row.length=bits.length) :
    ∃ t ≤ signatureCost W bits rows, ∃ rf,
      Eval signatureLoop t (signatureReady regs W bits rows key)
        (signatureState rf W bits [] (signatureValue W bits rows++key)) := by
  induction rows generalizing regs key with
  | nil =>
      refine ⟨1,by simp [signatureCost],(signatureReady regs W bits [] key).regs,?_⟩
      simpa [signatureLoop, signatureBody, signatureReady, signatureState,
        signatureValue, words, readRegs] using (Eval.while_false
        (show (signatureReady regs W bits [] key).regs 1=false by
          simp [signatureReady,signatureState,words,readRegs]) :
          Eval signatureLoop 1 (signatureReady regs W bits [] key)
            (signatureReady regs W bits [] key))
  | cons row rows ih =>
      obtain ⟨t,ht,rm,he⟩ := signatureStep_eval
        (signatureReady regs W bits (row::rows) key).regs W bits row rows key
        (hlen row (by simp))
      obtain ⟨u,hu,rf,hf⟩ := ih rm (Encoding.frame (rowKey W bits row)++key)
        (fun r hr => hlen r (by simp [hr]))
      have hg : (signatureReady regs W bits (row::rows) key).regs 1=true := by
        cases hr : words row <;> simp [signatureReady,signatureState,words,readRegs,
          Encoding.frame,hr]
      have h := Eval.while_true hg (he.seq (signaturePeek_eval rm W bits rows _)) hf
      refine ⟨(t+1)+u+1,?_,rf,?_⟩
      · simp only [signatureCost,List.map_cons,List.sum_cons] at *
        omega
      · simpa [signatureLoop, signatureBody, signatureValue, List.reverse_cons,
          words_append, words, List.append_assoc] using h

theorem signatureCommand_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row∈rows, row.length=bits.length) :
    ∃ t ≤ signatureCost W bits rows+1, ∃ rf,
      Eval signatureCommand t (signatureState regs W bits rows key)
        (signatureState rf W bits [] (signatureValue W bits rows++key)) := by
  obtain ⟨t,ht,rf,he⟩ := signatureLoop_eval regs W bits rows key hlen
  exact ⟨1+t,by omega,rf,(signaturePeek_eval regs W bits rows key).seq he⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem command_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows, ∃ out,
      Eval command n (state regs W bits rows key)
        (state out W bits rows (signatureValue W bits rows ++ key)) := by
  let a := state regs W bits rows key
  obtain ⟨b, hb, hbs⟩ := copy_eval (15 : Fin 16) 13 11
    (by decide) (by decide) (by decide) a rfl
  have hproj : projectState id signaturePorts b = signatureState b.regs W bits rows key := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    fin_cases i <;> simp [signaturePorts, hbs, a, state,
      StackRoutines.copyStacks]
  obtain ⟨ns, hns, out, he⟩ := signatureCommand_eval b.regs W bits rows key hlen
  rw [← hproj] at he
  have hc := eval_call_from_state signatureProgram id signaturePorts b
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 13 14)
  have hembed : embedState id signaturePorts b
      (signatureState out W bits [] (signatureValue W bits rows ++ key)) =
      state out W bits rows (signatureValue W bits rows ++ key) := by
    apply embedState_eq_of_ports id signaturePorts b _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      fin_cases i <;> simp [signaturePorts, state, signatureState, words]
    · intro i hi
      have hi15 : i = 15 := by
        apply Fin.ext
        by_contra hn
        have hil : i.val < 15 := by have := i.isLt; omega
        exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
      subst i
      simp [hbs, a, state, StackRoutines.copyStacks]
  rw [hembed] at hc
  exact ⟨_, by dsimp [cost, a, state] at *; omega, out, hb.seq hc⟩

theorem program_runs (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool)))
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Trace program n ((state regs W bits rows []).withPC (some program.entry))
        ((state out W bits rows (signatureValue W bits rows)).withPC none) := by
  obtain ⟨n, hn, out, he⟩ := command_eval regs W bits rows [] hlen
  simp only [List.append_nil] at he
  exact ⟨n + 1, Nat.add_le_add_right hn 1, out, compiled_halt_trace he 12 14⟩

theorem state_stackBits (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) :
    stackBits (state regs W bits rows []).stacks =
      W.length + bits.length + (words (rows.map words)).length := by
  simp [stackBits, state, Fin.sum_univ_succ, Nat.add_assoc]

/-- A complete per-key execution has polynomial local time. This estimate is
applied to that invocation only, never to the exponential outer traversal. -/
theorem prefix_stack_bound {labels : ℕ} (p : Program 8 16 labels)
    (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) {steps : ℕ} {intermediate : Cfg 8 16 labels}
    (hle : steps ≤ cost W bits rows + 1)
    (htrace : Trace p steps
      ((state regs W bits rows []).withPC (some p.entry)) intermediate)
    (i : Fin 16) :
    (intermediate.stacks i).length ≤
      16 * (W.length + bits.length + (words (rows.map words)).length) +
        cost W bits rows + 1 := by
  apply StructuredSpace.local_stack_bound p (steps := cost W bits rows + 1)
    (initialBound := 16 * (W.length + bits.length + (words (rows.map words)).length))
    _ steps intermediate hle htrace i
  change stackBits (state regs W bits rows []).stacks ≤ _
  rw [state_stackBits]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem Ready.projection {a : State 40 896} {W bits : List Bool}
    {rows : List (List (List Bool))} (ready : Ready a W bits rows) :
    projectState registers stackPorts a = state (a.regs ∘ registers) W bits rows [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change a.stacks (stackPorts i) = _
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h12 : i = 12
  · subst i; exact ready.assignment
  by_cases h14 : i = 14
  · subst i; exact ready.output
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  rw [ready.scratch i h0 h12 h14 h15]
  fin_cases i <;> simp_all

/-- The complete key computation and its all-stack prefix bound concern one
actual run, including its compiled return instruction and all caller words. -/
theorem run_oai (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) (ready : Ready a W bits rows)
    (hlen : ∀ row ∈ rows, row.length = bits.length) (frameBound : ℕ)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Eval command n a (outputState a out W bits rows) ∧
      Trace machine n (a.withPC (some machine.entry))
        ((outputState a out W bits rows).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace machine prefixSteps (a.withPC (some machine.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (16 * (W.length + bits.length + (words (rows.map words)).length) +
            cost W bits rows + 1) frameBound := by
  obtain ⟨n, hn, out, ht⟩ := program_runs (a.regs ∘ registers) W bits rows hlen
  have he := ht
  rw [← ready.projection] at he
  have heval := eval_call_from_state AttainedSignatureProgram.program registers stackPorts a
    registers.injective stackPorts.injective he
  have hi : embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows []) = a := by
    rw [← ready.projection, embedState_project registers stackPorts a registers.injective stackPorts.injective]
  have htrace := ProgramLinking.liftProgram_trace AttainedSignatureProgram.program
    registers stackPorts (a.withPC none) registers.injective stackPorts.injective ht
  have htrace' : Trace machine n (a.withPC (some machine.entry))
      ((outputState a out W bits rows).withPC none) := by
    change Trace machine n
      ((embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).withPC
        (some machine.entry)) ((outputState a out W bits rows).withPC none) at htrace
    rw [hi] at htrace
    exact htrace
  refine ⟨n, hn, out, heval, htrace', ?_⟩
  have hlocal : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace AttainedSignatureProgram.program prefixSteps
        ((state (a.regs ∘ registers) W bits rows []).withPC
          (some AttainedSignatureProgram.program.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        16 * (W.length + bits.length + (words (rows.map words)).length) +
          cost W bits rows + 1 := by
    intro prefixSteps intermediate hle hp i
    exact prefix_stack_bound _ _ _ _ _ (hle.trans hn) hp i
  have hb := StructuredSpace.liftProgram_stack_bound AttainedSignatureProgram.program
    registers stackPorts (a.withPC none) registers.injective stackPorts.injective ht hlocal hframe
  change ∀ prefixSteps intermediate, prefixSteps ≤ n →
    Trace machine prefixSteps
      ((embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).withPC
        (some machine.entry)) intermediate → ∀ i, (intermediate.stacks i).length ≤
      max (16 * (W.length + bits.length + (words (rows.map words)).length) +
        cost W bits rows + 1) frameBound at hb
  rw [hi] at hb
  exact hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run_oai

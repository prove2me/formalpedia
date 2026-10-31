-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:15:41.988814+00:00
-- url     : https://prove2.me/submissions/fa3d9cc0-5611-45c2-8194-9b1912c9dceb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

theorem increment_eval {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace true (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

namespace KeyEquality

open OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

theorem command_eval (regs : Fin 5 → Bool) (left right frame : List Bool) :
    ∃ n ≤ 18 * left.length + 9 * right.length + 25, ∃ out,
      Eval command n (recordState regs left [] right [] [] frame)
        (recordState out left [] right [] [] frame) ∧
      out 4 = decide (left = right) := by
  let r₁ := readRegs regs 0 1 none
  let r₂ := readRegs r₁ 0 1 none
  have h₁ : Eval (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 5) 1))
      (7 * left.length + 5)
      (recordState regs left [] right [] [] frame)
      (recordState r₁ left left right [] [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₁] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState regs left [] right [] [] frame)
        0 1 4 (by decide) (by decide) (by decide) rfl
  have h₂ : Eval (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (7 * right.length + 5)
      (recordState r₁ left left right [] [] frame)
      (recordState r₂ left left right right [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₂] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState r₁ left left right [] [] frame)
        2 3 4 (by decide) (by decide) (by decide) rfl
  obtain ⟨nc, hnc, rc, left', right', hc, hanswer, hl, hr⟩ :=
    compareKeys_eval r₂ left left right right [] frame
  let r₃ := readRegs rc 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have h₃ : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * left'.length + 3)
      (recordState rc left left' right right' [] frame)
      (recordState r₃ left [] right right' [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₃] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState rc left left' right right' [] frame) 1
  have h₄ : Eval (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))
      (2 * right'.length + 3)
      (recordState r₃ left [] right right' [] frame)
      (recordState r₄ left [] right [] [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₄] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState r₃ left [] right right' [] frame) 3
  refine ⟨_, by omega, r₄, h₁.seq (h₂.seq (hc.seq (h₃.seq h₄))), ?_⟩
  first | (simpa [r₄, r₃, readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hanswer) | (simpa [r₄, r₃, readRegs] using hanswer)

end KeyEquality

namespace Rescan

theorem keyCall_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool)
    (hlen : ∀ row ∈ rows, row.length = bits.length) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Eval keyCall n (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel fresh bits
          (signatureValue W bits rows ++ key)) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  have hr : Function.Injective signatureRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective signatureStacks := Fin.castAdd_injective _ _
  have hp : projectState signatureRegisters signatureStacks a =
      AttainedSignatureProgram.state (regs ∘ signatureRegisters) W bits rows key := by
    apply congrArg (StructuredProgram.State.mk _)
    first | done | (funext i; fin_cases i <;> rfl)
  obtain ⟨n, hn, out, he⟩ := AttainedSignatureProgram.command_eval
    (regs ∘ signatureRegisters) W bits rows key hlen
  rw [← hp] at he
  have hc := eval_call_from_state AttainedSignatureProgram.program
    signatureRegisters signatureStacks a hr hs (compiled_halt_trace he 12 14)
  let e := embedState signatureRegisters signatureStacks a
    (AttainedSignatureProgram.state out W bits rows (signatureValue W bits rows ++ key))
  have heq : e = workState e.regs W rows candidate saved predecessor fuel fresh bits
      (signatureValue W bits rows ++ key) := by
    apply embedState_eq_of_ports signatureRegisters signatureStacks a _ _ hr hs
    · intro i
      exact embedState_register signatureRegisters signatureStacks a _ hr i
    · intro i hi
      exact embedState_register_frame signatureRegisters signatureStacks a _ i hi
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      have hil : 16 ≤ i.val := by
        by_contra h
        exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      fin_cases i <;> simp_all [workState, a]
  change Eval keyCall (n + 1) a e at hc
  rw [heq] at hc
  exact ⟨n + 1, Nat.add_le_add_right hn 1, e.regs, hc⟩

theorem equalityCall_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ n ≤ 18 * key.length + 9 * saved.length + 26, ∃ out,
      Eval equalityCall n (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel fresh bits key) ∧
      out 4 = decide (key = saved) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  have hr : Function.Injective equalityRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective equalityStacks := by decide
  have hp : projectState equalityRegisters equalityStacks a =
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ equalityRegisters) key [] saved [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    first | done | (funext i; fin_cases i <;> rfl)
  obtain ⟨n, hn, out, he, hanswer⟩ := KeyEquality.command_eval
    (regs ∘ equalityRegisters) key saved []
  rw [← hp] at he
  have hc := eval_call_from_state KeyEquality.program equalityRegisters equalityStacks a hr hs
    (compiled_halt_trace he 0 0)
  let e := embedState equalityRegisters equalityStacks a
    (OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState out key [] saved [] [] [])
  have heq : e = workState e.regs W rows candidate saved predecessor fuel fresh bits key := by
    apply embedState_eq_of_ports equalityRegisters equalityStacks a _ _ hr hs
    · intro i
      exact embedState_register equalityRegisters equalityStacks a _ hr i
    · intro i hi
      exact embedState_register_frame equalityRegisters equalityStacks a _ i hi
    · intro i
      fin_cases i <;> rfl
    · intro i _
      rfl
  have ha : e.regs 4 = decide (key = saved) := by
    change e.regs (equalityRegisters 4) = _
    rw [embedState_register equalityRegisters equalityStacks a _ hr]
    exact hanswer
  change Eval equalityCall (n + 1) a e at hc
  rw [heq] at hc
  exact ⟨n + 1, by omega, e.regs, hc, ha⟩

theorem clear_eval (i : Fin 24) (a : Data) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks i a.stacks⟩ :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem copy_eval (i j : Fin 24) (a : Data)
    (hij : i ≠ j) (hi : i ≠ 21) (hj : (21 : Fin 24) ≠ j)
    (ht : a.stacks 21 = []) :
    Eval (copy i j) (7 * (a.stacks i).length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks i j a.stacks⟩ :=
  .call _ (ListRegisterProgram.copy_run i j 21 0 1 hij hi hj (by decide)
    a.regs a.stacks ht)

theorem storeFresh_eval (b : Bool) (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ out, Eval (storeFresh b) 7
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel b bits key) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  let c : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 22 a.stacks⟩
  let d := (StructuredProgram.Atom.set (0 : Fin 16) b).eval c
  let e := (StructuredProgram.Atom.push (22 : Fin 24) (0 : Fin 16)).eval d
  have hc : Eval (clear 22) 5 a c := clear_eval 22 a
  have he : Eval (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0)))) 2 c e :=
    .base ((StructuredProgram.Eval.atom _ c).seq (StructuredProgram.Eval.atom _ d))
  have hf : e = workState e.regs W rows candidate saved predecessor fuel b bits key := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [d, c, a, workState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  refine ⟨e.regs, ?_⟩
  have ht := hc.seq he
  rw [hf] at ht
  exact ht

theorem updateFresh_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ n ≤ 8, ∃ out, Eval updateFresh n
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel (fresh && !(regs 4)) bits key) := by
  cases hf : regs 4 with
  | false =>
    exact ⟨1, by omega, regs, by
      simpa [updateFresh, hf] using (Eval.ite_false hf (.base (.skip _)) :
        Eval updateFresh 1
          (workState regs W rows candidate saved predecessor fuel fresh bits key)
          (workState regs W rows candidate saved predecessor fuel fresh bits key))⟩
  | true =>
    obtain ⟨out, he⟩ := storeFresh_eval false regs W rows candidate saved predecessor fuel fresh bits key
    exact ⟨8, le_rfl, out, by simpa [updateFresh, hf] using (Eval.ite_true hf he :
      Eval updateFresh 8
        (workState regs W rows candidate saved predecessor fuel fresh bits key)
        (workState out W rows candidate saved predecessor fuel false bits key))⟩

theorem body_eval_oai (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (hlen : ∀ row ∈ rows, row.length = predecessor.length) :
    ∃ n ≤ bodyCost W predecessor saved rows, ∃ out,
      Eval body n (workState regs W rows candidate saved predecessor fuel fresh [] [])
        (workState out W rows candidate saved (CounterPrograms.ripple true predecessor) fuel
          (fresh && !decide (signatureValue W predecessor rows = saved)) [] []) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 18 12) (7 * predecessor.length + 5) a
      (workState r₁ W rows candidate saved predecessor fuel fresh predecessor []) := by
    have ht := copy_eval 18 12 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 18 12 a.stacks⟩ : Data) =
        workState r₁ W rows candidate saved predecessor fuel fresh predecessor [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨nk, hnk, rk, hk⟩ := keyCall_eval r₁ W rows candidate saved predecessor fuel
    fresh predecessor [] hlen
  simp only [List.append_nil] at hk
  obtain ⟨ne, hne, re, he, hanswer⟩ := equalityCall_eval rk W rows candidate saved predecessor fuel
    fresh predecessor (signatureValue W predecessor rows)
  obtain ⟨nf, hnf, rf, hf⟩ := updateFresh_eval re W rows candidate saved predecessor fuel
    fresh predecessor (signatureValue W predecessor rows)
  rw [hanswer] at hf
  let fresh' := fresh && !decide (signatureValue W predecessor rows = saved)
  let r₂ := readRegs rf 0 1 none
  have hclearBits : Eval (clear 12) (2 * predecessor.length + 3)
      (workState rf W rows candidate saved predecessor fuel fresh' predecessor
        (signatureValue W predecessor rows))
      (workState r₂ W rows candidate saved predecessor fuel fresh' []
        (signatureValue W predecessor rows)) := by
    have ht := clear_eval 12 (workState rf W rows candidate saved predecessor fuel fresh'
      predecessor (signatureValue W predecessor rows))
    have hs : StackRoutines.clearStacks 12
        (workState rf W rows candidate saved predecessor fuel fresh' predecessor
          (signatureValue W predecessor rows)).stacks =
        (workState r₂ W rows candidate saved predecessor fuel fresh' []
          (signatureValue W predecessor rows)).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [hs] at ht
    exact ht
  let r₃ := readRegs r₂ 0 1 none
  have hclearKey : Eval (clear 14) (2 * (signatureValue W predecessor rows).length + 3)
      (workState r₂ W rows candidate saved predecessor fuel fresh' []
        (signatureValue W predecessor rows))
      (workState r₃ W rows candidate saved predecessor fuel fresh' [] []) := by
    have ht := clear_eval 14 (workState r₂ W rows candidate saved predecessor fuel fresh' []
      (signatureValue W predecessor rows))
    have hs : StackRoutines.clearStacks 14
        (workState r₂ W rows candidate saved predecessor fuel fresh' []
          (signatureValue W predecessor rows)).stacks =
        (workState r₃ W rows candidate saved predecessor fuel fresh' [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [hs] at ht
    exact ht
  let b := workState r₃ W rows candidate saved predecessor fuel fresh' [] []
  let e := Counters.incrementResult predecessorPorts b
  have hincr := Counters.increment_eval predecessorPorts b (by rfl)
  have heq : e = workState e.regs W rows candidate saved
      (CounterPrograms.ripple true predecessor) fuel fresh' [] [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    exact (Counters.incrementResult_stacks predecessorPorts b (by rfl)).trans (by
      funext i
      fin_cases i <;> simp [b, workState, predecessorPorts])
  change Eval (Counters.incrementCmd predecessorPorts)
    (CounterPrograms.rippleCost true predecessor + 1) b e at hincr
  rw [heq] at hincr
  refine ⟨_, ?_, e.regs, hcopy.seq (hk.seq (he.seq (hf.seq
    (hclearBits.seq (hclearKey.seq hincr)))))⟩
  dsimp [bodyCost]
  omega

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval_oai

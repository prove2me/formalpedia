-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:07:14.031789+00:00
-- url     : https://prove2.me/submissions/0aeeae71-c7b8-4593-a900-fbd7deb5f06b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port binary argmin calls and a parser for unevaluated candidate
payloads. The scores are absent from the input encoding. All supplied commands
are actual finite programs; semantic scores are never atomic instructions. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem parser_cons (bits : List Bool) (rest : List (List Bool))
    (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = true ∧
      Eval parserCmd (6 * bits.length + 6)
        (BinaryArgmin.data regs BinaryArgmin.empty best (candidateEncoding (bits :: rest)))
        (BinaryArgmin.data regs' ⟨bits, []⟩ best (candidateEncoding rest)) := by
  let d := BinaryArgmin.data regs BinaryArgmin.empty best (candidateEncoding (bits :: rest))
  let a := (StructuredProgram.Atom.pop 8 7 6).eval d
  have ht : a.regs 7 = true := by
    simp [a, d, BinaryArgmin.data, BinaryArgmin.store, candidateEncoding,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs]
  have hs : a.stacks payloadPorts.source =
      Encoding.frame bits.reverse ++ candidateEncoding rest := by
    simp [a, d, BinaryArgmin.data, BinaryArgmin.store, candidateEncoding, payloadPorts,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have ho : a.stacks payloadPorts.payload = [] := rfl
  have hi := RecordPrograms.state_eq_self payloadPorts a (a.regs 0) (a.regs 1)
    (a.regs 7) _ [] rfl rfl rfl hs ho
  have hr := RecordPrograms.reader_eval payloadPorts a bits.reverse
    (candidateEncoding rest) [] (a.regs 0) (a.regs 1) (a.regs 7)
  rw [hi] at hr
  let b := RecordPrograms.state payloadPorts a false true (a.regs 7)
    (candidateEncoding rest) bits
  have hr' : Eval (RecordPrograms.reader payloadPorts) (6 * bits.length + 4) a b := by
    simpa [b] using hr
  have hb : b = BinaryArgmin.data b.regs ⟨bits, []⟩ best (candidateEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ a, d, payloadPorts,
        BinaryArgmin.data, BinaryArgmin.store, BinaryArgmin.empty,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  refine ⟨b.regs, ?_, ?_⟩
  · simpa [b, payloadPorts, RecordPrograms.state] using ht
  · rw [← hb]
    convert Eval.seq (Eval.base (StructuredProgram.Eval.atom (.pop 8 7 6) d))
      (Eval.ite_true ht hr') using 1 ; first | rfl | omega

theorem parse_cons {r s : ℕ} (p : Ports r s) (frame : State r s)
    (bits : List Bool) (rest : List (List Bool)) (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = true ∧
      Eval (parse p) (6 * bits.length + 7)
        (state p frame regs BinaryArgmin.empty best (candidateEncoding (bits :: rest)))
        (state p frame regs' ⟨bits, []⟩ best (candidateEncoding rest)) := by
  obtain ⟨regs', ht, he⟩ := parser_cons bits rest best regs
  refine ⟨regs', ht, ?_⟩
  convert eval_call_lifted parserProgram p.register p.stack frame
    p.register_injective p.stack_injective (compiled_halt_trace he 8 0) using 1 <;>
    first | rfl

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

theorem chunks_shape {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).map List.length = List.replicate depth (digitWidth m) := by
  apply List.map_splitLengths_length
  simp [hraw, payloadWidth]

theorem chunks_width {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    ∀ word ∈ chunks m depth raw, word.length = digitWidth m := by
  intro word hw
  have hmem : word.length ∈ (chunks m depth raw).map List.length :=
    List.mem_map.mpr ⟨word, hw, rfl⟩
  rw [chunks_shape hraw] at hmem
  exact (List.mem_replicate.mp hmem).2

theorem chunks_flatten {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).flatten = raw.reverse := by
  apply List.flatten_splitLengths
  simp [hraw, payloadWidth]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
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

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

private theorem core_state (frameRegs regs : Fin 8 → Bool)
    (next best : BinaryArgmin.Entry) (queue counter : List Bool) :
    HashSelectProgram.state core (data frameRegs BinaryArgmin.empty BinaryArgmin.empty [] counter)
      regs next best queue = data regs next best queue counter := by
  unfold HashSelectProgram.state
  apply SubexpScanPrimitives.embedState_eq core.register core.stack
    core.register_injective core.stack_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have hj9 : 9 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 9 := by omega
      exact hj ⟨⟨j.val, hlt⟩, by apply Fin.ext; rfl⟩
    fin_cases j <;> simp_all [data]

theorem load_eval (regs : Fin 8 → Bool) (best : BinaryArgmin.Entry) (word : List Bool) :
    ∃ regs', Eval load (20 * word.length + 38)
      (data regs BinaryArgmin.empty best [] (Encoding.encodeList id [word]))
      (data regs' ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])) := by
  let counter := Encoding.encodeList id [word]
  let a := data regs BinaryArgmin.empty best [] counter
  let regs₁ := readRegs regs 0 1 none
  have hcopy := Subexp.TupleProgram.copy_eval (9 : Fin 11) 8 10 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a rfl
  have hcopyOut : (⟨readRegs a.regs 0 1 none,
      StackRoutines.copyStacks 9 8 a.stacks⟩ : State 8 11) =
      data regs₁ BinaryArgmin.empty best counter counter := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, data, StackRoutines.copyStacks]
  rw [hcopyOut] at hcopy
  have hqueue : counter = HashSelectProgram.candidateEncoding [word.reverse] := by
    simp [counter, HashSelectProgram.candidateEncoding, Encoding.encodeList]
  let frame := data regs BinaryArgmin.empty BinaryArgmin.empty [] counter
  obtain ⟨regs₂, _, hparse⟩ := HashSelectProgram.parse_cons core frame
    word.reverse [] best regs₁
  rw [core_state, core_state, ← hqueue] at hparse
  have hclear := Subexp.TupleProgram.clear_eval (8 : Fin 11) (0 : Fin 8) 1
    (data regs₂ ⟨word.reverse, []⟩ best [false] counter)
  have hclearOut : (⟨readRegs regs₂ 0 1 none,
      StackRoutines.clearStacks 8 (data regs₂ ⟨word.reverse, []⟩ best [false] counter).stacks⟩ :
      State 8 11) = data (readRegs regs₂ 0 1 none) ⟨word.reverse, []⟩ best [] counter := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [data, StackRoutines.clearStacks]
  change Eval _ 5 _ _ at hclear
  change Eval _ 5 _ (⟨readRegs regs₂ 0 1 none, _⟩ : State 8 11) at hclear
  rw [hclearOut] at hclear
  refine ⟨readRegs regs₂ 0 1 none, ?_⟩
  have hlen : counter.length = 2 * word.length + 3 := by
    simp [counter, Encoding.encodeList, Encoding.length_frame]
  have h := hcopy.seq (hparse.seq hclear)
  change Eval load (7 * counter.length + 5 + (6 * word.reverse.length + 7 + 5))
    (data regs BinaryArgmin.empty best [] counter)
    (data (readRegs regs₂ 0 1 none) ⟨word.reverse, []⟩ best [] counter) at h
  rw [List.length_reverse, hlen] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem load_trace (regs : Fin 8 → Bool) (best : BinaryArgmin.Entry) (word : List Bool) :
    ∃ regs', Trace loadProgram (20 * word.length + 39)
      ((data regs BinaryArgmin.empty best [] (Encoding.encodeList id [word])).withPC
        (some loadProgram.entry))
      ((data regs' ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])).withPC none) := by
  obtain ⟨regs', he⟩ := load_eval regs best word
  exact ⟨regs', by simpa [loadProgram, Nat.add_assoc] using compiled_halt_trace he 9 0⟩


/-- The existing fixed addition-and-reduction table also canonicalizes an
arbitrary word: its second summand is the empty representation of zero. -/
theorem normalize_digit_runs (regs : Fin 8 → Bool) (word modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ word.length) :
    ∃ rf, RunsIn ModularRingPrograms.wordAddProgram
      (1000 * (modulus.length + word.length + 1) ^ 2)
      ⟨some 0, regs, ModularRingPrograms.extendSeven
        (ModularRingPrograms.scalarInput word [] modulus) []⟩
      ⟨none, rf, ModularRingPrograms.extendSeven
        (ModularDivisionPrograms.resting
          (SubexpLiftRing.fixedBits word.length
            (BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus)) modulus []) []⟩ := by
  obtain ⟨r, output, hr, hlen, hv⟩ := ModularRingPrograms.addMod_value
    (readRegs regs 1 3 none) word [] modulus hm
  obtain ⟨rf, ht⟩ := ModularRingPrograms.canonical_execute
    ModularRingPrograms.addModProgram regs r word [] modulus output
    (600 * (modulus.length + word.length + 1) ^ 2) hr
  have hsmall : BinaryArithmetic.toNat output < 2 ^ word.length := by
    rw [hv]
    simpa using (Nat.mod_lt (BinaryArithmetic.toNat word) hm).trans_le hcapacity
  have hvalue : BinaryArithmetic.toNat (ModularArithmetic.padTo word output) =
      BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus := by
    rw [ModularRingPrograms.padTo_value_of_lt _ _ hsmall, hv]
    simp
  have hout : ModularArithmetic.padTo word output =
      SubexpLiftRing.fixedBits word.length
        (BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus) := by
    apply ExecCNFTupleEnumeration.word_eq_of_length_value
    · simp [ModularArithmetic.padTo_length]
    · rw [CounterPrograms.value_eq_toNat, CounterPrograms.value_eq_toNat, hvalue,
        SubexpLiftRing.toNat_fixedBits_of_lt _ _ ((Nat.mod_lt _ hm).trans_le hcapacity)]
  rw [hout] at ht
  refine ⟨rf, ht.mono ?_⟩
  simp only [List.length_nil, Nat.add_zero] at hlen ⊢
  have hsq : modulus.length + word.length + 1 ≤
      (modulus.length + word.length + 1) ^ 2 := by
    nlinarith
  nlinarith

namespace Normalize

open OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

private theorem embed_arithmetic (regs rf : Fin 8 → Bool)
    (chunk modulus unread result : List Bool) :
    embedState id arithmeticPorts (state regs [] modulus unread result)
      ⟨rf, ModularRingPrograms.extendSeven
        (ModularDivisionPrograms.resting chunk modulus []) []⟩ =
      state rf chunk modulus unread result := by
  apply SubexpScanPrimitives.embedState_eq id arithmeticPorts
    Function.injective_id (Fin.castAdd_injective 8 4)
  · intros; rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have hj8 : 8 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 8 := by omega
      exact hj ⟨⟨j.val, hlt⟩, by apply Fin.ext; rfl⟩
    fin_cases j <;> simp_all [state]

theorem digit_eval (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ chunk.length) :
    ∃ t ≤ 1000 * (modulus.length + chunk.length + 1) ^ 2, ∃ rf,
      Eval digit t (state regs chunk modulus unread result)
        (state rf (SubexpLiftRing.fixedBits chunk.length
          (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus))
          modulus unread result) := by
  obtain ⟨rf, t, ht, he⟩ := normalize_digit_runs regs chunk modulus hm hcapacity
  have h := eval_call_lifted ModularRingPrograms.wordAddProgram id arithmeticPorts
    (state regs [] modulus unread result) Function.injective_id
    (Fin.castAdd_injective 8 4)
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput chunk [] modulus) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularDivisionPrograms.resting (SubexpLiftRing.fixedBits chunk.length
        (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus)) modulus []) []⟩) he
  have hin : ModularRingPrograms.scalarInput chunk [] modulus =
      ModularDivisionPrograms.resting chunk modulus [] := rfl
  simp only [hin] at h
  rw [embed_arithmetic, embed_arithmetic] at h
  exact ⟨t, ht, rf, h⟩

theorem take_eval (regs : Fin 8 → Bool) (chunk rest modulus result : List Bool)
    (hw : modulus.length = chunk.length) :
    Eval take (14 * chunk.length + 11)
      (state regs [] modulus (chunk ++ rest) result)
      (state (readRegs regs 0 1 none) chunk modulus rest result) := by
  have h := takeWord_eval (state regs [] modulus (chunk ++ rest) result)
    5 10 11 8 0 0 1 (by decide) (by decide) chunk rest rfl rfl rfl hw
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state]

theorem emit_eval (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool) :
    Eval emit (3 * chunk.length + 3) (state regs chunk modulus unread result)
      (state (readRegs regs 0 1 none) [] modulus unread (chunk.reverse ++ result)) := by
  have h := SubexpScanPrimitives.transfer_eval
    (state regs chunk modulus unread result) 0 9 0 1 (by decide) (by decide)
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.transferStacks]

theorem step_eval (regs : Fin 8 → Bool) (chunk rest modulus result : List Bool)
    (hw : modulus.length = chunk.length) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ chunk.length) :
    ∃ t ≤ 5000 * (modulus.length + 1) ^ 2, ∃ rf,
      Eval step t (state regs [] modulus (chunk ++ rest) result)
        (state rf [] modulus rest ((canonicalDigit modulus chunk).reverse ++ result)) := by
  have htake := take_eval regs chunk rest modulus result hw
  obtain ⟨t, ht, rf, hdigit⟩ := digit_eval (readRegs regs 0 1 none)
    chunk modulus rest result hm hcapacity
  have hemit := emit_eval rf (canonicalDigit modulus chunk) modulus rest result
  refine ⟨_, ?_, readRegs rf 0 1 none, htake.seq (hdigit.seq hemit)⟩
  simp only [canonicalDigit, SubexpLiftRing.fixedBits_length]
  rw [← hw] at ht ⊢
  nlinarith


theorem probe_eval (regs : Fin 8 → Bool) (modulus unread result : List Bool) :
    Eval probe 1 (state regs [] modulus unread result)
      (state (readRegs regs 0 1 unread.head?) [] modulus unread result) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (r := 8) (s := 12) 8 0 1)
    (state regs [] modulus unread result))
  exact h

theorem loop_eval (modulus : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus)
    (words : List (List Bool)) (hw : ∀ word ∈ words, word.length = modulus.length)
    (regs : Fin 8 → Bool) (result : List Bool)
    (hf : regs 1 = words.flatten.head?.isSome) :
    ∃ t ≤ words.length * (5000 * (modulus.length + 1) ^ 2 + 4) + 1,
      ∃ rf, Eval loop t (state regs [] modulus words.flatten result)
        (state rf [] modulus [] ((words.map (canonicalDigit modulus)).flatten.reverse ++ result)) := by
  have hwpos : 0 < modulus.length := by
    cases modulus with
    | nil => simp [BinaryArithmetic.toNat] at hm
    | cons b bs => simp
  induction words generalizing regs result with
  | nil =>
    exact ⟨1, by simp, regs, by simpa [loop] using
      (Eval.while_false (by simpa [state] using hf) :
        Eval (.while 1 (.seq step probe)) 1 (state regs [] modulus [] result)
          (state regs [] modulus [] result))⟩
  | cons word words ih =>
    have hword := hw word (by simp)
    have hwords : ∀ word ∈ words, word.length = modulus.length :=
      fun word h => hw word (by simp [h])
    have hwne : word ≠ [] := by intro hz; simp [hz] at hword; omega
    have hflag : regs 1 = true := by
      rw [hf]
      cases word with
      | nil => contradiction
      | cons bit rest => rfl
    have hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ word.length := by
      rw [hword]
      exact (ModularArithmetic.toNat_lt_pow_length modulus).le
    obtain ⟨a, ha, ra, he⟩ := step_eval regs word words.flatten modulus result
      hword.symm hm hcapacity
    let nextResult := (canonicalDigit modulus word).reverse ++ result
    have hp := probe_eval ra modulus words.flatten nextResult
    obtain ⟨b, hb, rb, ht⟩ := ih hwords
      (readRegs ra 0 1 words.flatten.head?) nextResult (by simp [readRegs])
    refine ⟨a + 1 + b + 1, ?_, rb, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have h := Eval.while_true hflag (he.seq hp) ht
      simpa [loop, state, nextResult, List.flatten_cons, List.reverse_append,
        List.append_assoc] using h

theorem command_eval (modulus : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus)
    (words : List (List Bool)) (hw : ∀ word ∈ words, word.length = modulus.length)
    (regs : Fin 8 → Bool) (result : List Bool) :
    ∃ t ≤ words.length * (5000 * (modulus.length + 1) ^ 2 + 4) + 4,
      ∃ rf, Eval command t (state regs [] modulus words.flatten result)
        (state rf [] modulus [] ((words.map (canonicalDigit modulus)).flatten.reverse ++ result)) := by
  have hp := probe_eval regs modulus words.flatten result
  obtain ⟨t, ht, rf, he⟩ := loop_eval modulus hm words hw
    (readRegs regs 0 1 words.flatten.head?) result (by simp [readRegs])
  exact ⟨1 + t, by omega, rf, hp.seq he⟩



theorem prepare_eval (regs : Fin 8 → Bool) (modulus raw : List Bool) :
    Eval prepare (9 * raw.length + 7)
      (state regs [] modulus raw [])
      (state (readRegs regs 0 1 none) [] modulus raw.reverse []) := by
  have h := SubexpScanPrimitives.reverse_eval (state regs [] modulus raw [])
    8 0 1 0 1 (by decide) (by decide) (by decide) (by decide) rfl rfl
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.reverseStacks]

/-- Complete current-candidate canonicalization. The modulus and all digits
are ordinary bit words; scalar division, truncation and copies are charged. -/
theorem normalize_eval {m depth : ℕ} (hm : 0 < m) (regs : Fin 8 → Bool)
    (raw modulus : List Bool) (hraw : raw.length = HashCandidates.payloadWidth m depth)
    (hwidth : modulus.length = HashCandidates.digitWidth m)
    (hmodulus : BinaryArithmetic.toNat modulus = 3 * m) :
    ∃ t ≤ budget m depth, ∃ rf,
      Eval normalize t (state regs [] modulus raw [])
        (state rf [] modulus [] (HashCandidates.normalize m depth raw)) := by
  let words := HashCandidates.chunks m depth raw
  have hwords : ∀ word ∈ words, word.length = modulus.length := by
    intro word hw
    exact (HashCandidates.chunks_width hraw word hw).trans hwidth.symm
  have hpositive : 0 < BinaryArithmetic.toNat modulus := by rw [hmodulus]; omega
  obtain ⟨t, ht, rf, he⟩ := command_eval modulus hpositive words hwords
    (readRegs regs 0 1 none) []
  have hflat : words.flatten = raw.reverse := HashCandidates.chunks_flatten hraw
  have hout : (words.map (canonicalDigit modulus)).flatten.reverse =
      HashCandidates.normalize m depth raw := by
    unfold HashCandidates.normalize
    congr 2
    apply List.map_congr_left
    intro word hw
    simp only [canonicalDigit, hmodulus, HashCandidates.chunks_width hraw word hw]
  rw [hflat, List.append_nil, hout] at he
  refine ⟨9 * raw.length + 7 + t, ?_, rf, (prepare_eval regs modulus raw).seq he⟩
  rw [hraw]
  simp only [words, HashCandidates.chunks_length, hwidth] at ht
  unfold budget
  omega

theorem program_runs {m depth : ℕ} (hm : 0 < m) (regs : Fin 8 → Bool)
    (raw modulus : List Bool) (hraw : raw.length = HashCandidates.payloadWidth m depth)
    (hwidth : modulus.length = HashCandidates.digitWidth m)
    (hmodulus : BinaryArithmetic.toNat modulus = 3 * m) :
    ∃ rf, RunsIn program (budget m depth + 1)
      ((state regs [] modulus raw []).withPC (some program.entry))
      ((state rf [] modulus [] (HashCandidates.normalize m depth raw)).withPC none) := by
  obtain ⟨t, ht, rf, he⟩ := normalize_eval hm regs raw modulus hraw hwidth hmodulus
  exact ⟨rf, t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 8 9⟩


end Normalize

namespace Leaf

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open scoped BigOperators

/-- Loading changes just the candidate payload port, with all other leaf
stacks retained. The parser's bounded singleton queue is cleared. -/
theorem loader_eval (a : Data) (word : List Bool)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = []) :
    ∃ b, Eval loader (20 * word.length + 39) a b ∧
      b.stacks = Function.update a.stacks 768 word.reverse := by
  have hc0 := hclean 0 (by decide) (by decide) (by decide)
  have hc1 := hclean 1 (by decide) (by decide) (by decide)
  have hc4 := hclean 4 (by decide) (by decide) (by decide)
  have hc5 := hclean 5 (by decide) (by decide) (by decide)
  have hc6 := hclean 6 (by decide) (by decide) (by decide)
  have hc7 := hclean 7 (by decide) (by decide) (by decide)
  have hc8 := hclean 8 (by decide) (by decide) (by decide)
  have hc10 := hclean 10 (by decide) (by decide) (by decide)
  simp [loaderStacks] at hc0 hc1 hc4 hc5 hc6 hc7 hc8 hc10
  let d := projectState registers loaderStacks a
  let best : BinaryArgmin.Entry := ⟨a.stacks 770, a.stacks 771⟩
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective loaderStacks := by decide
  have hd : d = data d.regs BinaryArgmin.empty best [] (Encoding.encodeList id [word]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [best, loaderStacks,
        BinaryArgmin.empty, hcounter, hc0, hc1, hc4, hc5, hc6, hc7, hc8, hc10]
  obtain ⟨rf, ht⟩ := load_trace d.regs best word
  rw [← hd] at ht
  let out := data rf ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])
  refine ⟨embedState registers loaderStacks a out,
    eval_call_from_state loadProgram registers loaderStacks a hr hs ht, ?_⟩
  have hout : out.stacks = Function.update d.stacks 0 word.reverse := by
    funext j
    fin_cases j <;> simp [out, d, projectState, data, best, loaderStacks,
      hcounter, hc1, hc4, hc5, hc6, hc7, hc8, hc10]
  change Function.extend loaderStacks out.stacks a.stacks = _
  rw [hout, ProgramLinking.extend_update hs]
  have hf : Function.extend loaderStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers loaderStacks a hr hs)
  rw [hf]
  rfl

theorem mem_lowPorts (j : Fin 896) : j ∈ lowPorts ↔ j.val < 12 := by
  simp only [lowPorts, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  change (j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
    j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨
    j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11) ↔ j.val < 12
  omega

theorem normalizer_eval {m depth : ℕ} (hm : 0 < m) (a : Data)
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hraw : (a.stacks 768).length = HashCandidates.payloadWidth m depth)
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ Normalize.budget m depth +
        100 * ((a.stacks 768).length + (a.stacks 780).length + 1), ∃ b,
      Eval normalizer n a b ∧ b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth (a.stacks 768)) := by
  have hl0 := hlow 0 (by decide)
  have hl1 := hlow 1 (by decide)
  have hl2 := hlow 2 (by decide)
  have hl3 := hlow 3 (by decide)
  have hl4 := hlow 4 (by decide)
  have hl5 := hlow 5 (by decide)
  have hl6 := hlow 6 (by decide)
  have hl7 := hlow 7 (by decide)
  have hl8 := hlow 8 (by decide)
  have hl9 := hlow 9 (by decide)
  have hl10 := hlow 10 (by decide)
  have hl11 := hlow 11 (by decide)
  let raw := a.stacks 768
  let modulus := a.stacks 780
  let canon := HashCandidates.normalize m depth raw
  let a1 := routed (768,8) a
  let a2 := routed (780,5) a1
  have he1 := route_eval (768,8) (by unfold routeValid; decide) a ht
  have he2 := route_eval (780,5) (by unfold routeValid; decide) a1
    (by simp [a1, routed, ht])
  let d := projectState registers normalizerStacks a2
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective normalizerStacks := Fin.castAdd_injective 12 884
  have hd : d = Normalize.state d.regs [] modulus raw [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [normalizerStacks, a2, a1, routed, raw, modulus,
        hl0, hl1, hl2, hl3, hl4, hl6, hl7, hl9, hl10, hl11]
  obtain ⟨rf, q, hq, htq⟩ := Normalize.program_runs hm d.regs raw modulus hraw hwidth hvalue
  rw [← hd] at htq
  let out := Normalize.state rf [] modulus [] canon
  let a3 := embedState registers normalizerStacks a2 out
  have he3 : Eval (.call (ProgramLinking.liftProgram Normalize.program registers normalizerStacks))
      q a2 a3 := eval_call_from_state _ _ _ a2 hr hs htq
  have ha3 : a3.stacks = Function.update (Function.update a2.stacks 8 []) 9 canon := by
    have hout : out.stacks = Function.update (Function.update d.stacks 8 []) 9 canon := by
      funext j
      fin_cases j <;> simp [out, d, projectState, normalizerStacks, Normalize.state,
        a2, a1, routed, modulus, hl0, hl1, hl2, hl3, hl4, hl6, hl7,
        hl10, hl11]
    change Function.extend normalizerStacks out.stacks a2.stacks = _
    rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs]
    have hf : Function.extend normalizerStacks d.stacks a2.stacks = a2.stacks :=
      congrArg StructuredProgram.State.stacks (embedState_project registers normalizerStacks a2 hr hs)
    rw [hf]
    rfl
  let a4 := routed (9,768) a3
  have he4 := route_eval (9,768) (by unfold routeValid; decide) a3
    (by rw [ha3]; simp [a2, a1, routed, ht])
  have htemp : a4.stacks 767 = [] := by
    dsimp [a4, routed]
    rw [Function.update_of_ne (by decide : (767 : Fin 896) ≠ 768), ha3]
    simp [a2, a1, routed, ht]
  have he5 := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 lowPorts
    (by decide) a4.regs a4.stacks htemp
  have hfinal : BankRoutines.clearBankStacks lowPorts a4.stacks =
      Function.update a.stacks 768 canon := by
    funext j
    by_cases hj : j ∈ lowPorts
    · have hjv := (mem_lowPorts j).mp hj
      have hj768 : j ≠ 768 := by intro he; subst j; exact (by decide : ¬ (768 : Fin 896).val < 12) hjv
      simp [BankRoutines.clearBankStacks, hj, hj768, hlow j hjv]
    · have hj5 : j ≠ 5 := by intro he; subst j; exact hj (by decide)
      have hj8 : j ≠ 8 := by intro he; subst j; exact hj (by decide)
      have hj9 : j ≠ 9 := by intro he; subst j; exact hj (by decide)
      by_cases hj768 : j = 768
      · subst j
        simp [BankRoutines.clearBankStacks, hj, a4, routed, ha3]
      · simp [BankRoutines.clearBankStacks, hj, a4, routed, ha3, a2, a1,
          hj768, hj5, hj8, hj9]
  rw [hfinal] at he5
  have hsum : (lowPorts.map (fun j => (a4.stacks j).length)).sum = modulus.length + canon.length := by
    simp [lowPorts, a4, routed, ha3, a2, a1, raw, modulus,
      hl0, hl1, hl2, hl3, hl4, hl6, hl7, hl10, hl11, Nat.add_comm]
  have hcanon : canon.length = raw.length := by
    simp only [canon, HashCandidates.normalize_length, raw, hraw]
  refine ⟨routeCost (768,8) a + (routeCost (780,5) a1 +
    (q + (routeCost (9,768) a3 + (2 * (lowPorts.map (fun j => (a4.stacks j).length)).sum +
      3 * lowPorts.length + 3)))), ?_, _, he1.seq (he2.seq (he3.seq (he4.seq he5))), rfl⟩
  have hc1 : routeCost (768,8) a = 7 * raw.length + 8 := by
    simp [routeCost, raw, hl8]
  have hc2 : routeCost (780,5) a1 = 7 * modulus.length + 8 := by
    simp [routeCost, a1, routed, modulus, hl5]
  have hc4 : routeCost (9,768) a3 = 2 * raw.length + 7 * canon.length + 8 := by
    simp [routeCost, ha3, a2, a1, routed, raw]
  rw [hc1, hc2, hc4, hsum, hcanon]
  simp only [lowPorts, List.length_cons, List.length_nil]
  change _ ≤ Normalize.budget m depth + 100 * (raw.length + modulus.length + 1)
  omega

/-- The concrete preparation wrapper preserves every stack except the next
candidate payload; in particular incumbent, history, counter and parameters. -/
theorem prepare_eval_oai {m depth : ℕ} (hm : 0 < m) (a : Data) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ budget m depth, ∃ b, Eval prepare n a b ∧
      b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth word.reverse) := by
  obtain ⟨a1, he1, ha1⟩ := loader_eval a word hcounter hclean
  have hl : ∀ j : Fin 896, j.val < 12 → a1.stacks j = [] := by
    intro j hj
    have hj768 : j ≠ 768 := by intro he; subst j; exact (by decide : ¬ (768 : Fin 896).val < 12) hj
    simpa [ha1, hj768] using hlow j hj
  obtain ⟨n, hn, b, he2, hb⟩ := normalizer_eval (depth := depth) hm a1 hl
    (by simp [ha1, ht]) (by simp [ha1, hword])
    (by simpa [ha1] using hwidth) (by simpa [ha1] using hvalue)
  refine ⟨20 * word.length + 39 + n, ?_, b, he1.seq he2, ?_⟩
  · simp only [ha1, Function.update_self, List.length_reverse,
      Function.update_of_ne (by decide : (780 : Fin 896) ≠ 768), hwidth, hword] at hn ⊢
    unfold budget
    omega
  · simpa [ha1] using hb

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval_oai

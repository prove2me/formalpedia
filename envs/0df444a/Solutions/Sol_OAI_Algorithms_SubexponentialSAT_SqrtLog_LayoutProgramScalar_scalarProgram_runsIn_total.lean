-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:04:22.690257+00:00
-- url     : https://prove2.me/submissions/4e2c79e2-9478-4cb0-8e1a-4844e7fa5ec6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S080
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_accumulate_eval_total
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgramScalar_multiply_eval_total

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem atom_pop_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) [false])
        (streamData regs' acc ([],[]) []) := by
  let d := streamData regs acc ([],[]) [false]
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = false := by
    simp [a, d, streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs]
  have ha : a = streamData a.regs acc ([],[]) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ d, streamData, StructuredProgram.Atom.instr, execInstr]
  refine ⟨a.regs, hg, ?_⟩
  rw [← ha]
  exact (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
    (Eval.ite_false hg (.base (.skip a)))

theorem parsePair_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) (pairEncoding []))
        (streamData regs' acc ([],[]) []) := atom_pop_nil regs acc

theorem parsePair_cons (regs : Fin 8 → Bool) (acc next : WordPair) (rest : List WordPair) :
    ∃ regs', regs' 7 = true ∧
      Eval parsePair (6*pairLength next+10)
        (streamData regs acc ([],[]) (pairEncoding (next::rest)))
        (streamData regs' acc next (pairEncoding rest)) := by
  let d := streamData regs acc ([],[]) (pairEncoding (next::rest))
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = true := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have hs : a.stacks 15 = Encoding.frame next.1.reverse ++
      (Encoding.frame next.2.reverse ++ pairEncoding rest) := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have hp : a.stacks 2 = [] := rfl
  have hi := RecordPrograms.state_eq_self positiveReader a (a.regs 0) (a.regs 1)
    (a.regs 7) _ [] rfl rfl rfl hs hp
  have hr := RecordPrograms.reader_eval positiveReader a next.1.reverse
    (Encoding.frame next.2.reverse ++ pairEncoding rest) [] (a.regs 0) (a.regs 1) (a.regs 7)
  rw [hi] at hr
  let b := RecordPrograms.state positiveReader a false true (a.regs 7)
    (Encoding.frame next.2.reverse ++ pairEncoding rest) next.1
  have hr' : Eval (RecordPrograms.reader positiveReader) (6*next.1.length+4) a b := by
    simpa [b] using hr
  have hs2 : b.stacks 15 = Encoding.frame next.2.reverse ++ pairEncoding rest := by
    simp [b, positiveReader, RecordPrograms.state]
  have hn : b.stacks 3 = [] := by
    simp [b, a, d, positiveReader, RecordPrograms.state, streamData,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have hi2 := RecordPrograms.state_eq_self negativeReader b (b.regs 0) (b.regs 1)
    (b.regs 7) _ [] rfl rfl rfl hs2 hn
  have hr2 := RecordPrograms.reader_eval negativeReader b next.2.reverse
    (pairEncoding rest) [] (b.regs 0) (b.regs 1) (b.regs 7)
  rw [hi2] at hr2
  let c := RecordPrograms.state negativeReader b false true (b.regs 7)
    (pairEncoding rest) next.2
  have hr2' : Eval (RecordPrograms.reader negativeReader) (6*next.2.length+4) b c := by
    simpa [c] using hr2
  have hc : c = streamData c.regs acc next (pairEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ b, a, d, positiveReader, negativeReader, RecordPrograms.state,
          streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  refine ⟨c.regs, ?_, ?_⟩
  · simpa [c, b, negativeReader, positiveReader, RecordPrograms.state] using hg
  · rw [← hc]
    convert (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
      (Eval.ite_true (no := .base .skip) hg (hr'.seq hr2')) using 1 ;
      simp [ pairLength] ; omega

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem workPorts_injective : Function.Injective workPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 18 => k.val) h

theorem workCall_eval {c : Cmd 8 16} {t : ℕ}
    {regs regs' : Fin 8 → Bool} {work next work' next' : WordPair}
    {queue queue' : List Bool}
    (he : Eval c t (streamData regs work next queue)
      (streamData regs' work' next' queue')) (acc : WordPair) :
    Eval (workCall c) (t+1) (state regs acc work next queue)
      (state regs' acc work' next' queue') := by
  have emb (r : Fin 8 → Bool) (w n : WordPair) (q : List Bool) :
      embedState id workPorts (state regs acc work next queue)
        (streamData r w n q) = state r acc w n q := by
    apply embedState_eq_of_ports id workPorts _ _ _
      Function.injective_id workPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state, streamData, workPorts]
    · intro i hi
      have hv : 16 ≤ i.val := by
        by_contra h
        have hlt : i.val < 16 := by omega
        exact hi ⟨⟨i.val,hlt⟩, Fin.ext rfl⟩
      fin_cases i <;> simp_all [state]
  have h := eval_call_lifted (compiled c 0 1) id workPorts
    (state regs acc work next queue) Function.injective_id workPorts_injective
    (compiled_halt_trace he 0 1)
  simpa only [workCall, emb] using h

theorem parse_cons (regs : Fin 8 → Bool) (acc work next : WordPair)
    (rest : List WordPair) :
    ∃ r, r 7 = true ∧ Eval parse (6*pairLength next+11)
      (state regs acc work ([],[]) (pairEncoding (next::rest)))
      (state r acc work next (pairEncoding rest)) := by
  obtain ⟨r,hg,he⟩ := parsePair_cons regs work next rest
  exact ⟨r,hg,by simpa only [parse, Nat.add_assoc] using workCall_eval he acc⟩

theorem parse_nil (regs : Fin 8 → Bool) (acc work : WordPair) :
    ∃ r, r 7 = false ∧ Eval parse 3
      (state regs acc work ([],[]) (pairEncoding []))
      (state r acc work ([],[]) []) := by
  obtain ⟨r,hg,he⟩ := parsePair_nil regs work
  exact ⟨r,hg,workCall_eval he acc⟩

theorem initializeOne_eval (regs : Fin 8 → Bool) (acc next : WordPair)
    (queue : List Bool) :
    Eval initializeOne 2 (state regs acc ([],[]) next queue)
      (state (Function.update regs 0 true) acc one next queue) := by
  let r := Function.update regs 0 true
  have hs : Eval (.base (.atom (.set 0 true))) 1
      (state regs acc ([],[]) next queue) (state r acc ([],[]) next queue) :=
    .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 0 0))) 1
      (state r acc ([],[]) next queue) (state r acc one next queue) := by
    convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
      (.push (0 : Fin 18) (0 : Fin 8)) (state r acc ([],[]) next queue))) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [state,one,r,StructuredProgram.Atom.instr,execInstr]
  exact hs.seq hp

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open scoped BigOperators

theorem scalarCost_poly (n A B : ℕ) :
    scalarCost n A B ≤
      200000000*(n+1)*(A+n*termGrowth B+B+4)^2 := by
  induction n generalizing A with
  | zero =>
    simp only [scalarCost,Nat.zero_mul,Nat.add_zero,Nat.zero_add,Nat.mul_one]
    have h := Nat.pow_le_pow_left (show 4 ≤ A+B+4 by omega) 2
    norm_num at h
    omega
  | succ n ih =>
    let H := A+(n+1)*termGrowth B+B+4
    have htail := ih (A+termGrowth B)
    have hsame : A+termGrowth B+n*termGrowth B+B+4 = H := by dsimp [H]; ring
    rw [hsame] at htail
    have hbase : A+B+4 ≤ H := by dsimp [H]; omega
    have hs := Nat.pow_le_pow_left hbase 2
    have hh : 6*B+11+termCost A B+1 ≤ 200000000*H^2 := by
      dsimp [termCost]
      have hB : B+4 ≤ H := by omega
      have hHpos : 4 ≤ H := by omega
      have hlin : 6*B+12 ≤ 100000000*H^2 := by nlinarith only [hB,hHpos]
      have hmain := Nat.mul_le_mul_left 100000000 hs
      omega
    change 6*B+11+termCost A B+scalarCost n (A+termGrowth B) B+1 ≤
      200000000*(n+1+1)*H^2
    nlinarith only [hh,htail]

open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem termStep_eval_total (regs : Fin 8 → Bool) (acc x y z : WordPair)
    (rest : List WordPair) (A B : ℕ)
    (ha : pairLength acc ≤ A) (hx : pairLength x ≤ B)
    (hy : pairLength y ≤ B) (hz : pairLength z ≤ B) :
    ∃ t ≤ termCost A B, ∃ r result,
      Eval termStep t
        (state regs acc ([],[]) x (pairEncoding (y::z::rest)))
        (state r result ([],[]) ([],[]) (pairEncoding rest)) ∧
      pairValue result = pairValue acc + pairValue x*pairValue y*pairValue z ∧
      wordTotal result = wordTotal acc + wordTotal x*wordTotal y*wordTotal z ∧
      pairLength result ≤ A+termGrowth B := by
  have hi := initializeOne_eval regs acc x (pairEncoding (y::z::rest))
  obtain ⟨t₁,ht₁,r₁,w₁,he₁,hv₁,hm₁,hl₁⟩ := multiply_eval_total
    (Function.update regs 0 true) acc one x (pairEncoding (y::z::rest))
  obtain ⟨r₂,_,hp₂⟩ := parse_cons r₁ acc w₁ y (z::rest)
  obtain ⟨t₂,ht₂,r₃,w₂,he₂,hv₂,hm₂,hl₂⟩ := multiply_eval_total r₂ acc w₁ y
    (pairEncoding (z::rest))
  obtain ⟨r₄,_,hp₃⟩ := parse_cons r₃ acc w₂ z rest
  obtain ⟨t₃,ht₃,r₅,w₃,he₃,hv₃,hm₃,hl₃⟩ := multiply_eval_total r₄ acc w₂ z
    (pairEncoding rest)
  obtain ⟨t₄,ht₄,r₆,result,he₄,hv₄,hm₄,hl₄⟩ := accumulate_eval_total r₅ acc w₃
    (pairEncoding rest)
  have hw₁ : pairLength w₁ ≤ 2*B+8 := by simp only [one_length] at hl₁; omega
  have hw₂ : pairLength w₂ ≤ 6*B+22 := by omega
  have hw₃ : pairLength w₃ ≤ 14*B+50 := by omega
  refine ⟨2+(t₁+((6*pairLength y+11)+(t₂+((6*pairLength z+11)+(t₃+t₄))))),
    ?_,r₆,result,hi.seq (he₁.seq (hp₂.seq (he₂.seq (hp₃.seq (he₃.seq he₄))))),?_,?_,?_⟩
  · let H := A+14*B+53
    have h₁ : pairLength one+pairLength x+3 ≤ H := by simp only [one_length]; dsimp [H]; omega
    have h₂ : pairLength w₁+pairLength y+3 ≤ H := by dsimp [H]; omega
    have h₃ : pairLength w₂+pairLength z+3 ≤ H := by dsimp [H]; omega
    have h₄ : pairLength acc+pairLength w₃+3 ≤ H := by dsimp [H]; omega
    have ht₁' := ht₁.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₁ 2)) 2)
    have ht₂' := ht₂.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₂ 2)) 2)
    have ht₃' := ht₃.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₃ 2)) 2)
    have ht₄' := ht₄.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 25000 (Nat.pow_le_pow_left h₄ 2)) 2)
    have hH : H ≤ 14*(A+B+4) := by dsimp [H]; omega
    have hsq := Nat.pow_le_pow_left hH 2
    let M := A+B+4
    have hMB : B+4 ≤ M := by dsimp [M]; omega
    have hMpos : 4 ≤ M := by omega
    have hlin : 12*B+32 ≤ 100*M^2 := by nlinarith only [hMB,hMpos]
    have htime : 2+(t₁+((6*pairLength y+11)+(t₂+
        ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000*H^2+12*B+32 := by
      omega
    have hsq' : H^2 ≤ 196*M^2 := by
      calc
        H^2 ≤ (14*(A+B+4))^2 := hsq
        _ = 196*M^2 := by dsimp [M]; ring
    change 2+(t₁+((6*pairLength y+11)+(t₂+
      ((6*pairLength z+11)+(t₃+t₄))))) ≤ 100000000*M^2
    omega
  · rw [hv₄,hv₃,hv₂,hv₁,one_value,one_mul]
  · rw [hm₄,hm₃,hm₂,hm₁,one_total,one_mul]
  · dsimp [termGrowth]; omega

theorem scalarCommand_eval_total (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ t ≤ scalarCost xs.length A B, ∃ r result,
      r 7 = false ∧
      Eval scalarCommand t
        (state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs)))
        (state r result ([],[]) ([],[]) []) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  induction xs generalizing regs acc A with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc ([],[])
    refine ⟨4,le_rfl,r,acc,hg,he.seq (.while_false hg),?_,?_,?_⟩
    · simp
    · simp
    · simpa using ha
  | cons x xs ih =>
    have hb := hx x (by simp)
    have hxs : Bounded B xs := fun y hy => hx y (by simp [hy])
    obtain ⟨r₁,hg₁,hp⟩ := parse_cons regs acc ([],[]) x.1
      (x.2.1::x.2.2::tripleWords xs)
    obtain ⟨ts,hts,r₂,middle,hs,hv,hm,hl⟩ := termStep_eval_total r₁ acc
      x.1 x.2.1 x.2.2 (tripleWords xs) A B ha hb.1 hb.2.1 hb.2.2
    obtain ⟨tt,htt,r₃,result,hg₃,ht,hv₃,hm₃,hl₃⟩ :=
      ih r₂ middle (A+termGrowth B) hl hxs
    cases ht with
    | seq hn hw =>
      rename_i tn tw between
      refine ⟨6*pairLength x.1+11+(ts+tn+tw+1),?_,r₃,result,hg₃,?_,?_,?_,?_⟩
      · simp only [scalarCost,List.length_cons] at *
        omega
      · simpa only [scalarCommand,tripleWords,List.flatMap_cons,List.flatMap,
          List.map_cons, List.flatten_cons, List.cons_append,List.nil_append] using
          hp.seq (.while_true hg₁ (hs.seq hn) hw)
      · rw [hv₃,hv]
        simp [termValue,add_assoc]
      · rw [hm₃,hm]
        simp [termTotal,Nat.add_assoc]
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem scalarProgram_runsIn_total_oai (xs : List Triple) (regs : Fin 8 → Bool)
    (acc : WordPair) (A B : ℕ) (ha : pairLength acc ≤ A) (hx : Bounded B xs) :
    ∃ r result,
      RunsIn scalarProgram
        (200000000*(xs.length+1)*(A+xs.length*termGrowth B+B+4)^2+1)
        ((state regs acc ([],[]) ([],[]) (pairEncoding (tripleWords xs))).withPC
          (some scalarProgram.entry))
        ((state r result ([],[]) ([],[]) []).withPC none) ∧
      pairValue result = pairValue acc+(xs.map termValue).sum ∧
      wordTotal result = wordTotal acc+(xs.map termTotal).sum ∧
      pairLength result ≤ A+xs.length*termGrowth B := by
  obtain ⟨t,ht,r,result,_,he,hv,hm,hl⟩ := scalarCommand_eval_total xs regs acc A B ha hx
  have hb := scalarCost_poly xs.length A B
  exact ⟨r,result,⟨t+1,by omega,compiled_halt_trace he 0 16⟩,hv,hm,hl⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total_oai

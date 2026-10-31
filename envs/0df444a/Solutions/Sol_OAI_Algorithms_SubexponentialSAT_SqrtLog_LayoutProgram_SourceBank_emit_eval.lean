-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:38:29.205504+00:00
-- url     : https://prove2.me/submissions/a3236bbf-7b4d-4049-9ba9-69dba9b0ae3c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowDataProgram_active_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowEmitCall_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

open BitProgram

namespace CountRecords

theorem start (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 0) value present input output)
      (cfg (some 2) false present input (false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (steps records)
      (cfg (some program.entry) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (Encoding.encodeNat records.length ++ output)) := by
  have h := (start value present (Encoding.encodeList id records ++ suffix) output).trans
    (loop_trace records suffix (false :: output) false present)
  simpa [steps, Encoding.encodeNat, Nat.add_comm, List.append_assoc] using h

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

open BitProgram StructuredCalls StackRoutines

theorem countRegs_injective : Function.Injective countRegs := Fin.castAdd_injective 2 6
theorem countStacks_injective : Function.Injective countStacks := by decide

theorem count_eval (records : List Word) (a : Data)
    (hs : a.stacks 17 = Encoding.encodeList id records) (ho : a.stacks 14 = []) :
    Eval count (SubexpSunflowerProgram.CountRecords.steps records) a (counted a records.length) := by
  let inner : State 2 2 := ⟨a.regs ∘ countRegs, a.stacks ∘ countStacks⟩
  let last : State 2 2 := ⟨fun _ => false, ParserProgram.pair [] (Encoding.encodeNat records.length)⟩
  have ht : Trace SubexpSunflowerProgram.CountRecords.program
      (SubexpSunflowerProgram.CountRecords.steps records)
      (inner.withPC (some SubexpSunflowerProgram.CountRecords.program.entry)) (last.withPC none) := by
    have h := SubexpSunflowerProgram.CountRecords.trace records [] [] (inner.regs 0) (inner.regs 1)
    convert h using 1 <;>
      simp [inner, last, SubexpSunflowerProgram.CountRecords.cfg, StructuredProgram.State.withPC,
        countRegs, countStacks  ]
    · constructor <;> funext j <;> fin_cases j <;>
        simp [ParserProgram.pair, hs, ho]
    · funext j
      fin_cases j <;> rfl
  have hin : embedState countRegs countStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ countRegs_injective countStacks_injective <;> intros <;> rfl
  have hout : embedState countRegs countStacks a last = counted a records.length := by
    apply embedState_eq_of_ports _ _ _ _ _ countRegs_injective countStacks_injective
    · intro j
      fin_cases j <;> simp [last, counted, countRegs, readRegs]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      simp [counted, readRegs, h0, h1]
    · intro j
      fin_cases j <;> simp [last, counted, countStacks, ParserProgram.pair]
    · intro j hj
      have h17 : j ≠ 17 := fun h => hj ⟨0, h.symm⟩
      have h14 : j ≠ 14 := fun h => hj ⟨1, h.symm⟩
      simp [counted, h17, h14]
  have he := eval_call_lifted SubexpSunflowerProgram.CountRecords.program countRegs countStacks a
    countRegs_injective countStacks_injective (a := inner) (b := last) ht
  simpa only [count, hin, hout] using he

theorem compareRegs_injective : Function.Injective compareRegs := by decide
theorem compareStacks_injective : Function.Injective compareStacks := by decide

theorem compareClean_eval (a : Data) :
    ∃ n ≤ 6 * ((a.stacks 14).length + (a.stacks 11).length) + 12, ∃ b : Data,
      Eval compareClean n a b ∧
      b.regs 7 = decide ((a.stacks 14).length ≤ (a.stacks 11).length) ∧
      b.stacks = Function.update (Function.update a.stacks 14 []) 11 [] := by
  let inner : State 4 2 := ⟨a.regs ∘ compareRegs,
    UnaryCompare.pairStacks (a.stacks 14) (a.stacks 11)⟩
  obtain ⟨n, hn, c, ht, hpc, hans⟩ := UnaryCompare.runs inner.regs (a.stacks 14) (a.stacks 11)
  let last : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : last.withPC none = c := by
    cases c
    simp_all [last, StructuredProgram.State.withPC]
  have ht' : Trace UnaryCompare.program n
      (inner.withPC (some UnaryCompare.program.entry)) (last.withPC none) := by
    rw [hc]
    exact ht
  have hin : embedState compareRegs compareStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ compareRegs_injective compareStacks_injective
    · intros; rfl
    · intros; rfl
    · intro j
      fin_cases j <;> simp [inner, UnaryCompare.pairStacks, compareStacks]
    · intros; rfl
  let mid := embedState compareRegs compareStacks a last
  have hcompare : Eval compare n a mid := by
    have he := eval_call_lifted UnaryCompare.program compareRegs compareStacks a
      compareRegs_injective compareStacks_injective (a := inner) (b := last) ht'
    simpa only [compare, hin, mid] using he
  have hanswer : mid.regs 7 = decide ((a.stacks 14).length ≤ (a.stacks 11).length) := by
    change mid.regs (compareRegs 3) = _
    rw [embedState_register _ _ _ _ compareRegs_injective]
    exact hans
  have hl : (mid.stacks 14).length ≤ (a.stacks 14).length := by
    change (mid.stacks (compareStacks 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using UnaryCompare.trace_length_le ht 0
  have hr : (mid.stacks 11).length ≤ (a.stacks 11).length := by
    change (mid.stacks (compareStacks 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStacks_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using UnaryCompare.trace_length_le ht 1
  have hframe (j : Fin 32) (h14 : j ≠ 14) (h11 : j ≠ 11) : mid.stacks j = a.stacks j := by
    exact embedState_stack_frame _ _ _ _ j (by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp_all [compareStacks])
  let cleaned : Data := ⟨readRegs mid.regs 0 1 none, clearStacks 14 mid.stacks⟩
  let b : Data := ⟨readRegs cleaned.regs 0 1 none, clearStacks 11 cleaned.stacks⟩
  have h14 := TupleProgram.clear_eval 14 (0 : Fin 8) 1 mid
  have h11 := TupleProgram.clear_eval 11 (0 : Fin 8) 1 cleaned
  refine ⟨n + ((2 * (mid.stacks 14).length + 3) +
    (2 * (cleaned.stacks 11).length + 3)), ?_, b,
      hcompare.seq (h14.seq h11), ?_, ?_⟩
  · have hm := Nat.min_le_left (a.stacks 14).length (a.stacks 11).length
    have hcleaned : cleaned.stacks 11 = mid.stacks 11 := by simp [cleaned, clearStacks]
    rw [hcleaned]
    omega
  · simpa [b, cleaned, readRegs] using hanswer
  · funext j
    by_cases hj14 : j = 14 <;> by_cases hj11 : j = 11
    all_goals simp_all [b, cleaned, clearStacks ]

theorem command_eval (records : List Word) (limit : Word) (a : Data)
    (hrecords : a.stacks 28 = Encoding.encodeList id records) (hlimit : a.stacks 13 = limit)
    (h11 : a.stacks 11 = []) (h14 : a.stacks 14 = [])
    (h15 : a.stacks 15 = []) (h17 : a.stacks 17 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length + 13 * limit.length +
        6 * records.length + 40, ∃ b : Data,
      Eval command n a b ∧ b.regs 7 = decide (records.length ≤ limit.length) ∧ b.stacks = a.stacks := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 28 17 a.stacks⟩
  have hcopy := TupleProgram.copy_eval 28 17 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h15
  let a2 := counted a1 records.length
  have hcount := count_eval records a1
    (by simp [a1, copyStacks, hrecords, h17]) (by simpa [a1, copyStacks] using h14)
  let a3 := TupleProgram.pushedState (11 : Fin 32) (0 : Fin 8) false a2
  have hpush := TupleProgram.pushConst_eval (11 : Fin 32) (0 : Fin 8) false a2
  let a4 : Data := ⟨readRegs a3.regs 0 1 none, copyStacks 13 11 a3.stacks⟩
  have hlimitCopy := TupleProgram.copy_eval 13 11 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a3
    (by simpa [a3, a2, a1, TupleProgram.pushedState, counted, copyStacks] using h15)
  obtain ⟨nc, hnc, b, hc, hb, hbs⟩ := compareClean_eval a4
  have hs14 : a4.stacks 14 = Encoding.encodeNat records.length := by
    simp [a4, a3, a2, a1, counted, copyStacks]
  have hs11 : a4.stacks 11 = limit ++ [false] := by
    simp [a4, a3, a2, a1, counted, copyStacks, hlimit, h11]
  have ht := hcopy.seq (hcount.seq (hpush.seq (hlimitCopy.seq hc)))
  refine ⟨_, ?_, b, ht, ?_, ?_⟩
  · have hcountBound := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hs13 : a3.stacks 13 = limit := by
      simpa [a3, a2, a1, TupleProgram.pushedState, counted, copyStacks] using hlimit
    simp only [hs14, hs11, Encoding.encodeNat, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] at hnc
    simp only [hrecords, hs13]
    omega
  · simpa [hs14, hs11, Encoding.encodeNat] using hb
  · rw [hbs]
    funext j
    by_cases hj11 : j = 11 <;> by_cases hj14 : j = 14 <;> by_cases hj17 : j = 17 <;>
      simp_all [a4, a3, a2, a1, TupleProgram.pushedState, counted, copyStacks ]

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermFraming
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical framing of a gathered correction term and the final row. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermFraming

open BitProgram StructuredCalls

theorem row_eval (a : Data) (delta : Word)
    (ts : List (UniversalRowProgram.Term Word))
    (hd : a.stacks 18 = delta)
    (ht : a.stacks 31 = Encoding.encodeList UniversalRowProgram.encodeTerm ts)
    (h23 : a.stacks 23 = []) :
    ∃ b : Data, Eval row (8 * delta.length + 8) a b ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.encodeRow ⟨delta, ts⟩) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 18 31 23
    (by decide) (by decide) (by decide) a h23
  refine ⟨b, ?_, ?_⟩
  · simpa [row, hd] using hb
  · simpa [hd, ht, UniversalRowProgram.encodeRow] using hbs

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowDataProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

private theorem ready_same_stacks (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    {a b : Data} (h : ready t width rowWidth positions a) (hs : b.stacks = a.stacks) :
    ready t width rowWidth positions b := by
  rcases h with ⟨hv, hi, hn, hr, hp, hw, hwr, hidx, he⟩
  exact ⟨by simpa only [hs] using hv, by simpa only [hs] using hi,
    by simpa only [hs] using hn, by simpa only [hs] using hr,
    by simpa only [hs] using hp, by simpa only [hs] using hw,
    by simpa only [hs] using hwr, by simpa only [hs] using hidx,
    fun j hj => by simpa only [hs] using he j hj⟩

private theorem ready_update (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    {a b : Data} (h : ready t width rowWidth positions a) (port : Fin 32)
    (hp : port = 17 ∨ port = 31) (word : Word)
    (hs : b.stacks = Function.update a.stacks port word) : ready t width rowWidth positions b := by
  rcases hp with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hs] using h.values
    · simpa [hs] using h.inverses
    · simpa [hs] using h.negatives
    · simpa [hs] using h.rows
    · simpa [hs] using h.indices
    · simpa [hs] using h.width
    · simpa [hs] using h.rowWidth
    · simpa [hs] using h.index
    · intro j hj
      have he := h.empty j hj
      fin_cases j <;> simp_all []

theorem command_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (delta limit : Word) (a : Data)
    (ha : ready t width rowWidth positions a)
    (hd : a.stacks 18 = delta) (hlimit : a.stacks 13 = limit)
    (h14 : a.stacks 14 = []) (h17 : a.stacks 17 = []) (h31 : a.stacks 31 = []) :
    ∃ n ≤ cost t width rowWidth positions delta limit, ∃ b : Data,
      Eval command n a b ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.encodeRow (row t positions delta limit)) := by
  obtain ⟨ng, hng, a1, hg, hanswer, h1⟩ := UniversalRowGuard.command_eval
    (positions.reverse.map indexWord) limit a ha.indices hlimit
    (ha.empty 11 (by simp)) h14 (ha.empty 15 (by simp)) h17
  have ha1 := ready_same_stacks t width rowWidth positions ha h1
  let a2 := TupleProgram.pushedState (31 : Fin 32) (0 : Fin 8) false a1
  have hp := TupleProgram.pushConst_eval (31 : Fin 32) (0 : Fin 8) false a1
  have ha2 := ready_update t width rowWidth positions ha1 31 (Or.inr rfl)
    (false :: a1.stacks 31) (show a2.stacks = _ from rfl)
  have h2 : a2.stacks = Function.update a.stacks 31 [false] := by
    simp [a2, h1, h31]
  have hbranch : ∃ nb ≤ activeCost t width rowWidth positions + 1, ∃ a3 : Data,
      Eval (.ite 7 active (.base .skip)) nb a2 a3 ∧
      a3.stacks = Function.update a.stacks 31
        (Encoding.encodeList UniversalRowProgram.encodeTerm (row t positions delta limit).terms) := by
    by_cases h : positions.length ≤ limit.length
    · obtain ⟨na, hna, a3, he, hs⟩ := active_eval t width rowWidth positions valid a2 ha2
        (by simpa [h2] using h17) (by simp [h2])
      refine ⟨na + 1, by omega, a3, .ite_true ?_ he, ?_⟩
      · simpa [a2, TupleProgram.pushedState, h] using hanswer
      · simpa [row, h, h2] using hs
    · refine ⟨1, by omega, a2, .ite_false ?_ (.base (.skip _)), ?_⟩
      · simpa [a2, TupleProgram.pushedState, h] using hanswer
      · simpa [row, h, Encoding.encodeList] using h2
  obtain ⟨nb, hnb, a3, hb, h3⟩ := hbranch
  obtain ⟨b, hr, hbs⟩ := UniversalRowTermFraming.row_eval a3 delta
    (row t positions delta limit).terms (by simpa [h3] using hd) (by simp [h3])
    (by simpa [h3] using ha.empty 23 (by simp))
  refine ⟨ng + (2 + (nb + (8 * delta.length + 8))), ?_, b,
    hg.seq (hp.seq (hb.seq hr)), ?_⟩
  · simp only [List.length_map, List.length_reverse] at hng
    unfold cost
    change ng ≤ 10 * (UniversalRowTermProgram.indices positions).length +
      13 * limit.length + 6 * positions.length + 40 at hng
    omega
  · rw [hbs, h3]
    funext j
    by_cases hj18 : j = 18 <;> by_cases hj31 : j = 31 <;>
      simp_all [row, Function.update_apply]

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed producer from packed scalar/cache tables to row postfix bytes. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceProgram

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)

theorem program_runsIn (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (delta limit zero one : Word) (a : Data)
    (ha : ready t width rowWidth positions a)
    (hd : a.stacks 18 = delta) (hl : a.stacks 13 = limit)
    (hz : a.stacks 3 = zero) (ho : a.stacks 10 = one)
    (h14 : a.stacks 14 = []) (h17 : a.stacks 17 = []) (h31 : a.stacks 31 = []) :
    ∃ b : Data, RunsIn program (bound t width rowWidth positions delta limit zero one)
      (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.rowCode zero one (zero ++ one)
          (UniversalRowDataProgram.row t positions delta limit)) := by
  obtain ⟨nd, hnd, middle, hdata, hm⟩ := UniversalRowDataProgram.command_eval t width rowWidth
    positions valid delta limit a ha hd hl h14 h17 h31
  obtain ⟨ne, hne, hem⟩ := UniversalRowEmitCall.command_eval middle zero one
    (UniversalRowDataProgram.row t positions delta limit)
    (by simp [hm]) (by simpa [hm] using hz) (by simpa [hm] using ho)
    (by simpa [hm] using ha.empty 1 (by simp))
    (by simpa [hm] using ha.empty 2 (by simp))
    (by simpa [hm] using ha.empty 4 (by simp))
    (by simpa [hm] using ha.empty 5 (by simp))
    (by simpa [hm] using ha.empty 6 (by simp))
  refine ⟨_, ⟨nd + ne + 1, ?_, compiled_halt_trace (hdata.seq hem) 31 31⟩, ?_⟩
  · unfold bound
    omega
  · simp [UniversalRowEmitCall.result, hm]

end SubexponentialSAT.Subexp.UniversalRowSourceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured native stages used by the packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem emitterRegs_inj : Function.Injective emitterRegs := Fin.castAdd_injective _ _
theorem emitterPorts_inj : Function.Injective emitterPorts := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [emitterPorts] at hh
  omega

theorem emit_eval_oai (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (delta limit zero one : List Bool) (a : Data)
    (ha : UniversalRowLoop.ready tables width rowWidth positions
      (projectState emitterRegs emitterPorts a))
    (hd : a.stacks 274=delta) (hl : a.stacks 269=limit)
    (hz : a.stacks 259=zero) (ho : a.stacks 266=one)
    (h14 : a.stacks 270=[]) (h17 : a.stacks 273=[]) (h31 : a.stacks 287=[]) :
    ∃ n ≤ UniversalRowSourceProgram.bound tables width rowWidth positions delta limit zero one,
      ∃ b : Data, Eval emit n a b ∧
        b.stacks=Function.update (Function.update a.stacks 274 []) 287
          (UniversalRowProgram.rowCode zero one (zero++one)
            (UniversalRowDataProgram.row tables positions delta limit)) := by
  let small := projectState emitterRegs emitterPorts a
  obtain ⟨z,⟨n,hn,he⟩,hstack⟩ := UniversalRowSourceProgram.program_runsIn tables width rowWidth
    positions valid delta limit zero one small ha hd hl hz ho h14 h17 h31
  let b := embedState emitterRegs emitterPorts a z
  have hh := eval_call_from_state UniversalRowSourceProgram.program emitterRegs emitterPorts a
    emitterRegs_inj emitterPorts_inj he
  refine ⟨n,hn,b,hh,?_⟩
  change Function.extend emitterPorts z.stacks a.stacks=_
  rw [hstack,ProgramLinking.extend_update emitterPorts_inj,ProgramLinking.extend_update emitterPorts_inj]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project emitterRegs emitterPorts a emitterRegs_inj emitterPorts_inj)
  change Function.extend emitterPorts small.stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emit_eval_oai

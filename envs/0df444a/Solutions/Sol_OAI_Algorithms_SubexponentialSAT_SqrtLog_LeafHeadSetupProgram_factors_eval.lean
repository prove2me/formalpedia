-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:11:56.683555+00:00
-- url     : https://prove2.me/submissions/2e704ccd-1cf8-4a44-a1c6-0ce88262e25f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram_test_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

theorem cost_le (index bits : List Bool) : cost index bits ≤ 3 * index.length + 2 * bits.length + 6 := by
  induction index generalizing bits with
  | nil => simp only [cost,List.length_nil,Nat.mul_zero,Nat.zero_add,List.length_tail]; omega
  | cons b index ih =>
      have h := ih bits.tail
      have ht : bits.tail.length ≤ bits.length := by simp only [List.length_tail]; omega
      simp only [cost,List.length_cons]
      omega

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem testCost_bound (A j W : ℕ) (bitIndex word : List Bool) (hw : word.length = W) :
    testCost A j W bitIndex word ≤
      lookupCost (A + j) W + 9 * (A + j) + 10 * bitIndex.length + 2 * W + 24 := by
  have h := Subexp.TypeBitProgram.cost_le bitIndex word
  unfold testCost
  omega

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem emitFrame_eval (d : Data) (bits : List Bool) (hv : d.stacks 34 = bits.reverse) :
    ∃ e, Eval (Subexp.SupportSelectionProgram.emit 0 (by decide)) (5 * bits.length + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 34 []) 0
        ((true :: Encoding.frame bits) ++ d.stacks 0) := by
  let a := Subexp.TupleProgram.pushedState 0 0 false d
  let b := Subexp.TupleProgram.escapedState (Subexp.SupportSelectionProgram.emitPorts 0 (by decide)) a
  let e := Subexp.TupleProgram.pushedState 0 0 true b
  have h1 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false d
  have h2 := Subexp.TupleProgram.escape_eval_state (Subexp.SupportSelectionProgram.emitPorts 0 (by decide)) a
  have h3 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) true b
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq h3)
    change Eval (Subexp.SupportSelectionProgram.emit 0 (by decide)) _ d e at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    simp [a, Subexp.SupportSelectionProgram.emitPorts, hv]
    ; omega
  · funext i
    by_cases h0 : i = 0
    · subst i
      simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts, hv, Subexp.TupleProgram.frame_eq_escaped,
        List.append_assoc]
    by_cases h34 : i = 34
    · subst i
      simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts]
    · simp [e, b, a,
        Subexp.SupportSelectionProgram.emitPorts, h0, h34]

theorem emit_eval (d : Data) (j : ℕ) (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ e, Eval emit (12 * j + 21) d e ∧
      e.stacks = Function.update (Function.update d.stacks 0 (natRecord j ++ d.stacks 0))
        1 (false :: d.stacks 1) := by
  let a := afterCopy d 39 34 0 1
  have h1 : Eval (copy 39 34) (7 * j + 5) d a := by
    simpa [copy,Subexp.SupportSelectionProgram.copy,a,afterCopy,hj] using
      copy_eval d 39 34 42 0 1 (by decide) (by decide) (by decide) (by decide)
        (hc 42 (by decide))
  let b := Subexp.TupleProgram.pushedState 34 0 false a
  have h2 := Subexp.TupleProgram.pushConst_eval (34 : Fin 64) (0 : Fin 16) false a
  have hb : b.stacks 34 = (Encoding.encodeNat j).reverse := by
    simp [b, a, afterCopy, StackRoutines.copyStacks,
      hj, hc 34 (by decide), Encoding.encodeNat, List.reverse_append]
  obtain ⟨c, h3, hcs⟩ := emitFrame_eval b (Encoding.encodeNat j) hb
  let e := Subexp.TupleProgram.pushedState 1 0 false c
  have h4 := Subexp.TupleProgram.pushConst_eval (1 : Fin 64) (0 : Fin 16) false c
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq (h3.seq h4))
    convert he using 1 <;> simp [emit] ; omega
  · funext i
    by_cases h34 : i = 34
    · subst i
      simp [e, hcs, b, a, afterCopy,
        StackRoutines.copyStacks, hc 34 (by decide)]
    · by_cases h0 : i = 0
      · subst i; simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, natRecord]
      by_cases h1 : i = 1
      · subst i; simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, natRecord]
      · simp [e, hcs, b, a, afterCopy,
          StackRoutines.copyStacks, h34, h0, h1, natRecord]

theorem choose_eval (d : Data) (j : ℕ) (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ 12 * j + 22 ∧ Eval choose ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if d.regs 4 then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if d.regs 4 then false :: d.stacks 1 else d.stacks 1) := by
  cases hh : d.regs 4 with
  | false =>
    refine ⟨1, d, by omega, Eval.ite_false hh (.base (.skip d)), ?_⟩
    simp []
  | true =>
    obtain ⟨e, he, hs⟩ := emit_eval d j hj hc
    refine ⟨12 * j + 22, e, le_rfl, ?_, ?_⟩
    · simpa [choose, Nat.add_assoc] using Eval.ite_true hh he
    · simpa [hh] using hs

theorem visit_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (A j : ℕ)
    (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
    (hA : d.stacks 31 = unary A) (hj : d.stacks 39 = unary j)
    (hi : A + j = earlier.length) (hw : word.length = (d.stacks 38).length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound A j (d.stacks 38).length (d.stacks 32).length ∧
      Eval visit ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if word.getD (d.stacks 32).length false then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if word.getD (d.stacks 32).length false then false :: d.stacks 1 else d.stacks 1) := by
  let a := tested d (word.getD (d.stacks 32).length false)
  have ht : Eval test (testCost A j (d.stacks 38).length (d.stacks 32) word) d a := by
    simpa [a, hA, hj] using test_eval d earlier word rest hs (by simpa [hA, hj] using hi) hw hr hc
  obtain ⟨nc, e, hnc, he, hse⟩ := choose_eval a j hj hc
  refine ⟨_, e, ?_, ht.seq he, ?_⟩
  · have hb := testCost_bound A j (d.stacks 38).length (d.stacks 32) word hw
    unfold visitBound
    omega
  · simpa [a, tested, readRegs] using hse

theorem clean_outputs (d e : Data) (hc : Clean d) (xs ys : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 0 xs) 1 ys) : Clean e := by
  intro i hi
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  simpa [hs, h0, h1] using hc i hi

theorem visit_row (rows : List (List Bool)) (A W z j : ℕ) (d : Data)
    (hrows : ∀ row ∈ rows, row.length = W) (hlt : A + j < rows.length)
    (hs : d.stacks 33 = rows.flatten) (hA : d.stacks 31 = unary A)
    (hz : d.stacks 32 = unary z) (hw : d.stacks 38 = unary W)
    (hj : d.stacks 39 = unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound A j W z ∧ Eval visit ticks d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if predicate rows A z j then natRecord j ++ d.stacks 0 else d.stacks 0))
        1 (if predicate rows A z j then false :: d.stacks 1 else d.stacks 1) := by
  have hsplit := List.take_append_drop (A + j) rows
  rw [List.drop_eq_getElem_cons hlt] at hsplit
  have hsource : d.stacks 33 = (rows.take (A + j)).flatten ++
      (rows[A + j] ++ (rows.drop (A + j + 1)).flatten) := by
    calc
      d.stacks 33 = rows.flatten := hs
      _ = (rows.take (A + j) ++ rows[A + j] :: rows.drop (A + j + 1)).flatten :=
        congrArg List.flatten hsplit.symm
      _ = _ := by simp only [List.flatten_append, List.flatten_cons]
  have hlen : A + j = (rows.take (A + j)).length := by
    simp [List.length_take, Nat.min_eq_left hlt.le]
  have hword : rows[A + j].length = (d.stacks 38).length := by
    simpa [hw] using hrows rows[A + j] (List.getElem_mem hlt)
  have hearlier : ∀ row ∈ rows.take (A + j), row.length = (d.stacks 38).length := by
    intro row hr
    simpa [hw] using hrows row (List.mem_of_mem_take hr)
  obtain ⟨ticks, e, ht, he, hs'⟩ := visit_eval d (rows.take (A + j)) rows[A + j]
    (rows.drop (A + j + 1)).flatten A j hsource hA hj hlen hword hearlier hc
  refine ⟨ticks, e, ?_, he, ?_⟩
  · simpa [hw, hz] using ht
  · have hp : predicate rows A z j = rows[A + j].getD z false := by
      unfold predicate
      rw [List.getD_eq_getElem _ _ hlt]
    simpa only [hp, hz, List.length_replicate] using hs'

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem prefix_succ (p : ℕ → Bool) (n : ℕ) :
    recordPrefix p (n+1) = recordPrefix p n ++ (if p n then natRecord n else []) := by
  simp only [recordPrefix, chosenIds, List.range_succ, List.filter_append, List.flatMap_append]
  cases hp : p n <;> simp [hp]

theorem records_prefix (xs : List ℕ) :
    xs.flatMap natRecord ++ [false] = ProgramEncoding.encodeRecords (xs.map Encoding.encodeNat) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    change (natRecord j ++ xs.flatMap natRecord) ++ [false] =
      natRecord j ++ ProgramEncoding.encodeRecords (xs.map Encoding.encodeNat)
    rw [List.append_assoc, ih]

theorem prefix_encode (p : ℕ → Bool) (n : ℕ) :
    recordPrefix p n ++ [false] = ProgramEncoding.encodeRecords ((chosenIds p n).map Encoding.encodeNat) :=
  records_prefix _

theorem count_succ (p : ℕ → Bool) (n : ℕ) :
    count p (n+1)=count p n+(if p n then 1 else 0) := by
  simp only [count,chosenIds,List.range_succ,List.filter_append,List.length_append]
  cases hp : p n <;> simp [hp]

theorem visitBound_mono {a b : ℕ} (hab : a ≤ b) (A W z : ℕ) :
    visitBound A a W z ≤ visitBound A b W z := by
  unfold visitBound lookupCost
  gcongr

/-- Descending physical visits prepend records, so the resulting list is in
ascending original-factor order. Every visit is discharged by visit_row. -/
theorem loop_visits (rows : List (List Bool)) (A W z : ℕ)
    (hrows : ∀ row ∈ rows,row.length=W) (n : ℕ) :
    ∀ d : Data, A + n ≤ rows.length → d.stacks 33=rows.flatten → d.stacks 31=unary A →
      d.stacks 32=unary z → d.stacks 38=unary W → d.stacks 39=unary n → Clean d →
    ∃ costs ticks e, UnaryForPrograms.Visits loopPorts visit costs ticks d e ∧
      ticks ≤ n*(visitBound A rows.length W z+2)+2 ∧
      e.stacks=Function.update (Function.update (Function.update d.stacks 39 [])
        0 (recordPrefix (predicate rows A z) n++d.stacks 0))
        1 (zeros (count (predicate rows A z) n)++d.stacks 1) := by
  induction n with
  | zero =>
      intro d _ hs hA hz hw hn hc
      refine ⟨[],2,UnaryForPrograms.popped loopPorts d,.done d hn,by simp,?_⟩
      funext i
      by_cases h0 : i=0
      · subst i; simp [UnaryForPrograms.popped,loopPorts,recordPrefix,count,chosenIds]
      by_cases h1 : i=1
      · subst i; simp [UnaryForPrograms.popped,loopPorts,recordPrefix,count,chosenIds]
      by_cases h39 : i=39
      · subst i; simp [UnaryForPrograms.popped,loopPorts,hn]
      · simp [UnaryForPrograms.popped,loopPorts,h0,h1,h39]
  | succ n ih =>
      intro d hnd hs hA hz hw hn hc
      have hlt : A+n < rows.length := by omega
      let p := UnaryForPrograms.popped loopPorts d
      have hp39 : p.stacks 39=unary n := by
        simp [p,UnaryForPrograms.popped,loopPorts,hn,List.replicate_succ]
      have hp33 : p.stacks 33=rows.flatten := by simp [p,UnaryForPrograms.popped,loopPorts,hs]
      have hp31 : p.stacks 31=unary A := by simp [p,UnaryForPrograms.popped,loopPorts,hA]
      have hp32 : p.stacks 32=unary z := by simp [p,UnaryForPrograms.popped,loopPorts,hz]
      have hp38 : p.stacks 38=unary W := by simp [p,UnaryForPrograms.popped,loopPorts,hw]
      have hpc : Clean p := by
        intro i hi
        have hne : i ≠ 39 := by intro he; subst i; simp at hi
        simpa [p,UnaryForPrograms.popped,loopPorts,hne] using hc i hi
      obtain ⟨nv,e,hnv,hev,hes⟩ := visit_row rows A W z n p hrows hlt hp33 hp31 hp32 hp38 hp39 hpc
      have hnv' : nv ≤ visitBound A rows.length W z :=
        hnv.trans (visitBound_mono (by omega) A W z)
      have he39 : e.stacks 39=unary n := by simp [hes,hp39]
      obtain ⟨costs,nt,f,hv,hnt,hfs⟩ := ih e (by omega)
        (by simp [hes,hp33]) (by simp [hes,hp31]) (by simp [hes,hp32])
        (by simp [hes,hp38]) he39 (clean_outputs p e hpc _ _ hes)
      refine ⟨nv::costs,nv+nt+2,f,
        .step (by simp [loopPorts,hn]) hev (by simp [hes,loopPorts,p]) hv,?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · funext i
        by_cases h0 : i=0
        · subst i
          cases hp : predicate rows A z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,
              prefix_succ,hp,List.append_assoc]
        by_cases h1 : i=1
        · subst i
          cases hp : predicate rows A z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,count_succ,hp,
              zeros,List.replicate_succ',List.append_assoc]
        by_cases h39 : i=39
        · subst i; simp [hfs]
        · simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,h0,h1,h39]

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem setup_eval (regs : Fin 16 → Bool) (rows : List (List Bool)) (A N W z : ℕ) :
    ∃ e, Eval setup (7*N+7) (input regs rows A N W z) e ∧
      e.stacks=preparedStacks rows A N W z := by
  let d := input regs rows A N W z
  let a := afterCopy d 30 39 0 1
  let e := Subexp.TupleProgram.pushedState 0 0 false a
  have h1 : Eval (copy 30 39) (7*N+5) d a := by
    have he := copy_eval d 30 39 42 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    simpa [Subexp.SupportSelectionProgram.copy, a, d, input, baseStacks] using he
  have h2 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false a
  refine ⟨e,?_,?_⟩
  · convert h1.seq h2 using 1 ; simp [setup]
  · funext i
    by_cases h39 : i=39
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    by_cases h0 : i=0
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    · simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks,h0,h39]

theorem program_runsIn (regs : Fin 16 → Bool) (rows : List (List Bool))
    (A N W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) (hsize : A+N ≤ rows.length) :
    RunsIn program (budget A N rows.length W z)
      ((input regs rows A N W z).withPC (some program.entry))
      ((result rows A N W z).withPC none) := by
  obtain ⟨d,hs,hsd⟩ := setup_eval regs rows A N W z
  have hdClean : Clean d := by
    intro i hi
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [hsd,preparedStacks,baseStacks]
  obtain ⟨costs,nl,e,hv,hnl,hse⟩ := loop_visits rows A W z hrows N d hsize
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks]) hdClean
  have hz := RegisterResetProgram.all_eval e
  have hout : RegisterResetProgram.zeroed e=result rows A N W z := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [hse,hsd,preparedStacks,baseStacks,result,
        prefix_encode]
  rw [hout] at hz
  have he := hs.seq (hv.eval.seq hz)
  refine ⟨7*N+7+(nl+16)+1,?_,compiled_halt_trace he 30 0⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem work_ne_temporary {s : ℕ} (hs : s ≤ 288) (i : Fin s) :
    workPort hs i ≠ temporary := by
  intro h
  have := congrArg Fin.val h
  have := i.isLt
  simp only [workPort,temporary] at *
  omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem inputCopies_good {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p ∈ ins, Protected p.1) :
    ∀ p ∈ inputCopies hs ins, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨protected_ne_work hs (hi q hq) q.2,(hi q hq).2,(work_ne_temporary hs q.2).symm⟩

theorem outputCopies_good {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p ∈ outs, Protected p.2) :
    ∀ p ∈ outputCopies hs outs, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨(protected_ne_work hs (ho q hq) q.1).symm,work_ne_temporary hs q.1,(ho q hq).2.symm⟩

theorem prepared_word {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (hi : ∀ p ∈ ins, Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (p : Fin 768 × Fin s) (hp : p ∈ ins) :
    (prepared hs ins a).stacks (workPort hs p.2) = a.stacks p.1 := by
  have hd' : ((inputCopies hs ins).map Prod.snd).Nodup := by
    simpa only [inputCopies,List.map_map,Function.comp_def] using
      hd.map (workPort_injective hs)
  have hc : ∀ q ∈ inputCopies hs ins,
      (beforeCopies temporary (workPorts hs) a).stacks q.2 = [] := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
      ite_eq_left (work_mem_workPorts hs z.2)]
  have hsep : ∀ q ∈ inputCopies hs ins, ∀ z ∈ inputCopies hs ins, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact protected_ne_work hs (hi q' hq') z'.2
  have hv := copyMany_value (inputCopies hs ins) (beforeCopies temporary (workPorts hs) a)
    hd' hc hsep (p.1,workPort hs p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
  change (prepared hs ins a).stacks (workPort hs p.2) = _ at hv
  rw [hv]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
    ite_eq_right (protected_not_workPorts hs (hi p hp))]
  simp [(hi p hp).2]

theorem prepared_empty {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (j : Fin s) (hj : ∀ p ∈ ins,j ≠ p.2) :
    (prepared hs ins a).stacks (workPort hs j) = [] := by
  have hn : ∀ p ∈ inputCopies hs ins,workPort hs j ≠ p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact fun h => hj q hq (workPort_injective hs h)
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hn]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,ite_eq_left (work_mem_workPorts hs j)]

theorem prepared_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (a : Data) (b : State r s)
    (hi : ∀ p ∈ ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (hr : ∀ j,(prepared hs ins a).regs (reg j)=b.regs j)
    (hw : ∀ p ∈ ins,b.stacks p.2=a.stacks p.1)
    (hz : ∀ j,(∀ p ∈ ins,j≠p.2)→b.stacks j=[]) :
    projectState reg (workPort hs) (prepared hs ins a)=b := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; exact hr j
  · funext j
    by_cases hm : ∃ p ∈ ins,p.2=j
    · obtain ⟨p,hp,rfl⟩ := hm
      exact (prepared_word hs ins a hi hd p hp).trans (hw p hp).symm
    · have hj : ∀ p ∈ ins,j≠p.2 := by
        intro p hp h; exact hm ⟨p,hp,h.symm⟩
      exact (prepared_empty hs ins a j hj).trans (hz j hj).symm

theorem stage_eval {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hr : Function.Injective reg) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b c : State r s) {t : ℕ}
    (hi : ∀ q ∈ ins,Protected q.1) (ho : ∀ q ∈ outs,Protected q.2)
    (hl : projectState reg (workPort hs) (prepared hs ins a)=b)
    (ht : Trace p t (b.withPC (some p.entry)) (c.withPC none)) :
    Eval (stage p reg hs ins outs) (stageCost reg hs ins outs a c t) a
      (returned reg hs ins outs a c) := by
  apply isolated_eval p reg (workPort hs) hr (workPort_injective hs)
    temporary (workPorts hs) (inputCopies hs ins) (outputCopies hs outs) a c
    (inputCopies_good hs ins hi) (outputCopies_good hs outs ho)
  · rintro ⟨j,hj⟩; exact work_ne_temporary hs j hj
  · change Trace p t ((projectState reg (workPort hs) (prepared hs ins a)).withPC _) _
    rw [hl]
    exact ht

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem factorInputs_protected : ∀ p ∈ factorInputs,Protected p.1 := by simp [factorInputs,Protected,temporary]
theorem factorOutputs_protected : ∀ p ∈ factorOutputs,Protected p.2 := by simp [factorOutputs,Protected,temporary]

theorem factors_eval_oai (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (hN : a.stacks 129=unary N) (hA : a.stacks 128=unary A)
    (hz : a.stacks 649=unary z) (hrows : a.stacks 133=rows.flatten)
    (hW : a.stacks 132=unary W) (hw : ∀ row∈rows,row.length=W) (hsize : A+N ≤ rows.length) :
    ∃ t ≤ factorCost a A N rows W z,Eval factors t a (factorResult a A N rows W z) := by
  let regs := (prepared (by decide) factorInputs a).regs
  have hp : projectState id (workPort (by decide)) (prepared (by decide) factorInputs a)=
      LeafHeadFactorsProgram.input regs rows A N W z := by
    apply prepared_eq id (by decide) factorInputs a _ factorInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [factorInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;>
        simp [LeafHeadFactorsProgram.input,LeafHeadFactorsProgram.baseStacks,hN,hA,hz,hrows,hW,unary]
    · intro j hj
      have h30 : j≠30 := hj (129,30) (by simp [factorInputs])
      have h31 : j≠31 := hj (128,31) (by simp [factorInputs])
      have h32 : j≠32 := hj (649,32) (by simp [factorInputs])
      have h33 : j≠33 := hj (133,33) (by simp [factorInputs])
      have h38 : j≠38 := hj (132,38) (by simp [factorInputs])
      simp [LeafHeadFactorsProgram.input,LeafHeadFactorsProgram.baseStacks,h30,h31,h32,h33,h38]
  obtain ⟨t,ht,he⟩ := LeafHeadFactorsProgram.program_runsIn regs rows A N W z hw hsize
  have hc := stage_eval LeafHeadFactorsProgram.program id Function.injective_id (by decide)
    factorInputs factorOutputs a _ _ factorInputs_protected factorOutputs_protected hp he
  refine ⟨_,?_,hc⟩
  unfold factorCost stageCost
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factors_eval_oai

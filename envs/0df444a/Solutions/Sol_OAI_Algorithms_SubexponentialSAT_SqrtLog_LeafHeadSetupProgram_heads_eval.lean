-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:12:23.667708+00:00
-- url     : https://prove2.me/submissions/2cdb2804-c58c-4884-a88b-b4d3fc700e13

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HeadIdentifierProgram_visit_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered support records selected from the actual packing inverse. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open ConstructivePacking

variable {D r Q Δ : ℕ}

theorem prefix_succ (p : ℕ → Bool) (n : ℕ) :
    supportPrefix p (n + 1) = supportPrefix p n ++ if p n then record n else [] := by
  simp only [supportPrefix, List.range_succ, List.filter_append, List.flatMap_append]
  cases h : p n <;> simp [h]

theorem prefix_encode (p : ℕ → Bool) (n : ℕ) :
    supportPrefix p n ++ [false] = Encoding.encodeList id (indexWords p n) := by
  have h (xs : List ℕ) : xs.flatMap record ++ [false] =
      Encoding.encodeList id (xs.map unary) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons, Encoding.encodeList, id_eq]
      rw [List.append_assoc, ih]
      rfl
  exact h _

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- Only outputs 0 and 1 change; the work invariant is restored. -/
theorem clean_outputs (d e : Data) (hc : Clean d) (xs ys : List Bool)
    (hs : e.stacks=Function.update (Function.update d.stacks 0 xs) 1 ys) : Clean e := by
  intro i hi
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  simpa [hs,h0,h1] using hc i hi

/-- Row selection is by the original array index, including rows not covered
by a complete packing block. -/
theorem visit_row (rows : List (List Bool)) (low : List Bool) (W z j : ℕ) (d : Data)
    (hrows : ∀ row ∈ rows,row.length=W) (hlt : j < rows.length)
    (hs : d.stacks 33=rows.flatten) (hl : d.stacks 31=low)
    (hz : d.stacks 32=unary z) (hw : d.stacks 38=unary W)
    (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound j W low.length z ∧ Eval visit ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if predicate rows low z j then record j++d.stacks 0 else d.stacks 0))
        1 (if predicate rows low z j then false::d.stacks 1 else d.stacks 1) := by
  have hsplit := List.take_append_drop j rows
  rw [List.drop_eq_getElem_cons hlt] at hsplit
  have hsource : d.stacks 33=(rows.take j).flatten++(rows[j]++(rows.drop (j+1)).flatten) := by
    exact hs.trans (by
      simpa only [List.flatten_append,List.flatten_cons,List.append_assoc] using
        congrArg List.flatten hsplit.symm)
  have hlen : j=(rows.take j).length := by simp [List.length_take,Nat.min_eq_left hlt.le]
  have hword : rows[j].length=(d.stacks 38).length := by
    simpa [hw] using hrows rows[j] (List.getElem_mem hlt)
  have hearlier : ∀ row ∈ rows.take j,row.length=(d.stacks 38).length := by
    intro row hr
    simpa [hw] using hrows row (List.mem_of_mem_take hr)
  obtain ⟨ticks,e,ht,he,hs'⟩ := visit_eval d (rows.take j) rows[j] (rows.drop (j+1)).flatten j
    hsource hj hlen hword hearlier hc
  refine ⟨ticks,e,?_,he,?_⟩
  · simpa [hw,hl,hz] using ht
  · have hget : rows.getD j []=rows[j] := List.getD_eq_getElem _ _ hlt
    simpa only [predicate,hl,hz,List.length_replicate,hget] using hs'

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem count_succ (p : ℕ → Bool) (n : ℕ) :
    count p (n+1)=count p n+(if p n then 1 else 0) := by
  simp only [count,chosenIds,List.range_succ,List.filter_append,List.length_append]
  cases hp : p n <;> simp [hp]

theorem visitBound_mono {a b : ℕ} (hab : a ≤ b) (W L z : ℕ) :
    visitBound a W L z ≤ visitBound b W L z := by
  unfold visitBound lookupCost
  gcongr

/-- Descending physical visits prepend records, so the resulting list is in
ascending original-variable order. Every visit is discharged by visit_row. -/
theorem loop_visits (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (hrows : ∀ row ∈ rows,row.length=W) (n : ℕ) :
    ∀ d : Data, n ≤ rows.length → d.stacks 33=rows.flatten → d.stacks 31=low →
      d.stacks 32=unary z → d.stacks 38=unary W → d.stacks 39=unary n → Clean d →
    ∃ costs ticks e, UnaryForPrograms.Visits loopPorts visit costs ticks d e ∧
      ticks ≤ n*(visitBound rows.length W low.length z+2)+2 ∧
      e.stacks=Function.update (Function.update (Function.update d.stacks 39 [])
        0 (supportPrefix (predicate rows low z) n++d.stacks 0))
        1 (zeros (count (predicate rows low z) n)++d.stacks 1) := by
  induction n with
  | zero =>
      intro d _ hs hl hz hw hn hc
      refine ⟨[],2,UnaryForPrograms.popped loopPorts d,.done d hn,by simp,?_⟩
      funext i
      by_cases h0 : i=0
      · subst i; simp [UnaryForPrograms.popped,loopPorts,count,chosenIds]
      by_cases h1 : i=1
      · subst i; simp [UnaryForPrograms.popped,loopPorts,count,chosenIds]
      by_cases h39 : i=39
      · subst i; simp [UnaryForPrograms.popped,loopPorts,hn]
      · simp [UnaryForPrograms.popped,loopPorts,h0,h1,h39]
  | succ n ih =>
      intro d hnd hs hl hz hw hn hc
      have hlt : n < rows.length := by omega
      let p := UnaryForPrograms.popped loopPorts d
      have hp39 : p.stacks 39=unary n := by
        simp [p,UnaryForPrograms.popped,loopPorts,hn,List.replicate_succ]
      have hp33 : p.stacks 33=rows.flatten := by simp [p,UnaryForPrograms.popped,loopPorts,hs]
      have hp31 : p.stacks 31=low := by simp [p,UnaryForPrograms.popped,loopPorts,hl]
      have hp32 : p.stacks 32=unary z := by simp [p,UnaryForPrograms.popped,loopPorts,hz]
      have hp38 : p.stacks 38=unary W := by simp [p,UnaryForPrograms.popped,loopPorts,hw]
      have hpc : Clean p := by
        intro i hi
        have hne : i ≠ 39 := by intro he; subst i; simp at hi
        simpa [p,UnaryForPrograms.popped,loopPorts,hne] using hc i hi
      obtain ⟨nv,e,hnv,hev,hes⟩ := visit_row rows low W z n p hrows hlt hp33 hp31 hp32 hp38 hp39 hpc
      have hnv' : nv ≤ visitBound rows.length W low.length z :=
        hnv.trans (visitBound_mono (by omega) W low.length z)
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
          cases hp : predicate rows low z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,
              Subexp.SupportSelectionProgram.prefix_succ,hp,List.append_assoc]
        by_cases h1 : i=1
        · subst i
          cases hp : predicate rows low z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,count_succ,hp,
              zeros,List.replicate_succ',List.append_assoc]
        by_cases h39 : i=39
        · subst i; simp [hfs]
        · simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,h0,h1,h39]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem setup_eval (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    ∃ e, Eval setup (7*n+7) (input regs n rows low W z) e ∧
      e.stacks=preparedStacks n rows low W z := by
  let d := input regs n rows low W z
  let a := afterCopy d 30 39 0 1
  let e := Subexp.TupleProgram.pushedState 0 0 false a
  have h1 : Eval (copy 30 39) (7*n+5) d a := by
    have he := copy_eval d 30 39 42 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    simpa [Subexp.SupportSelectionProgram.copy, a, d, input, baseStacks] using he
  have h2 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false a
  refine ⟨e,?_,?_⟩
  · simpa only [setup, HeadIdentifierProgram.setup, Nat.add_assoc,
      Nat.reduceAdd] using h1.seq h2
  · funext i
    by_cases h39 : i=39
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    by_cases h0 : i=0
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    · simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks,h0,h39]

theorem program_runsIn (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool)
    (W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) (hn : n ≤ rows.length) :
    RunsIn program (budget n rows.length W low.length z)
      ((input regs n rows low W z).withPC (some program.entry))
      ((result n rows low W z).withPC none) := by
  obtain ⟨d,hs,hsd⟩ := setup_eval regs n rows low W z
  have hdClean : Clean d := by
    intro i hi
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [hsd,preparedStacks,baseStacks]
  obtain ⟨costs,nl,e,hv,hnl,hse⟩ := loop_visits rows low W z hrows n d hn
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks]) hdClean
  have hz := RegisterResetProgram.all_eval e
  have hout : RegisterResetProgram.zeroed e=result n rows low W z := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [hse,hsd,preparedStacks,baseStacks,result,
        Subexp.SupportSelectionProgram.prefix_encode,ProgramEncoding.encodeRecords,
        Subexp.SupportSelectionProgram.indexWords,chosenIds]
  rw [hout] at hz
  have he := hs.seq (hv.eval.seq hz)
  refine ⟨7*n+7+(nl+16)+1,?_,compiled_halt_trace he 30 0⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable

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

theorem headInputs_protected : ∀ p ∈ headInputs,Protected p.1 := by simp [headInputs,Protected,temporary]
theorem headOutputs_protected : ∀ p ∈ headOutputs,Protected p.2 := by simp [headOutputs,Protected,temporary]

theorem heads_eval_oai (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (hn : a.stacks 128=unary n) (hlow : a.stacks 134=low)
    (hz : a.stacks 649=unary z) (hrows : a.stacks 133=rows.flatten)
    (hW : a.stacks 132=unary W) (hw : ∀ row∈rows,row.length=W) (hsize : n ≤ rows.length) :
    ∃ t ≤ headCost a n rows low W z,Eval heads t a (headResult a n rows low W z) := by
  let regs := (prepared (by decide) headInputs a).regs
  have hp : projectState id (workPort (by decide)) (prepared (by decide) headInputs a)=
      HeadIdentifierProgram.FullTable.input regs n rows low W z := by
    apply prepared_eq id (by decide) headInputs a _ headInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [headInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;>
        simp [HeadIdentifierProgram.FullTable.input,HeadIdentifierProgram.FullTable.baseStacks,
          hn,hlow,hz,hrows,hW,unary]
    · intro j hj
      have h30 : j≠30 := hj (128,30) (by simp [headInputs])
      have h31 : j≠31 := hj (134,31) (by simp [headInputs])
      have h32 : j≠32 := hj (649,32) (by simp [headInputs])
      have h33 : j≠33 := hj (133,33) (by simp [headInputs])
      have h38 : j≠38 := hj (132,38) (by simp [headInputs])
      simp [HeadIdentifierProgram.FullTable.input,HeadIdentifierProgram.FullTable.baseStacks,
        h30,h31,h32,h33,h38]
  obtain ⟨t,ht,he⟩ := HeadIdentifierProgram.FullTable.program_runsIn regs n rows low W z hw hsize
  have hc := stage_eval HeadIdentifierProgram.FullTable.program id Function.injective_id
    (by decide) headInputs headOutputs a _ _ headInputs_protected headOutputs_protected hp he
  refine ⟨_,?_,hc⟩
  unfold headCost stageCost
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.heads_eval_oai

-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:25.632255+00:00
-- url     : https://prove2.me/submissions/ab5dfee8-874b-47a2-9ee6-8d142475d70b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S143
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutMatrixProgram_rowScan_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective _ _

theorem lift8_eval {s : ℕ} (c : Cmd 8 s) (input output : Fin s) (d : Data s)
    (t : ℕ) (e : State 8 s)
    (he : Eval c t (projectState regs8 id d) e) :
    ∃ rf, Eval (lift8 c input output) (t+1) d ⟨rf,e.stacks⟩ := by
  let z := embedState regs8 id d e
  have hs := embedState_project regs8 (id : Fin s → Fin s) d
    regs8_injective Function.injective_id
  have hz : z = ⟨z.regs,e.stacks⟩ := by
    apply congrArg (StructuredProgram.State.mk z.regs)
    funext i
    exact embedState_stack regs8 id d e Function.injective_id i
  have h := eval_call_lifted (compiled c input output) regs8 id d
    regs8_injective Function.injective_id (compiled_halt_trace he input output)
  rw [hs] at h
  change Eval (lift8 c input output) (t+1) d z at h
  rw [hz] at h
  exact ⟨z.regs,h⟩

theorem frame_eval {s : ℕ} (src dst tmp : Fin s) (hsd : src ≠ dst)
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp=[]) :
    ∃ e, Eval (frame src dst tmp htd) (8*(d.stacks src).length+9) d e ∧
      e.stacks=Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src)++d.stacks dst) := by
  obtain ⟨e,he,hs⟩ := Subexp.MatrixProgramSupport.emitFrame_eval src dst tmp hsd hst htd
    (projectState regs8 id d) ht
  obtain ⟨rf,hf⟩ := lift8_eval _ src dst d _ e he
  refine ⟨⟨rf,e.stacks⟩,?_,hs⟩
  convert hf using 1 ; simp [projectState]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem update_rowIndex (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 277 word =
      (state base regs {q with rowIndex:=word}).stacks := by
  funext i
  by_cases h : i=277
  · subst i; simp [state]
  · simp [state,h]

theorem update_remaining (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 281 word =
      (state base regs {q with remaining:=word}).stacks := by
  funext i
  by_cases h : i=281
  · subst i; simp [state]
  · simp [state,h]

theorem update_todo (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 283 word =
      (state base regs {q with todo:=word}).stacks := by
  funext i
  by_cases h : i=283
  · subst i; simp [state]
  · simp [state,h]

theorem update_row (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 284 word =
      (state base regs {q with row:=word}).stacks := by
  funext i
  by_cases h : i=284
  · subst i; simp [state]
  · simp [state,h]

theorem update_matrix (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 24 word =
      (state base regs {q with matrix:=word}).stacks := by
  funext i
  by_cases h : i=24
  · subst i; simp [state]
  · simp [state,h]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid traversal of the explicit original-column identifier records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowScanCost_le (T B n : ℕ) (js : List ℕ) (h : ∀ v ∈ js, v ≤ n) :
    rowScanCost T B js ≤ js.length*(T+8*B+8*n+29)+3 := by
  induction js with
  | nil => simp [rowScanCost]
  | cons v vs ih =>
    have hv := h v (by simp)
    have ht := ih (fun w hw => h w (by simp [hw]))
    simp only [rowScanCost,List.length_cons]
    nlinarith

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical row preparation and output framing for all-D construction. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copyRowIndex_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (regs : Fin 16 → Bool) (q : Store) (hq : q.rowIndex=[]) :
    Eval copyRowIndex (7*q.remaining.length+5) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with rowIndex:=q.remaining}) := by
  have h := Subexp.TupleProgram.copy_eval (281 : Fin 288) 277 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    simp only [StackRoutines.copyStacks]
    simpa [state,hq] using (update_rowIndex base regs q q.remaining).symm

theorem copyIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (regs : Fin 16 → Bool) (q : Store) (hq : q.todo=[]) :
    Eval copyIDs (7*q.reversedIDs.length+5) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with todo:=q.reversedIDs}) := by
  have h := Subexp.TupleProgram.copy_eval (282 : Fin 288) 283 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    simp only [StackRoutines.copyStacks]
    simpa [state,hq] using (update_todo base regs q q.reversedIDs).symm

theorem emitRow_eval (base : Fin 288 → List Bool) (hb : base 286=[])
    (regs : Fin 16 → Bool) (q : Store) :
    ∃ rf, Eval emitRow (8*q.row.length+9) (state base regs q)
      (state base rf {q with row:=[],matrix:=Encoding.frame q.row++q.matrix}) := by
  obtain ⟨e,he,hs⟩ := frame_eval (284 : Fin 288) 24 286
    (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  have heq : e=state base e.regs {q with row:=[],matrix:=Encoding.frame q.row++q.matrix} := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    rw [hs]
    change Function.update (Function.update (state base regs q).stacks 284 []) 24
      (Encoding.frame q.row++q.matrix)=_
    rw [update_row,update_matrix]
    rfl
  rw [heq] at he
  exact ⟨e.regs,by simpa [emitRow,state] using he⟩

theorem clearRowIndex_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearRowIndex (2*q.rowIndex.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with rowIndex:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (277 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    exact (update_rowIndex base regs q []).symm

theorem pairWords_length_le {Rel : ℕ → Pair → Prop} {js : List ℕ} {ps : List Pair}
    {B : ℕ} (h : List.Forall₂ (fun v p => Rel v p ∧ pairLength p ≤ B) js ps) :
    (pairWords ps).length ≤ 2*js.length*B+2*js.length := by
  induction h with
  | nil => simp [pairWords]
  | @cons v p vs ps hp ht ih =>
    simp only [pairWords,List.length_append,Encoding.length_frame,List.length_cons]
    dsimp [pairLength] at hp
    nlinarith [hp.2]

theorem rowBody_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (j n : ℕ) (js : List ℕ)
    (hvalid : ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (regs : Fin 16 → Bool) (q : Store)
    (hj : q.remaining=List.replicate j true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ t ≤ rowBodyCost T B n j (ids js.reverse).length js.length, ∃ rf ps,
      Eval (rowBody entry) t (state base regs q)
        (state base rf {q with rowIndex:=[],columnIndex:=[],positive:=[],negative:=[],todo:=[],row:=[], matrix:=Encoding.frame (pairWords ps)++q.matrix}) ∧
      List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps := by
  have hcopy := copyRowIndex_eval base hb regs q hr
  let q₁ : Store := {q with rowIndex:=q.remaining}
  let r₁ := readRegs regs 0 1 none
  have hcopy' := copyIDs_eval base hb r₁ q₁ htodo
  let q₂ : Store := {q₁ with todo:=q.reversedIDs}
  let r₂ := readRegs r₁ 0 1 none
  obtain ⟨ts,hts,rs,ps,hes,hps⟩ := rowScan_eval entry base hb' Valid Rel T B hc j js.reverse
    (fun v hv => hvalid v (by simpa using hv)) r₂ q₂ hj hcol hp hn hids
  have hrel : List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps.reverse := by
    simpa using List.rel_reverse hps
  have hlen := pairWords_length_le hrel
  let q₃ : Store := {q₂ with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}
  obtain ⟨re,hee⟩ := emitRow_eval base hb' rs q₃
  let q₄ : Store := {q₃ with row:=[],matrix:=Encoding.frame q₃.row++q₃.matrix}
  have hec := clearRowIndex_eval base re q₄
  have hscan := rowScanCost_le T B n js.reverse (fun v hv => hbound v (by simpa using hv))
  refine ⟨(7*q.remaining.length+5)+((7*q.reversedIDs.length+5)+
    (ts+((8*q₃.row.length+9)+(2*q₄.rowIndex.length+3)))),?_,
    readRegs re 0 1 none,ps.reverse,?_,hrel⟩
  · simp only [List.length_reverse] at hscan
    dsimp [q₄,q₃,q₂,q₁,rowBodyCost]
    rw [hj,hids,hrow,List.append_nil,List.length_replicate]
    nlinarith
  · simpa [rowBody,q₄,q₃,q₂,q₁,r₂,r₁,hrow] using
      hcopy.seq (hcopy'.seq (hes.seq (hee.seq hec)))

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested traversal: descending unary rows and reversed original head
IDs, with prepending restoring the requested row and column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

@[simp] theorem rowsWords_append (a b : List (List Pair)) :
    rowsWords (a++b)=rowsWords a++rowsWords b := by
  simp [rowsWords,Subexp.MatrixProgramSupport.words_append]

theorem popped_state (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    UnaryForPrograms.popped counter (state base regs q)=
      state base (readRegs regs 0 1 q.remaining.head?) {q with remaining:=q.remaining.tail} := by
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 q.remaining.head?))
  change Function.update (state base regs q).stacks 281 q.remaining.tail = _
  exact update_remaining base regs q q.remaining.tail

theorem rowLoop_visits (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (k : ℕ) (hk : k ≤ D) (regs : Fin 16 → Bool) (q : Store)
    (hrem : q.remaining=List.replicate k true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ costs t rf rows,
      UnaryForPrograms.Visits counter (rowBody entry) costs t (state base regs q)
        (state base rf {q with remaining:=[],matrix:=rowsWords rows++q.matrix}) ∧
      List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
        (List.range k) rows ∧
      t ≤ k*(rowBodyCost T B n D (ids js.reverse).length js.length+2)+2 := by
  induction k generalizing regs q with
  | zero =>
    have hq : q.remaining=[] := by simpa using hrem
    refine ⟨[],2,readRegs regs 0 1 none,[],?_,.nil,by simp⟩
    have hv := UnaryForPrograms.Visits.done (p:=counter) (body:=rowBody entry)
      (state base regs q) (by simp [state,counter,hq])
    simpa [popped_state,hq,rowsWords,Subexp.MatrixProgramSupport.words] using hv
  | succ k ih =>
    let qp : Store := {q with remaining:=List.replicate k true}
    let rp := readRegs regs 0 1 (some true)
    have hpop : UnaryForPrograms.popped counter (state base regs q)=state base rp qp := by
      rw [popped_state,hrem]
      simp [rp,qp,List.replicate_succ]
    obtain ⟨tb,htb,rb,row,heb,hrel⟩ := rowBody_eval entry base hb hb' Valid Rel T B hc k n js
      (hvalid k (by omega)) hbound rp qp rfl hids hr hcol hp hn htodo hrow
    let qb : Store := {q with remaining:=List.replicate k true, matrix:=Encoding.frame (pairWords row)++q.matrix}
    have heb' : Eval (rowBody entry) tb (UnaryForPrograms.popped counter (state base regs q))
        (state base rb qb) := by
      rw [hpop]
      simpa [qp,qb,hr,hcol,hp,hn,htodo,hrow] using heb
    obtain ⟨costs,tt,rf,rows,hvis,hrels,htt⟩ := ih (by omega) rb qb rfl hids
      hr hcol hp hn htodo hrow
    refine ⟨tb::costs,tb+tt+2,rf,rows++[row],?_,?_,?_⟩
    · have hv := UnaryForPrograms.Visits.step
        (d:=state base regs q) (e:=state base rb qb)
        (by simp [state,counter,hrem,List.replicate_succ]) heb'
        (by rw [hpop]; rfl) hvis
      simpa [qb,rowsWords_append,rowsWords,Subexp.MatrixProgramSupport.words,Subexp.MatrixProgramSupport.words_append,List.append_assoc] using hv
    · simpa [List.range_succ] using List.rel_append hrels (List.Forall₂.cons hrel List.Forall₂.nil)
    · have hm : rowBodyCost T B n k (ids js.reverse).length js.length ≤
          rowBodyCost T B n D (ids js.reverse).length js.length := by
        unfold rowBodyCost
        omega
      nlinarith

theorem rowLoop_eval_oai (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v) (hbound : ∀ v ∈ js, v ≤ n)
    (regs : Fin 16 → Bool) (q : Store)
    (hrem : q.remaining=List.replicate D true) (hids : q.reversedIDs=ids js.reverse)
    (hr : q.rowIndex=[]) (hcol : q.columnIndex=[]) (hp : q.positive=[]) (hn : q.negative=[])
    (htodo : q.todo=[]) (hrow : q.row=[]) :
    ∃ t ≤ D*(rowBodyCost T B n D (ids js.reverse).length js.length+2)+2, ∃ rf rows,
      Eval (rowLoop entry) t (state base regs q)
        (state base rf {q with remaining:=[],matrix:=rowsWords rows++q.matrix}) ∧
      List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
        (List.range D) rows := by
  obtain ⟨costs,t,rf,rows,hv,hr,ht⟩ := rowLoop_visits entry base hb hb' Valid Rel T B hc D n js
    hvalid hbound D le_rfl regs q hrem hids hr hcol hp hn htodo hrow
  exact ⟨t,ht,rf,rows,hv.eval,hr⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval_oai

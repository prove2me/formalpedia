-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:52.657969+00:00
-- url     : https://prove2.me/submissions/29a43b0f-df5a-40d1-93e0-5d55e5200aa6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S143

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

theorem parse_nil {s : ℕ} (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (tail : List Bool) (hs : d.stacks src=false::tail)
    (hd : d.stacks dst=[]) :
    ∃ rf, rf 2=false ∧ Eval (parse src dst h) 2 d (parsed src dst d rf tail []) := by
  let a := (StructuredProgram.Atom.pop src 2 3).eval d
  have ha : a.regs 2=false := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs,readRegs]
  have heq : a=parsed src dst d a.regs tail [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i
    by_cases hi : i=dst
    · subst i
      simp [StructuredProgram.Atom.instr,execInstr,hs,hd,Ne.symm h]
    · simp [StructuredProgram.Atom.instr,execInstr,hs,hi]
  refine ⟨a.regs,ha,?_⟩
  rw [←heq]
  exact (Eval.base (StructuredProgram.Eval.atom (.pop src 2 3) d)).seq
    (.ite_false ha (.base (.skip a)))

theorem parse_cons {s : ℕ} (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (bits tail : List Bool)
    (hs : d.stacks src=true::(Encoding.frame bits++tail)) (hd : d.stacks dst=[]) :
    ∃ rf, rf 2=true ∧ Eval (parse src dst h) (6*bits.length+6) d
      (parsed src dst d rf tail bits.reverse) := by
  let a := (StructuredProgram.Atom.pop src 2 3).eval d
  have ha : a.regs 2=true := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs,readRegs]
  have has : a.stacks src=Encoding.frame bits++tail := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs]
  have had : a.stacks dst=[] := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hd,Ne.symm h]
  let p := readerPorts src dst h
  have hp := RecordPrograms.state_eq_self p a (a.regs 0) (a.regs 1) (a.regs 2)
    _ [] rfl rfl rfl has had
  have hr := RecordPrograms.reader_eval p a bits tail [] (a.regs 0) (a.regs 1) (a.regs 2)
  rw [hp] at hr
  let e := RecordPrograms.state p a false true (a.regs 2) tail bits.reverse
  have hg : e.regs 2=true := by simpa [e,p,readerPorts,RecordPrograms.state] using ha
  have heq : e=parsed src dst d e.regs tail bits.reverse := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases hi : i=dst
    · subst i; simp [p,readerPorts]
    · by_cases hj : i=src
      · subst i; simp [p,readerPorts,h]
      · simp [p,a,
          StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,hi,hj]
  refine ⟨e.regs,hg,?_⟩
  rw [←heq]
  have hh := (Eval.base (StructuredProgram.Eval.atom (.pop src 2 3) d)).seq
    (Eval.ite_true (no := .base .skip) ha hr)
  convert hh using 1
  · omega
  · simp [e]

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

theorem bankPort_injective : Function.Injective bankPort := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [bankPort] at this
  omega

@[simp] theorem bankPort_eq (i : Fin 256) (j : Fin 256) :
    bankPort i=bankPort j ↔ i=j := bankPort_injective.eq_iff

private theorem bankPort_ne_low (i : Fin 256) (j : Fin 288) (h : j.val < 25) :
    bankPort i ≠ j := by
  intro he
  have := congrArg Fin.val he
  simp [bankPort] at this
  omega
private theorem bankPort_ne_high (i : Fin 256) (j : Fin 288) (h : 280 < j.val) :
    bankPort i ≠ j := by
  intro he
  have := congrArg Fin.val he
  simp [bankPort] at this
  have := i.isLt
  omega

private theorem project_entry (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    projectState id bankPort (state base regs q) =
      entryState base regs q.rowIndex q.columnIndex q.positive q.negative := by
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  have h24 := bankPort_ne_low i 24 (by decide)
  have h281 := bankPort_ne_high i 281 (by decide)
  have h282 := bankPort_ne_high i 282 (by decide)
  have h283 := bankPort_ne_high i 283 (by decide)
  have h284 := bankPort_ne_high i 284 (by decide)
  change (if bankPort i=bankPort 252 then _ else if bankPort i=bankPort 253 then _ else
    if bankPort i=bankPort 254 then _ else if bankPort i=bankPort 255 then _ else _) = _
  simp [h24,h281,h282,h283,h284]

private theorem embed_entry (base : Fin 288 → List Bool) (regs rf : Fin 16 → Bool)
    (q : Store) (P N : List Bool) :
    embedState id bankPort (state base regs q)
      (entryState base rf q.rowIndex q.columnIndex P N) =
      state base rf {q with positive:=P,negative:=N} := by
  apply embedState_eq_of_ports id bankPort _ _ _ Function.injective_id bankPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    have h := congrArg (fun d : Data 256 => d.stacks i)
      (project_entry base rf {q with positive:=P,negative:=N})
    exact h
  · intro i hi
    have h279 : i ≠ 279 := fun h => hi ⟨254,by simpa [bankPort] using h.symm⟩
    have h280 : i ≠ 280 := fun h => hi ⟨255,by simpa [bankPort] using h.symm⟩
    simp [state,h279,h280]

theorem entryCall_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B)
    (regs : Fin 16 → Bool) (q : Store) (j v : ℕ) (hv : Valid j v)
    (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=List.replicate v true)
    (hp : q.positive=[]) (hn : q.negative=[]) :
    ∃ t ≤ T+1, ∃ rf result,
      Eval (entryCall entry) t (state base regs q)
        (state base rf {q with positive:=result.1,negative:=result.2}) ∧
      Rel j v result ∧ pairLength result ≤ B := by
  obtain ⟨t,ht,rf,result,he,hr,hb⟩ := hc regs j v hv
  have hs : projectState id bankPort (state base regs q)=
      entryState base regs (List.replicate j true) (List.replicate v true) [] [] := by
    rw [project_entry,hj,hcol,hp,hn]
  rw [←hs] at he
  have hh := eval_call_lifted (compiled entry 252 254) id bankPort (state base regs q)
    Function.injective_id bankPort_injective (compiled_halt_trace he 252 254)
  rw [embedState_project id bankPort _ Function.injective_id bankPort_injective] at hh
  rw [←hj,←hcol,embed_entry] at hh
  exact ⟨t+1,by omega,rf,result,hh,hr,hb⟩

theorem update_columnIndex (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 278 word =
      (state base regs {q with columnIndex:=word}).stacks := by
  funext i
  by_cases h : i=278
  · subst i; simp [state]
  · simp [state,h]

theorem update_positive (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 279 word =
      (state base regs {q with positive:=word}).stacks := by
  funext i
  by_cases h : i=279
  · subst i; simp [state]
  · simp [state,h]

theorem update_negative (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 280 word =
      (state base regs {q with negative:=word}).stacks := by
  funext i
  by_cases h : i=280
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

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual matrix coefficient call followed by physical signed framing. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem emitPair_eval (base : Fin 288 → List Bool) (hb : base 286=[])
    (regs : Fin 16 → Bool) (q : Store) :
    ∃ rf, Eval emitPair (8*(q.positive.length+q.negative.length)+18)
      (state base regs q) (state base rf {q with positive:=[],negative:=[], row:=Encoding.frame q.positive++Encoding.frame q.negative++q.row}) := by
  obtain ⟨a,ha,hsa⟩ := frame_eval (280 : Fin 288) 284 286
    (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  let qa : Store := {q with negative:=[],row:=Encoding.frame q.negative++q.row}
  have hea : a=state base a.regs qa := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    rw [hsa]
    simp only [state]
    change Function.update (Function.update (state base regs q).stacks 280 []) 284
      (Encoding.frame q.negative++q.row)=(state base a.regs qa).stacks
    rw [update_negative,update_row]
    rfl
  rw [hea] at ha
  obtain ⟨b,hb',hsb⟩ := frame_eval (279 : Fin 288) 284 286
    (by decide) (by decide) (by decide) (state base a.regs qa) (by simp [state,hb])
  have heb : b=state base b.regs {q with positive:=[],negative:=[], row:=Encoding.frame q.positive++Encoding.frame q.negative++q.row} := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    rw [hsb]
    change Function.update (Function.update (state base a.regs qa).stacks 279 []) 284
      (Encoding.frame q.positive++qa.row)=_
    rw [update_positive,update_row]
    simp [state,qa,List.append_assoc]
  rw [heb] at hb'
  refine ⟨b.regs,?_⟩
  convert ha.seq hb' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp [state, qa]; omega)

theorem clearColumn_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearColumn (2*q.columnIndex.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with columnIndex:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (278 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  unfold clearColumn
  rw [show (state base regs q).stacks 278 = q.columnIndex by simp [state]] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
  exact (update_columnIndex base regs q []).symm

theorem coefficientStep_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 286=[]) (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (regs : Fin 16 → Bool) (q : Store)
    (j v : ℕ) (hv : Valid j v) (hj : q.rowIndex=List.replicate j true)
    (hcol : q.columnIndex=List.replicate v true) (hp : q.positive=[]) (hn : q.negative=[]) :
    ∃ t ≤ T+8*B+2*v+22, ∃ rf result,
      Eval (coefficientStep entry) t (state base regs q)
        (state base rf {q with columnIndex:=[],positive:=[],negative:=[], row:=Encoding.frame result.1++Encoding.frame result.2++q.row}) ∧
      Rel j v result ∧ pairLength result ≤ B := by
  obtain ⟨t,ht,r,result,he,hr,hl⟩ := entryCall_eval entry base Valid Rel T B hc regs q j v hv hj hcol hp hn
  obtain ⟨r',hf⟩ := emitPair_eval base hb r {q with positive:=result.1,negative:=result.2}
  have hg := clearColumn_eval base r' {q with positive:=[],negative:=[], row:=Encoding.frame result.1++Encoding.frame result.2++q.row}
  refine ⟨t+((8*(result.1.length+result.2.length)+18)+(2*q.columnIndex.length+3)),?_,
    readRegs r' 0 1 none,result,he.seq (hf.seq hg),hr,hl⟩
  dsimp [pairLength] at hl
  rw [hcol,List.length_replicate]
  omega

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

private theorem parsed_state (base : Fin 288 → List Bool) (regs rf : Fin 16 → Bool)
    (q : Store) (tail bits : List Bool) :
    parsed 283 278 (state base regs q) rf tail bits =
      state base rf {q with todo:=tail,columnIndex:=bits} := by
  apply congrArg (StructuredProgram.State.mk rf)
  change Function.update (Function.update (state base regs q).stacks 283 tail) 278 bits = _
  rw [update_todo,update_columnIndex]
  rfl

theorem rowScan_eval_oai (entry : Code 256) (base : Fin 288 → List Bool) (hb : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (j : ℕ) (js : List ℕ)
    (hvalid : ∀ v ∈ js, Valid j v) (regs : Fin 16 → Bool) (q : Store)
    (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=[])
    (hp : q.positive=[]) (hn : q.negative=[]) (htodo : q.todo=ids js) :
    ∃ t ≤ rowScanCost T B js, ∃ rf ps,
      Eval (rowScan entry) t (state base regs q)
        (state base rf {q with columnIndex:=[],positive:=[],negative:=[],todo:=[], row:=pairWords ps.reverse++q.row}) ∧
      List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js ps := by
  induction js generalizing regs q with
  | nil =>
    obtain ⟨rf,hg,he⟩ := parse_nil (283 : Fin 288) 278 (by decide) (state base regs q) []
      (by simpa [state,ids,ProgramEncoding.encodeRecords, Encoding.encodeList] using htodo)
      (by simpa [state] using hcol)
    rw [parsed_state] at he
    refine ⟨3,le_rfl,rf,[],?_,.nil⟩
    have hw := he.seq (Eval.while_false (body:=.seq (coefficientStep entry)
      (parse 283 278 (by decide))) hg)
    simpa [rowScan,pairWords,hp,hn] using hw
  | cons v vs ih =>
    obtain ⟨r₁,hg,hparse⟩ := parse_cons (283 : Fin 288) 278 (by decide)
      (state base regs q) (List.replicate v true) (ids vs)
      (by simpa [state,ids,ProgramEncoding.encodeRecords, Encoding.encodeList] using htodo)
      (by simpa [state] using hcol)
    rw [parsed_state] at hparse
    simp only [List.reverse_replicate] at hparse
    let q₁ : Store := {q with todo:=ids vs,columnIndex:=List.replicate v true}
    obtain ⟨ta,hta,r₂,p,he,hr,hl⟩ := coefficientStep_eval entry base hb Valid Rel T B hc r₁ q₁
      j v (hvalid v (by simp)) hj rfl hp hn
    let q₂ : Store := {q with todo:=ids vs,columnIndex:=[],positive:=[],negative:=[], row:=Encoding.frame p.1++Encoding.frame p.2++q.row}
    obtain ⟨tt,htt,r₃,ps,ht,hps⟩ := ih (fun w hw => hvalid w (by simp [hw])) r₂ q₂
      hj rfl rfl rfl rfl
    cases ht with
    | seq hnext hwhile =>
      rename_i tn tw between
      refine ⟨(6*v+6)+(ta+tn+tw+1),?_,r₃,p::ps,?_,.cons ⟨hr,hl⟩ hps⟩
      · simp only [rowScanCost] at htt ⊢
        omega
      · have hall := hparse.seq (Eval.while_true hg (he.seq hnext) hwhile)
        simpa [rowScan,q₁,q₂,pairWords,List.reverse_cons,List.append_assoc] using hall

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval_oai

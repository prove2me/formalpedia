-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:44:32.145344+00:00
-- url     : https://prove2.me/submissions/47f945a2-30d0-4f9c-95df-80cd30e074a2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_RawTable_call_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramReset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Reset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (command is) is.length a (result is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip _)
  | cons i is ih =>
      let b : State r s := ⟨Function.update a.regs i false,a.stacks⟩
      have hs : Eval (.base (.atom (.set i false))) 1 a b := .base (.atom _ _)
      have he : result is b = result (i::is) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hji : j=i <;> by_cases hj : j ∈ is <;>
            simp [b,hji,hj,Function.update]
        · rfl
      have h := hs.seq (ih b)
      rw [he] at h
      simpa [command,Nat.add_comm] using h

theorem all_eval {r s : ℕ} (a : State r s) :
    Eval (all : Cmd r s) r a ⟨fun _ => false,a.stacks⟩ := by
  simpa [all,result] using command_eval (List.finRange r) a

end SubexponentialSAT.SqrtLog.HashScopeProgram.Reset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

theorem emit_eval (a : Data) : Eval emit (5*(a.stacks 47).length+7) a (emitted a) := by
  have h := (pushConst_eval (48 : Fin 49) (8 : Fin 11) false a).seq
    ((escape_eval_state ports (pushedState 48 8 false a)).seq
      (pushConst_eval (48 : Fin 49) (8 : Fin 11) true (escapedState ports (pushedState 48 8 false a))))
  convert h using 1 <;> simp [emitted,ports,pushedState] ; omega

theorem fix_eval (a : Data) : Eval fix 3 a (fixed a) := by
  exact (Eval.base (.atom _ a)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))

theorem command_eval (a : Data) (bits : List Bool) (h : a.stacks 47=bits.reverse) :
    ∃ b : Data, Eval command (5*bits.length+10) a b ∧
      b.stacks 47=[] ∧ b.stacks 48=prependRecord bits (a.stacks 48) ∧
      b.regs 8=false ∧ b.regs 9=true ∧ b.regs 10=false ∧
      ∀ i, i ≠ 47 → i ≠ 48 → b.stacks i=a.stacks i := by
  refine ⟨fixed (emitted a),?_,?_,?_,?_,?_,?_,?_⟩
  · convert (emit_eval a).seq (fix_eval (emitted a)) using 1 ; simp [h]
  · simp [fixed,emitted,ports,pushedState]
  · simp [fixed,emitted,ports,pushedState,h,prependRecord,frame_eq_escaped,List.append_assoc]
  · simp [fixed]
  · simp [fixed]
  · simp [fixed]
  · intro i hi47 hi48
    simp [fixed,emitted,ports,pushedState,hi47,hi48]

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem takeInput_eval (rf : Fin 11 → Bool) (width modulus master shape source bits out : List Bool) :
    Eval takeInput (6*bits.length+6)
      (data rf [] width modulus master shape [] source bits.reverse out [])
      (data (readRegs (readRegs rf 8 9 none) 8 9 none) bits.reverse width modulus master shape [] source [] out []) := by
  let a := data rf [] width modulus master shape [] source bits.reverse out []
  let z := SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 47 45 8 9
  have h1 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 47 45 8 9 (by decide) (by decide)
  have h2 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval z 45 0 8 9 (by decide) (by decide)
  have hz : (z.stacks 45).length=bits.length := by
    simp [z,a,data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer z 45 0 8 9=
      data (readRegs (readRegs rf 8 9 none) 8 9 none) bits.reverse width modulus master shape [] source [] out [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [z,a,data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]
  have hh := h1.seq h2
  rw [hz,he] at hh
  simpa [takeInput,a,data,show 3*bits.length+3+(3*bits.length+3)=6*bits.length+6 by omega] using hh

theorem takeOutput_eval (rf : Fin 11 → Bool) (width modulus master shape source bits out : List Bool) :
    Eval takeOutput (3*bits.length+3)
      (data rf [] width modulus master shape bits source [] out [])
      (data (readRegs rf 8 9 none) [] width modulus master shape [] source bits.reverse out []) := by
  have hh := SubexponentialSAT.SubexpScanPrimitives.transfer_eval
    (data rf [] width modulus master shape bits source [] out []) 16 47 8 9 (by decide) (by decide)
  convert hh using 1
  · rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext i; fin_cases i <;> simp [data,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]

theorem callback_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape source out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ callbackCost t d b modulus clauses codes terms, ∃ rf',
      rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval callback n
        (data rf [] width modulus (Encoding.encodeList id clauses) shape [] source (rowBits b terms).reverse out [])
        (data rf' [] width modulus (Encoding.encodeList id clauses) shape [] source []
          (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) out) []) := by
  have hi := takeInput_eval rf width modulus (Encoding.encodeList id clauses) shape source (rowBits b terms) out
  have hz := Reset.all_eval (data (readRegs (readRegs rf 8 9 none) 8 9 none)
    (rowBits b terms).reverse width modulus (Encoding.encodeList id clauses) shape [] source [] out [])
  obtain ⟨nc,hnc,rc,hec⟩ := call_eval t d ht b hb clauses codes hc terms hbound width modulus shape source out hw hm hshape
  have ho := takeOutput_eval rc width modulus (Encoding.encodeList id clauses) shape source (scopeBytes (clauses := clauses) t d codes terms) out
  let a := data (readRegs rc 8 9 none) [] width modulus (Encoding.encodeList id clauses) shape [] source
    (scopeBytes (clauses := clauses) t d codes terms).reverse out []
  obtain ⟨z,he,h47,h48,h8,h9,h10,hframe⟩ := RawFrame.command_eval a (scopeBytes (clauses := clauses) t d codes terms) (by simp [a,data])
  have hez : z=data z.regs [] width modulus (Encoding.encodeList id clauses) shape [] source []
      (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) out) [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      by_cases hi47 : i=47
      · subst i; simpa [data] using h47
      by_cases hi48 : i=48
      · subst i; simpa [a,data] using h48
      rw [hframe i hi47 hi48]
      simp [a,data,hi47,hi48]
  rw [hez] at he
  refine ⟨_,?_,z.regs,h8,h9,h10,hi.seq (hz.seq (hec.seq (ho.seq he)))⟩
  unfold callbackCost
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed outer scanner for a table of raw tuple payloads. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls



theorem parser_state (rf : Fin 11 → Bool) (v p f : Bool)
    (width modulus master shape src pay out : List Bool) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src pay =
      state (RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src pay).regs
        width modulus master shape src pay out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data]

theorem parser_state_self (rf : Fin 11 → Bool) (width modulus master shape src out : List Bool)
    (h8 : rf 8=false) (h9 : rf 9=true) (h10 : rf 10=false) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) false true false src [] =
      state rf width modulus master shape src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i
    change (Function.update (Function.update (Function.update rf 8 false) 9 true) 10 false) i=rf i
    fin_cases i <;> simp [h8,h9,h10]
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem loop_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 1+loopCost t d b modulus clauses codes rows, ∃ rf',
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (state rf width modulus (Encoding.encodeList id clauses) shape [] [] out)
          (rows.map (rowBits b)) [])
        (RecordPrograms.state ports
          (state rf' width modulus (Encoding.encodeList id clauses) shape [] [] (appendScopes (clauses := clauses) t d codes rows out))
          false true false [] []) := by
  induction rows generalizing rf out with
  | nil =>
      refine ⟨1,by simp [loopCost],rf,?_⟩
      apply Eval.while_false
      simp [RecordPrograms.afterTag,RecordPrograms.state,ports]
  | cons row rows ih =>
      let base := state rf width modulus (Encoding.encodeList id clauses) shape [] [] out
      let tail := Encoding.encodeList id (rows.map (rowBits b))
      let initial := RecordPrograms.state ports base false true false tail (rowBits b row).reverse
      have hin : initial=state initial.regs width modulus (Encoding.encodeList id clauses) shape tail (rowBits b row).reverse out :=
        parser_state rf false true false width modulus (Encoding.encodeList id clauses) shape tail (rowBits b row).reverse out
      obtain ⟨nc,hnc,rc,h8,h9,h10,hec⟩ := callback_eval t d ht b hb clauses codes hc row hbound
        initial.regs width modulus shape tail out hw hm hshape
      let middle := state rc width modulus (Encoding.encodeList id clauses) shape [] []
        (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row) out)
      have hcallback : Eval callback nc initial (RecordPrograms.state ports middle false true false tail []) := by
        rw [hin,parser_state_self rc width modulus (Encoding.encodeList id clauses) shape tail _ h8 h9 h10]
        exact hec
      have hreader : Eval (RecordPrograms.reader ports) (6*(rowBits b row).length+4)
          (RecordPrograms.afterTag ports base ((row::rows).map (rowBits b)) []) initial := by
        simpa [RecordPrograms.afterTag,base,initial,tail] using
          RecordPrograms.reader_eval ports base (rowBits b row) tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordPrograms.afterTag ports middle (rows.map (rowBits b)) []) := by
        apply Eval.ite_false (by simp)
        simpa [tail] using RecordPrograms.pop_list_eval ports middle (rows.map (rowBits b)) [] false true
      obtain ⟨nr,hnr,rr,her⟩ := ih rc (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row) out)
      have hguard : (RecordPrograms.afterTag ports base ((row::rows).map (rowBits b)) []).regs ports.tag=true := by
        simp [RecordPrograms.afterTag]
      refine ⟨(6*(rowBits b row).length+4+(nc+2))+nr+1,?_,rr,?_⟩
      · simp only [loopCost]; omega
      · simpa [RecordPrograms.loop,RecordPrograms.body,appendScopes,middle] using
          Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) her

theorem iterate_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 3+loopCost t d b modulus clauses codes rows, ∃ rf',
      Eval iterate n
        (RecordPrograms.state ports (state rf width modulus (Encoding.encodeList id clauses) shape [] [] out)
          false false false (Encoding.encodeList id (rows.map (rowBits b))) [])
        (RecordPrograms.state ports
          (state rf' width modulus (Encoding.encodeList id clauses) shape [] [] (appendScopes (clauses := clauses) t d codes rows out))
          false true false [] []) := by
  let base := state rf width modulus (Encoding.encodeList id clauses) shape [] [] out
  have hs := RecordPrograms.set_found_eval ports base false false false false
    (Encoding.encodeList id (rows.map (rowBits b))) []
  have hp := RecordPrograms.pop_list_eval ports base (rows.map (rowBits b)) [] false false
  simp only [List.append_nil] at hp
  obtain ⟨n,hn,rf',he⟩ := loop_eval t d ht b hb clauses codes hc rows hbound rf width modulus shape out hw hm hshape
  refine ⟨1+(1+n),by omega,rf',?_⟩
  simpa [iterate,RecordPrograms.iterate,base] using hs.seq (hp.seq he)

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem state_flags (rf : Fin 11 → Bool) (width modulus master shape src out : List Bool) (v p f : Bool) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src []=
      state (flags rf v p f) width modulus master shape src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data,flags]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data]

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem data_empty (rf : Fin 11 → Bool) (width modulus master shape out index flag : List Bool) :
    data rf width modulus master shape [] out index flag=
      Marked.data rf width modulus master shape out index flag [] [] [] := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; by_cases hj : j=46 <;> simp [data,Marked.data,Marked.tapes,hj]

theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

private theorem restrict_data (rf : Fin 11 → Bool) (width modulus master shape source out index flag : List Bool) :
    restrictState id lowStacks (data rf width modulus master shape source out index flag)=
      RawTable.state rf width modulus master shape source [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> rfl

private theorem embed_data (rf rr : Fin 11 → Bool)
    (width modulus master shape oldSource oldOut source out index flag : List Bool) :
    embedState id lowStacks (data rf width modulus master shape oldSource oldOut index flag)
      (RawTable.state rr width modulus master shape source [] out)=
        data rr width modulus master shape source out index flag := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowStacks_injective
  · intro j; rfl
  · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h46 : j≠46 := fun h => hj ⟨46,h.symm⟩
    have h48 : j≠48 := fun h => hj ⟨48,h.symm⟩
    simp [data,Marked.tapes,h46,h48]

theorem runRows_eval_oai (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape out index flag : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 4+RawTable.loopCost t d b modulus clauses codes rows, ∃ rf,
      Eval runRows n
        (data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) out index flag)
        (Marked.data rf width modulus (Encoding.encodeList id clauses) shape
          (RawTable.appendScopes (clauses := clauses) t d codes rows out) index flag [] [] []) := by
  obtain ⟨nr,hnr,rf,hr⟩ := RawTable.iterate_eval t d ht b hb clauses codes hc rows hbound RawTable.zeroRegs
    width modulus shape out hw hm hshape
  rw [RawTable.state_flags,RawTable.state_flags] at hr
  have hz : RawTable.flags RawTable.zeroRegs false false false=RawTable.zeroRegs := by
    funext j; simp [RawTable.flags,RawTable.zeroRegs]
  rw [hz] at hr
  let a := data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) out index flag
  let z := RawTable.state (RawTable.flags rf false true false) width modulus (Encoding.encodeList id clauses) shape [] []
    (RawTable.appendScopes (clauses := clauses) t d codes rows out)
  have hrun : RunsIn rowsProgram (4+RawTable.loopCost t d b modulus clauses codes rows)
      ((restrictState id lowStacks a).withPC (some rowsProgram.entry)) (z.withPC none) := by
    rw [restrict_data]
    exact ⟨nr+1,by omega,compiled_halt_trace hr 46 48⟩
  obtain ⟨n,hn,he⟩ := lifted_call rowsProgram id lowStacks Function.injective_id lowStacks_injective a z
    (4+RawTable.loopCost t d b modulus clauses codes rows) hrun
  exact ⟨n,hn,_,by simpa [runRows,a,z,embed_data,data_empty] using he⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval_oai

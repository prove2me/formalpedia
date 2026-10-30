-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:34:36.364778+00:00
-- url     : https://prove2.me/submissions/b03a5f05-7ea6-4762-8620-34c052b137ce

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_portStep_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.Subexp

theorem ternary_scalarWord (x : SparseCode.F3) :
    MatrixWordEncoding.word 3 x=[decide (x=1),decide (x=2)] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 3=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem ternary_frames (xs : List SparseCode.F3) :
    CodeSearchProgram.scalarFrames xs=
      xs.flatMap (fun x => Cell.frame (decide (x=1)) (decide (x=2))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Encoding.frame (MatrixWordEncoding.word 3 x) ++ CodeSearchProgram.scalarFrames xs = _
    rw [ternary_scalarWord,ih]
    rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable binary indexing for Cayley vertices. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem cubeEquiv_encode (r : ℕ) (x : Cube r) :
    ((cubeEquiv r).symm x).val = ∑ j, (x j).val * 2 ^ j.val := by
  rfl

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem index_value (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) :
    (index shifts side v p).val =
      ((WalshExistence.cubeEquiv r).symm (if side then v+shifts p else v)).val*D+p.val := by
  simp [index,SparseCode.edgeEquiv,edge,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

theorem toNat_ofFn {r : ℕ} (f : Fin r → Bool) :
    BinaryArithmetic.toNat (List.ofFn f)=∑ i : Fin r,bitVal (f i)*2^i.val := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ,toNat_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem vertexBits_value {r : ℕ} (v : Cayley.Cube r) :
    BinaryArithmetic.toNat (vertexBits v)=((WalshExistence.cubeEquiv r).symm v).val := by
  rw [vertexBits,toNat_ofFn,WalshExistence.cubeEquiv_encode]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hb (x : ZMod 2) : bitVal (decide (x=1))=x.val := by fin_cases x <;> decide
  exact hb (v i)

theorem shifted_vertexBits {r : ℕ} (side : Bool) (v s : Cayley.Cube r) :
    Shift.result side (List.ofFn fun i => (decide (v i=1),decide (s i=1))) =
      vertexBits (if side then v+s else v) := by
  simp only [Shift.result,List.map_ofFn,vertexBits,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  cases side
  · rfl
  · have hb (x y : ZMod 2) : (decide (x=1)).xor (decide (y=1))=decide (x+y=1) := by
      fin_cases x <;> fin_cases y <;> decide
    exact hb (v i) (s i)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem shiftRows_cons {r : ℕ} (v : Cayley.Cube r) (vs : List (Cayley.Cube r)) :
    shiftRows (v::vs)=Shift.frames (vertexBits v)++shiftRows vs := by
  simp [shiftRows]

theorem scalar_drop_head {D : ℕ} (q : Fin D → SparseCode.F3) (i : ℕ) (hi : i < D) :
    CodeSearchProgram.scalarFrames ((List.ofFn q).drop i)=
      Cell.frame (decide (q ⟨i,hi⟩=1)) (decide (q ⟨i,hi⟩=2)) ++
        CodeSearchProgram.scalarFrames ((List.ofFn q).drop (i+1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp [ternary_frames]

theorem shifts_drop_head {r D : ℕ} (shifts : Fin D → Cayley.Cube r) (i : ℕ) (hi : i < D) :
    shiftRows ((List.ofFn shifts).drop i)=Shift.frames (vertexBits (shifts ⟨i,hi⟩))++
      shiftRows ((List.ofFn shifts).drop (i+1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi),shiftRows_cons]
  simp

theorem prefixSlots_succ {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i : ℕ) (hi : i < D) :
    prefixSlots m shifts Q side v a (i+1)=prefixSlots m shifts Q side v a i ++
      (slot m shifts Q side v a ⟨i,hi⟩).toList := by
  unfold prefixSlots
  rw [List.take_succ_eq_append_getElem (by simpa using hi)]
  simp
  cases hs : slot m shifts Q side v a ⟨i,hi⟩ <;> simp [hs]

theorem rowPayload_append {m : ℕ} (b : ℕ) (xs ys : List (Fin m × SparseCode.F3)) :
    rowPayload b m (xs++ys)=rowPayload b m xs++rowPayload b m ys := by
  simp [rowPayload,List.flatten_append]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPortSemantic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BinaryArithmetic

theorem portIndex_vertex {r D : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (side : Bool) (v : Cayley.Cube r) (p : Fin D)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hp : BinaryArithmetic.toNat (d.stacks 14)=p.val) :
    portIndex d (vertexPairs v (shifts p))=(index shifts side v p).val := by
  rw [portIndex,hside,vertexPairs,shifted_vertexBits,vertexBits_value,hD,hp,index_value]

theorem coefficientValue_ternary (c : SparseCode.F3) (m : ℕ) :
    coefficientValue (decide (c=1)) (decide (c=2)) m=m*c.val := by
  fin_cases c
  · change coefficientValue false false m=m*0
    simp [coefficientValue]
  · change coefficientValue true false m=m*1
    simp [coefficientValue]
  · change coefficientValue false true m=m*2
    simp [coefficientValue]
    omega

theorem portAccum_vertex {r D t m : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (p : Fin D) (b : ℕ)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hm : BinaryArithmetic.toNat (d.stacks 4)=m) (hp : BinaryArithmetic.toNat (d.stacks 14)=p.val)
    (hb : (d.stacks 5).length=b) :
    portAccum d (decide (Q a p=1)) (decide (Q a p=2)) (vertexPairs v (shifts p))=
      (rowPayload b m (slot m shifts Q side v a p).toList).reverse++d.stacks 13 := by
  rw [portAccum,portIndex_vertex d shifts side v p hside hD hp,hm,hb,coefficientValue_ternary]
  by_cases h : (index shifts side v p).val  <  m <;>
    simp [h,slot,rowPayload]

theorem portAccum_prefix {r D t m : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i b : ℕ) (hi : i < D) (tail : List Bool)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hm : BinaryArithmetic.toNat (d.stacks 4)=m) (hp : BinaryArithmetic.toNat (d.stacks 14)=i)
    (hb : (d.stacks 5).length=b)
    (hacc : d.stacks 13=(rowPayload b m (prefixSlots m shifts Q side v a i)).reverse++tail) :
    portAccum d (decide (Q a ⟨i,hi⟩=1)) (decide (Q a ⟨i,hi⟩=2))
        (vertexPairs v (shifts ⟨i,hi⟩))=
      (rowPayload b m (prefixSlots m shifts Q side v a (i+1))).reverse++tail := by
  rw [portAccum_vertex d shifts Q side v a ⟨i,hi⟩ b hside hD hm hp hb,hacc,
    prefixSlots_succ m shifts Q side v a i hi,rowPayload_append,List.reverse_append]
  exact (List.append_assoc _ _ _).symm

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramInvariant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem LocalInvariant.width {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {a : Fin t} {b : ℕ} {qt st : List Bool} {i : ℕ} {d : Data}
    (h : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    portWidth d ≤ portWidth base+D := by
  have h2 := h.other 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h3 := h.other 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h4 := h.other 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 := h.other 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [portWidth,h2,h3,h4,h5]
  have hp := h.position
  have hl := h.indexLength
  omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem localStep_eval_oai {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
    (i : ℕ) (hi : i < D) (d : Data) (inv : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    ∃ n e, n ≤ 2000*(portWidth base+D+1)^2 ∧ Eval portStep n d e ∧
      e.stacks portLoop.counter=d.stacks portLoop.counter ∧
      LocalInvariant (m:=m) base shifts Q side v a b qt st (i+1) e := by
  let p : Fin D := ⟨i,hi⟩
  let pairs := vertexPairs v (shifts p)
  let qt1 := CodeSearchProgram.scalarFrames ((List.ofFn (Q a)).drop (i+1))++qt
  let st1 := shiftRows ((List.ofFn shifts).drop (i+1))++st
  have hq : d.stacks 0=Cell.frame (decide (Q a p=1)) (decide (Q a p=2))++qt1 := by
    rw [inv.source,scalar_drop_head (Q a) i hi]
    simp [p,qt1,List.append_assoc]
  have hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st1 := by
    rw [inv.shiftSource,shifts_drop_head shifts i hi]
    simp [p,pairs,st1,List.append_assoc]
  have hv : d.stacks 2=pairs.map Prod.fst := by
    rw [inv.other 2 (by decide) (by decide) (by decide) (by decide) (by decide),ready.vertex]
    simp [pairs]
  have work (j : Fin 64) (h17 : 17 ≤ j.val) (h41 : j.val ≤ 41) : d.stacks j=[] := by
    have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
    have h1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
    have h13 : j≠13 := by intro hne; have hv := congrArg Fin.val hne; change j.val=13 at hv; omega
    have h14 : j≠14 := by intro hne; have hv := congrArg Fin.val hne; change j.val=14 at hv; omega
    have h15 : j≠15 := by intro hne; have hv := congrArg Fin.val hne; change j.val=15 at hv; omega
    rw [inv.other j h0 h1 h13 h14 h15]
    exact ready.work j h17 h41
  have ha : ∀ j, d.stacks (arithmeticWork j)=[] := by
    intro j
    fin_cases j <;> exact work _ (by decide) (by decide)
  have hc : ∀ j : Fin 8, 2 ≤ j.val → d.stacks (compareStacks j)=[] := by
    intro j hj
    fin_cases j <;> simp_all [compareStacks]
  have hD : BinaryArithmetic.toNat (d.stacks 3)=D := by
    rw [inv.other 3 (by decide) (by decide) (by decide) (by decide) (by decide),ready.degree]
  have hm : BinaryArithmetic.toNat (d.stacks 4)=m := by
    rw [inv.other 4 (by decide) (by decide) (by decide) (by decide) (by decide),ready.modulus]
  have hb : (d.stacks 5).length=b := by
    rw [inv.other 5 (by decide) (by decide) (by decide) (by decide) (by decide),ready.width]
  have hmode : d.regs 12=side := (inv.registers 12 (by decide)).trans ready.mode
  obtain ⟨n,rf,he,hn,hregs⟩ := portStep_eval d (decide (Q a p=1)) (decide (Q a p=2))
    qt1 st1 pairs hq hs hv
    (work 17 (by decide) (by decide)) (work 18 (by decide) (by decide))
    (work 19 (by decide) (by decide)) (work 20 (by decide) (by decide))
    (work 21 (by decide) (by decide)) (work 22 (by decide) (by decide))
    (work 23 (by decide) (by decide)) (work 24 (by decide) (by decide))
    (work 25 (by decide) (by decide)) (work 41 (by decide) (by decide)) ha hc
    (by simpa [hm,hb] using ready.capacity)
  let e : Data := ⟨rf,portStacks d qt1 st1 (portAccum d (decide (Q a p=1)) (decide (Q a p=2)) pairs)⟩
  refine ⟨n,e,?_,he,?_,?_⟩
  · exact hn.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right inv.width 1) 2))
  · simp [e,portStacks,portLoop]
  · constructor
    · omega
    · intro j hj
      have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have h1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
      have h8 : j≠8 := by intro hne; have hv := congrArg Fin.val hne; change j.val=8 at hv; omega
      have h9 : j≠9 := by intro hne; have hv := congrArg Fin.val hne; change j.val=9 at hv; omega
      have hr := hregs j (by omega)
      have hr' : rf j=d.regs j := by
        simpa [coefficientRegs,h0,h1,h8,h9] using hr
      change rf j=base.regs j
      exact hr'.trans (inv.registers j hj)
    · simp [e,portStacks,qt1]
    · simp [e,portStacks,st1]
    · have hacc := portAccum_prefix d shifts Q side v a i b hi (base.stacks 13)
        hmode hD hm inv.index hb inv.accum
      simpa [e,portStacks,p,pairs] using hacc
    · have hv' := CounterPrograms.value_increment (d.stacks 14)
      simpa [e,portStacks,CounterPrograms.value_eq_toNat,inv.index] using hv'
    · have hl := CounterPrograms.ripple_length_le true (d.stacks 14)
      have old := inv.indexLength
      simp only [e,portStacks,Function.update_same]
      omega
    · intro j h0 h1 h13 h14 h15
      simpa [e,portStacks,h0,h1,h13,h14] using inv.other j h0 h1 h13 h14 h15

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.localStep_eval_oai

-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalSplitEmission.program
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:12:39.780663+00:00
-- url     : https://prove2.me/submissions/406fae97-a1de-4b08-a148-f7444e2b6e98

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring
import Definitions.Def_OAIQ222A004

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGModel
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat

lemma cache_project {α : Type} [Hashable α] [DecidableEq α]
    {ds : Array (AIG.Decl α)} (c : AIG.Cache α ds) (d : AIG.Decl α) :
    (c.get? d).map AIG.CacheHit.idx=c.val[d]? := by
  unfold AIG.Cache.get?
  split <;> simp_all
lemma nativeKey_injective {n : ℕ} : Function.Injective (nativeKey (n:=n)) := by
  rintro ⟨⟨a,ai⟩,⟨b,bi⟩⟩ ⟨⟨c,ci⟩,⟨d,di⟩⟩ h
  simp only [nativeKey,AIG.Decl.gate.injEq] at h
  have ha:=congrArg AIG.Fanin.gate h.1
  have hai:=congrArg AIG.Fanin.invert h.1
  have hb:=congrArg AIG.Fanin.gate h.2
  have hbi:=congrArg AIG.Fanin.invert h.2
  simp only [AIG.Fanin.gate_mk,AIG.Fanin.invert_mk] at *
  simp_all
lemma empty_rel (n : ℕ) : Rel empty (AIG.empty : AIG (Fin n)) := by
  constructor
  · rfl
  · intro k;simp [empty,lookup,AIG.empty,AIG.Cache.empty]
lemma constant_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    constant r (a.gate,a.invert)=AIG.getConstant g a := by
  unfold constant
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,Option.map_some,
    Option.getD_some]
  rw [AIG.getConstant]
  cases g.decls[a.gate]'a.hgate <;> rfl
lemma atom_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : Fin n) :
    EPRel (atom r i.val) (AIG.mkAtom g i) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · simpa only [atom,AIG.mkAtom,Array.toList_push,List.map_append,List.map_cons,List.map_nil,eraseDecl]
      using congrArg (fun ds=>ds++[Decl.atom i.val]) h.1
  · intro k;simpa only [atom,AIG.mkAtom,AIG.Cache.noUpdate] using h.2 k
  · simp only [atom,AIG.mkAtom,h.1,List.length_map,Array.length_toList]
lemma pushed_rel {n : ℕ} {r : Graph} {g g' : AIG (Fin n)} (h : Rel r g) (a b : Ref)
    (hd : g'.decls=g.decls.push (nativeKey (a,b)))
    (hc : g'.cache.val=g.cache.val.insert (nativeKey (a,b)) g.decls.size) :
    Rel (addGate r a b).1 g' := by
  constructor
  · simp only [addGate,hd,Array.toList_push,List.map_append,List.map_cons,List.map_nil,
      nativeKey,eraseDecl,AIG.Fanin.gate_mk,AIG.Fanin.invert_mk,h.1]
  · intro k
    simp only [addGate,lookup,hc,Std.HashMap.getElem?_insert]
    simp only [beq_iff_eq,(nativeKey_injective (n:=n)).eq_iff]
    by_cases hk:k=(a,b)
    · simp only [hk,↓reduceIte,h.1,List.length_map,Array.length_toList]
    · simp only [hk,Ne.symm hk,↓reduceIte,h.2]

lemma go_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (go r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (AIG.mkGateCached.go g i) := by
  let k : Key:=((i.lhs.gate,i.lhs.invert),(i.rhs.gate,i.rhs.invert))
  have hl : lookup k r.cache=(g.cache.get? (nativeKey k)).map AIG.CacheHit.idx :=
    (h.2 k).trans (cache_project _ _).symm
  unfold go AIG.mkGateCached.go
  dsimp only
  change EPRel (match lookup k r.cache with
    | some v => (r,(v,false))
    | none => _) _
  rw [hl]
  cases hc : g.cache.get? (nativeKey k) with
  | some hit =>
    simp only [Option.map_some]
    simp only [nativeKey,k] at hc
    simp only [hc]
    exact ⟨h,rfl⟩
  | none =>
    simp only [Option.map_none]
    simp only [nativeKey,k] at hc
    simp only [hc]
    rw [constant_eq h i.lhs,constant_eq h i.rhs]
    cases ha : AIG.getConstant g i.lhs with
    | some a =>
      cases a <;> cases hb : AIG.getConstant g i.rhs with
      | none => exact ⟨h,rfl⟩
      | some b => cases b <;> exact ⟨h,rfl⟩
    | none =>
      cases hb : AIG.getConstant g i.rhs with
      | some b => cases b <;> exact ⟨h,rfl⟩
      | none =>
        simp only [beq_iff_eq]
        by_cases he : i.lhs.gate=i.rhs.gate
        · simp only [he,↓reduceIte]
          by_cases hi : i.lhs.invert=i.rhs.invert <;>
            simp only [hi,↓reduceIte] <;> exact ⟨h,rfl⟩
        · simp only [he,↓reduceIte]
          refine ⟨pushed_rel h _ _ rfl ?_,?_⟩
          · simp only [AIG.Cache.insert];rfl
          · simp only [addGate,h.1,List.length_map,Array.length_toList]
lemma gate_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkGateCached i) := by
  unfold gate AIG.mkGateCached
  dsimp only
  split
  · exact go_rel h ⟨i.lhs,i.rhs⟩
  · exact go_rel h ⟨i.rhs,i.lhs⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
lemma or_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (orGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkOrCached i) := by
  have hs:=gate_rel h (i.invert true true)
  simpa only [EPRel,orGate,AIG.mkOrCached,AIG.BinaryInput.invert,AIG.Ref.not,
    AIG.Ref.flip,Bool.true_xor,notRef] using And.intro hs.1 (congrArg notRef hs.2)
lemma xor_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (xorGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkXorCached i) := by
  let s:=g.mkGateCached i
  let sr:=gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)
  have hs : EPRel sr s:=gate_rel h i
  let i':=i.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) g i)
  let t:=s.aig.mkGateCached (i'.invert true true)
  let tr:=gate sr.1 (notRef (i.lhs.gate,i.lhs.invert)) (notRef (i.rhs.gate,i.rhs.invert))
  have ht : EPRel tr t := by
    simpa only [tr,t,i',notRef,AIG.BinaryInput.cast,AIG.BinaryInput.invert,
      AIG.Ref.cast,AIG.Ref.flip,Bool.true_xor] using gate_rel hs.1 (i'.invert true true)
  let a:=s.ref.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) s.aig (i'.invert true true))
  have hh:=gate_rel ht.1 (⟨a.not,t.ref.not⟩ : AIG.BinaryInput t.aig)
  have ha : (a.not.gate,a.not.invert)=notRef sr.2 := by
    simpa only [a,AIG.Ref.cast,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef hs.2.symm
  have hb : (t.ref.not.gate,t.ref.not.invert)=notRef tr.2 := by
    simpa only [AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef ht.2.symm
  change EPRel (gate tr.1 (a.not.gate,a.not.invert) (t.ref.not.gate,t.ref.not.invert)) _ at hh
  rw [ha,hb] at hh
  exact hh

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGFullAdder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
lemma fullOut_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullOut r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderOut g i) := by
  let s:=g.mkXorCached ⟨i.lhs,i.rhs⟩
  have hs:=xor_rel h (⟨i.lhs,i.rhs⟩ : AIG.BinaryInput g)
  have hh:=xor_rel hs.1 (⟨s.ref,i.cin.cast (AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) ..)⟩ :
    AIG.BinaryInput s.aig)
  change EPRel (xorGate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) _ at hh
  rw [←hs.2] at hh
  exact hh
lemma fullCarry_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullCarry r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderCarry g i) := by
  let si : AIG.BinaryInput g:=⟨i.lhs,i.rhs⟩
  let s:=g.mkXorCached si
  have hs:=xor_rel h si
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨s.ref,i.cin.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht:=gate_rel hs.1 ti
  change EPRel (gate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) t at ht
  rw [←hs.2] at ht
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  let ui : AIG.BinaryInput t.aig:=⟨(i.lhs.cast hsub).cast hlor,(i.rhs.cast hsub).cast hlor⟩
  let u:=t.aig.mkAndCached ui
  have hu:=gate_rel ht.1 ui
  change EPRel (gate _ (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) u at hu
  let hror:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) t.aig ui
  have hh:=or_rel hu.1 (⟨t.ref.cast hror,u.ref⟩ : AIG.BinaryInput u.aig)
  change EPRel (orGate _ (t.ref.gate,t.ref.invert) (u.ref.gate,u.ref.invert)) _ at hh
  rw [←ht.2,←hu.2] at hh
  exact hh
lemma full_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    Rel (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).1
      (mkFullAdder g i).aig ∧
    (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).2 =
      (((mkFullAdder g i).out.gate,(mkFullAdder g i).out.invert),
        ((mkFullAdder g i).cout.gate,(mkFullAdder g i).cout.invert)) := by
  have ho:=fullOut_rel h i
  have hk:=fullCarry_rel ho.1 (i.cast (AIG.LawfulOperator.le_size (f:=mkFullAdderOut) g i))
  exact ⟨hk.1,congrArg₂ Prod.mk ho.2 hk.2⟩

end ExactQuantumFactoring.NativeAIG
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

lemma known_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    known r (a.gate,a.invert) = (match g.decls[a.gate]'a.hgate with | .false=>true | _=>false) := by
  unfold known
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,
    Option.map_some,Option.getD_some]
  cases g.decls[a.gate]'a.hgate <;> rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
lemma countKnown_go_eq {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (v : AIG.RefVec g w) (idx acc : ℕ) :
    AIG.RefVec.countKnown.go g v idx acc = acc+countKnown r ((eraseVec v).drop idx) := by
  rw [AIG.RefVec.countKnown.go]
  by_cases hi : idx<w
  · rw [dite_eq_left hi]
    have hl : idx<(eraseVec v).length:=by simpa only [eraseVec_length] using hi
    rw [List.drop_eq_getElem_cons hl,countKnown_cons]
    have he : (eraseVec v)[idx]'hl=((v.get idx hi).gate,(v.get idx hi).invert) := by
      simp [eraseVec]
    rw [he,known_eq hr]
    simp only [refVec_get_gate]
    cases g.decls[v.refs[idx].gate]'(v.hrefs hi) <;>
      simp only [Bool.false_eq_true,↓reduceIte] <;>
      rw [countKnown_go_eq hr v (idx+1)] <;> omega
  · rw [dite_eq_right hi,List.drop_eq_nil_of_le (by simpa only [eraseVec_length] using Nat.le_of_not_gt hi)]
    simp only [countKnown_nil,Nat.add_zero]
termination_by w-idx
@[simp] lemma countKnown_eq {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (v : AIG.RefVec g w) : AIG.RefVec.countKnown g v=countKnown r (eraseVec v) := by
  simpa only [AIG.RefVec.countKnown,List.drop_zero,Nat.zero_add] using countKnown_go_eq hr v 0 0

lemma addLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (cin : AIG.Ref g)
    (out : AIG.RefVec g curr) :
    VecRel (addLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (cin.gate,cin.invert) (eraseVec out))
      (blastAdd.go g lhs rhs curr hc cin out) := by
  rw [blastAdd.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,addLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let i : FullAdderInput g:=⟨lhs.get curr hi,rhs.get curr hi,cin⟩
    let s:=mkFullAdder g i
    have hs:=full_rel hr i
    have hh:=addLoop_rel hs.1 (lhs.cast s.hle) (rhs.cast s.hle) (curr+1) (by omega)
      s.cout ((out.cast s.hle).push s.out)
    simp only [eraseVec_cast,eraseVec_push] at hh
    rw [hs.2]
    exact hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,addLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma addBlast_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (addBlast r (eraseVec i.lhs) (eraseVec i.rhs)) (blastAdd.blast g i) := by
  cases i with
  | mk lhs rhs=>
   simpa only [blastAdd.blast,addBlast,eraseVec_length,Nat.sub_zero,AIG.mkConstCached,
     AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty] using
    addLoop_rel hr lhs rhs 0 (Nat.zero_le _) (g.mkConstCached false) (.emptyWithCapacity w)
lemma add_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (add r (eraseVec i.lhs) (eraseVec i.rhs)) (blastAdd g i) := by
  cases i with
  | mk lhs rhs=>
    unfold add blastAdd
    rw [countKnown_eq hr,countKnown_eq hr]
    split
    · exact addBlast_rel hr ⟨lhs,rhs⟩
    · exact addBlast_rel hr ⟨rhs,lhs⟩
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionModel
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_assign _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_band _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bit _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bnot _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_bxor _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_constant _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_mux _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_rewire _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.BooleanNetwork.eval_rewire _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
lemma eraseNode_map {n m : ℕ} (o : BoolNode n) (f : Fin n→Fin m) (g : ℕ→ℕ)
    (h : ∀i,(f i).val=g i.val) : eraseNode (o.map f)=(eraseNode o).map g := by
  cases o <;> simp only [BoolNode.map,eraseNode,Node.map,h]
lemma attachIndex_input {m k : ℕ} (ρ : Fin m→Fin k) (i : Fin m) :
    attachIndex ρ i.val=(ρ i).val := dite_eq_left i.isLt
lemma attachIndex_work {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) (h : m ≤ i) :
    attachIndex ρ i=k+(i-m) := dite_eq_right (by omega)
lemma attach_output {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l)
    (i : Fin l) : ((a.attach ρ b).2.2 i).val=attachIndex ρ i.val := by
  induction b with
  | input=>exact (attachIndex_input ρ i).symm
  | @add l b o ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [BoolNet.attach,Fin.snoc_last,Fin.val_last]
      rw [attachIndex_work ρ l b.input_le]
      have hw:=(a.attach ρ b).2.1.width_eq
      have hc:=BoolNet.attach_count a ρ b
      have hb:=b.width_eq
      rw [hc] at hw
      have ha:=a.width_eq
      omega
    · simp only [BoolNet.attach,Fin.snoc_castSucc,Fin.val_castSucc]
      exact ih j
lemma attach_erase {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l) :
    eraseNet (a.attach ρ b).2.1=eraseNet a++(eraseNet b).map (Node.map (attachIndex ρ)) := by
  induction b with
  | input=>simp only [BoolNet.attach,eraseNet,List.map_nil,List.append_nil]
  | add b o ih=>
    simp only [BoolNet.attach,eraseNet,List.map_append,List.map_singleton]
    rw [ih,List.append_assoc,eraseNode_map o _ _ (attach_output a ρ b)]

lemma attachRawIndex_ofFn {m k : ℕ} (ρ : Fin m→Fin k) :
    attachRawIndex k (List.ofFn (fun i=>(ρ i).val))=attachIndex ρ := by
  funext i
  unfold attachRawIndex attachIndex
  simp only [List.length_ofFn]
  split_ifs with h
  · rw [List.headD_eq_head?_getD,List.head?_drop]
    simp [h]
  · rfl

lemma erase_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    erase (a.comp b)=comp (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  simp only [erase,BooleanNetwork.comp,comp,hw,attachRawIndex_ofFn,attach_erase]
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  exact attach_output a.net a.output b.net (b.output i)

lemma erase_select {n m : ℕ} (f : Fin m→Fin n) :
    erase (BooleanNetwork.select f)=select n (List.ofFn (fun i=>(f i).val)) := rfl

lemma erase_node {n : ℕ} (o : BoolNode n) : erase (BooleanNetwork.node o)=node n (eraseNode o) := by
  simp [erase,BooleanNetwork.node,eraseNet,node,List.ofFn_succ]
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPair
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

lemma pairIndex_eq {n k : ℕ} (h : n ≤ k) :
    pairIndex n k=attachIndex (fun i : Fin n=>i.castLE h) := by
  funext i
  unfold pairIndex attachIndex
  split_ifs <;> rfl

lemma erase_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    erase (a.pair b)=pair (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  let ρ : Fin n→Fin a.width:=fun i=>i.castLE a.net.input_le
  simp only [erase,BooleanNetwork.pair,pair,hw,pairIndex_eq a.net.input_le,attach_erase]
  congr 1
  have he : (fun i=>(Fin.append (fun j=>(a.output j).castLE (a.net.attach_le ρ b.net))
      ((a.net.attach ρ b.net).2.2 ∘ b.output) i).val)=
      Fin.append (fun j=>(a.output j).val)
        (fun j=>((a.net.attach ρ b.net).2.2 (b.output j)).val) := by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp
  rw [he,List.ofFn_fin_append,List.map_ofFn]
  congr 2
  funext i
  exact attach_output a.net ρ b.net (b.output i)

end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma erase_bit {n : ℕ} (i : Fin n) : erase (BooleanNetwork.bit i)=bit n i.val := by
  simp [BooleanNetwork.bit,erase_select,bit,List.ofFn_succ]
lemma erase_constant {n : ℕ} (b : Bool) : erase (BooleanNetwork.constant (n:=n) b)=constant n b:=
  erase_node _
lemma erase_bnot {n : ℕ} (a : BooleanNetwork n 1) : erase a.bnot=bnot (erase a):=by
  rw [BooleanNetwork.bnot,erase_comp,erase_node];rfl
lemma erase_band {n : ℕ} (a b : BooleanNetwork n 1) : erase (a.band b)=band (erase a) (erase b):=by
  rw [BooleanNetwork.band,erase_comp,erase_pair,erase_node];rfl
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma pairPack_inputs (a b : Pack) : (pairPack a b).val.value.inputs=a.val.value.inputs:=by
  unfold pairPack;split <;> rfl
lemma pairPack_value (a b : Pack) (h : a.val.value.inputs=b.val.value.inputs) :
    (pairPack a b).val.value=pair a.val.value b.val.value:=by simp only [pairPack,ite_eq_left h]
lemma compPack_value (a b : Pack) (h : a.val.value.outputs.length=b.val.value.inputs) :
    (compPack a b).val.value=comp a.val.value b.val.value:=by simp only [compPack,ite_eq_left h]
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionRewire
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma erase_rewireBy {n m l : ℕ} (a : BooleanNetwork n m) (f : Fin l→Fin m) :
    rewireBy (erase a) (List.ofFn (fun i=>(f i).val))=erase (a.rewire f):=by
  unfold rewireBy erase BooleanNetwork.rewire
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [(f i).isLt]
lemma rewirePack_value {n m l : ℕ} (a : Pack) (b : BooleanNetwork n m) (f : Fin l→Fin m)
    (h : a.val.value=erase b) :
    (rewirePack a (List.ofFn (fun i=>(f i).val))).val.value=erase (b.rewire f):=by
  change rewireBy a.val.value _=_
  rw [h,erase_rewireBy]
lemma identityPack_value (n : ℕ) : (identityPack n).val.value=erase (BooleanNetwork.select (id : Fin n→Fin n)):=by
  rw [erase_select]
  change select n (List.range n)=select n (List.ofFn (fun i:Fin n=>i.val))
  congr 1
  exact (ofFn_val_range n).symm

lemma assignPack_value {n : ℕ} (i : Fin n) (a : Pack) (v : BooleanNetwork n 1) (ha : a.val.value=erase v) :
    (assignPack n i.val a).val.value=erase (BooleanNetwork.assign i v):=by
  have hp : (pairPack (identityPack n) a).val.value=erase ((BooleanNetwork.select id).pair v):=by
    rw [pairPack_value,identityPack_value,ha,erase_pair]
    rw [identityPack_value,ha];rfl
  have hi : ((List.range n).map (fun j=>if j=i.val then n else j))=
      List.ofFn (fun j:Fin n=>(if j=i then Fin.natAdd n (0 : Fin 1) else j.castAdd 1).val):=by
    rw [←ofFn_val_range,List.map_ofFn]
    congr 1
    funext j
    by_cases h : j=i
    · subst j;simp
    · have hn : j.val≠i.val:=fun hh=>h (Fin.ext hh)
      simp [h,hn]
  rw [assignPack,hi,rewirePack_value _ _ _ hp]
  rfl
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionVector
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma vectorPack_inputs (n : ℕ) (xs : List Pack) : (vectorPack n xs).val.value.inputs=n:=by
  unfold vectorPack
  suffices ∀a:Pack,(xs.foldl pairPack a).val.value.inputs=a.val.value.inputs by exact this _
  intro a
  induction xs generalizing a with
  | nil=>rfl
  | cons b xs ih=>rw [List.foldl_cons,ih,pairPack_inputs]
lemma vectorPack_value {n m : ℕ} (f : Fin m→BooleanNetwork n 1) (p : Fin m→Pack)
    (hp : ∀i,(p i).val.value=erase (f i)) :
    (vectorPack n (List.ofFn p)).val.value=erase (BooleanNetwork.vector f):=by
  induction m with
  | zero=>rfl
  | succ m ih=>
    rw [BooleanNetwork.vector,erase_pair,List.ofFn_succ_last]
    change ((List.ofFn (fun i:Fin m=>p i.castSucc)++[p (Fin.last m)]).foldl pairPack (emptyAt n)).val.value=_
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (pairPack (vectorPack n (List.ofFn fun i:Fin m=>p i.castSucc)) (p (Fin.last m))).val.value=_
    rw [pairPack_value,ih (fun i=>f i.castSucc) (fun i=>p i.castSucc) (fun i=>hp i.castSucc),hp]
    rw [vectorPack_inputs,hp];rfl
lemma bitPack_value {n : ℕ} (i : Fin n) : (bitPack n i.val).val.value=erase (BooleanNetwork.bit i):=by
  rw [erase_bit]
  simp only [bitPack,selectPack,min_eq_right (Nat.le_of_lt i.isLt),bit]
lemma constantPack_value (n : ℕ) (b : Bool) : (constantPack n b).val.value=erase (BooleanNetwork.constant (n:=n) b):=by
  rw [erase_constant];rfl
lemma bnotPack_value {n : ℕ} (a : Pack) (f : BooleanNetwork n 1) (h : a.val.value=erase f) :
    (bnotPack a).val.value=erase f.bnot:=by
  rw [erase_bnot,bnotPack,compPack_value]
  · rw [h];rfl
  · rw [h];simp [erase,nodePack,node]
lemma bandPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (bandPack a b).val.value=erase (f.band g):=by
  have hp : (pairPack a b).val.value=erase (f.pair g):=by
    rw [pairPack_value,ha,hb,erase_pair]
    rw [ha,hb];rfl
  rw [erase_band,bandPack,compPack_value]
  · rw [hp,erase_pair];rfl
  · rw [hp];simp [erase,nodePack,node]
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGNetworkEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat BooleanNetwork
open NetworkEmission

lemma faninPack_value {n : ℕ} (g : AIG (Fin n)) (f : AIG.Fanin) :
    (faninPack n g.decls.size (f.gate,f.invert)).val.value=erase (AIGCompiler.faninNet g f):=by
  unfold faninPack AIGCompiler.faninNet
  by_cases h : f.gate<g.decls.size
  · simp only [h,↓reduceIte,↓reduceDIte]
    have hv:=bitPack_value (AIGCompiler.graphWire g ⟨f.gate,h⟩)
    change (bitPack (n+g.decls.size) (n+f.gate)).val.value=_ at hv
    cases f.invert
    · exact hv
    · exact bnotPack_value _ _ hv
  · simp only [h,↓reduceIte,↓reduceDIte]
    cases f.invert
    · exact constantPack_value _ _
    · exact bnotPack_value _ _ (constantPack_value _ _)

lemma nodePack_value {n : ℕ} (g : AIG (Fin n)) (i : Fin g.decls.size) :
    (nodePack n g.decls.size (NativeAIG.eraseDecl g.decls[i.val])).val.value=
      erase (AIGCompiler.nodeNet g i):=by
  unfold AIGCompiler.nodeNet
  cases h : g.decls[i.val] with
  | false=>exact constantPack_value _ _
  | atom v=>exact bitPack_value (v.castAdd g.decls.size)
  | gate a b=>exact bandPack_value _ _ _ _ (faninPack_value g a) (faninPack_value g b)

lemma partialPack_value {n : ℕ} {r : NativeAIG.Graph} {g : AIG (Fin n)}
    (hr : NativeAIG.Rel r g) (k : ℕ) (hk : k≤g.decls.size) :
    (partialPack n r.decls k).val.value=erase (AIGCompiler.partialGraph g k hk):=by
  have hl : r.decls.length=g.decls.size:=by rw [hr.1,List.length_map,Array.length_toList]
  induction k with
  | zero=>simpa only [partialPack,List.range_zero,List.map_nil,List.foldl_nil,hl,AIGCompiler.partialGraph]
      using identityPack_value (n+g.decls.size)
  | succ k ih=>
    have hips:=ih (by omega)
    have hd : (r.decls.drop k).headD .zero=NativeAIG.eraseDecl g.decls[k]:=by
      rw [List.headD_eq_head?_getD,List.head?_drop,hr.1,List.getElem?_map,Array.getElem?_toList,
        Array.getElem?_eq_getElem (by omega),Option.map_some,Option.getD_some]
    have hn:=assignPack_value (AIGCompiler.graphWire g ⟨k,by omega⟩) _ _ (nodePack_value g ⟨k,by omega⟩)
    simp only [AIGCompiler.graphWire,Fin.val_natAdd] at hn
    unfold partialPack
    rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (compPack (partialPack n r.decls k) (assignPack (n+r.decls.length) (n+k)
      (nodePack n r.decls.length ((r.decls.drop k).headD .zero)))).val.value=_
    rw [compPack_value]
    · rw [hips,hl,hd,hn]
      exact (erase_comp _ _).symm
    · rw [hips,hl,hd,hn]
      simp [erase]

lemma padPack_value (n gs : ℕ) : (padPack n gs).val.value=erase (BooleanNetwork.padRight n gs):=by
  unfold padPack BooleanNetwork.padRight
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  by_cases h : i.val<n
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact bitPack_value ⟨i.val,h⟩
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact constantPack_value _ _

lemma compilePack_value {n m : ℕ} {r : NativeAIG.Graph} {g : AIG (Fin n)}
    (hr : NativeAIG.Rel r g) (refs : Fin m→AIG.Ref g) :
    (compilePack n r.decls (List.ofFn (fun i=>((refs i).gate,(refs i).invert)))).val.value=
      erase (AIGCompiler.compile g refs):=by
  have hl : r.decls.length=g.decls.size:=by rw [hr.1,List.length_map,Array.length_toList]
  have hp:=partialPack_value hr g.decls.size le_rfl
  have hs : (compPack (padPack n r.decls.length) (partialPack n r.decls r.decls.length)).val.value=
      erase ((BooleanNetwork.padRight n g.decls.size).comp (AIGCompiler.partialGraph g g.decls.size le_rfl)):=by
    rw [compPack_value]
    · rw [hl,padPack_value,hp,erase_comp]
    · rw [hl,padPack_value,hp];simp [erase]
  have hv : (vectorPack (n+r.decls.length) ((List.ofFn (fun i=>((refs i).gate,(refs i).invert))).map
      (faninPack n r.decls.length))).val.value=
      erase (BooleanNetwork.vector (fun i=>AIGCompiler.faninNet g (.mk (refs i).gate (refs i).invert))):=by
    rw [hl,List.map_ofFn]
    apply vectorPack_value
    intro i
    dsimp only [Function.comp_apply]
    simpa only [AIG.Fanin.gate_mk,AIG.Fanin.invert_mk] using
      faninPack_value g (.mk (refs i).gate (refs i).invert)
  unfold compilePack
  rw [compPack_value]
  · rw [hs,hv];exact (erase_comp _ _).symm
  · rw [hs,hv];simp [erase]
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGInputs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

lemma refVector_get {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) (i : ℕ) (hi : i < w) :
    (refVector f).get i hi = f ⟨i,hi⟩ := by
  simp [refVector, AIG.RefVec.get, AIG.Fanin.gate_mk, AIG.Fanin.invert_mk]

end ExactQuantumFactoring.AIGCompiler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGIf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

lemma if_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.TernaryInput g) :
    EPRel (ifGate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkIfCached i) := by
  let si : AIG.BinaryInput g:=⟨i.discr,i.lhs⟩
  let s:=g.mkAndCached si
  have hs:=gate_rel h si
  change EPRel (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)) s at hs
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨(i.discr.cast hsub).not,i.rhs.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht : EPRel (gate (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)).1
      (notRef (i.discr.gate,i.discr.invert)) (i.rhs.gate,i.rhs.invert)) t := by
    simpa only [si,s,ti,t,AIG.mkAndCached,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,AIG.Ref.cast,notRef] using gate_rel hs.1 ti
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  have hh:=or_rel ht.1 (⟨s.ref.cast hlor,t.ref⟩ : AIG.BinaryInput t.aig)
  change EPRel (orGate _ (s.ref.gate,s.ref.invert) (t.ref.gate,t.ref.invert)) _ at hh
  rw [←hs.2,←ht.2] at hh
  exact hh
lemma ifLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (d : AIG.Ref g) (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w)
    (out : AIG.RefVec g curr) :
    VecRel (ifLoop (w-curr) r (d.gate,d.invert) (eraseVec lhs) (eraseVec rhs) curr (eraseVec out))
      (AIG.RefVec.ite.go g curr hc d lhs rhs out) := by
  rw [AIG.RefVec.ite.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,ifLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let i : AIG.TernaryInput g:=⟨d,lhs.get curr hi,rhs.get curr hi⟩
    let s:=g.mkIfCached i
    have hs:=if_rel hr i
    let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkIfCached) g i
    have hh:=ifLoop_rel hs.1 (d.cast hsub) (lhs.cast hsub) (rhs.cast hsub)
      (curr+1) (by omega) ((out.cast hsub).push s.ref)
    simp only [eraseVec_cast,eraseVec_push,AIG.Ref.cast] at hh
    rw [hs.2]
    exact hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,ifLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma ifVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.RefVec.IfInput g w) :
    VecRel (ifVec r (i.discr.gate,i.discr.invert) (eraseVec i.lhs) (eraseVec i.rhs))
      (AIG.RefVec.ite g i) := by
  cases i with
  | mk d lhs rhs=>
    simpa only [AIG.RefVec.ite,ifVec,eraseVec_length,Nat.sub_zero,
      AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty] using
      ifLoop_rel hr d lhs rhs 0 (Nat.zero_le _) (.emptyWithCapacity w)

end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma shiftLoop_value (k : ℕ) (xs : List Ref) (d i : ℕ) (out : List Ref) :
    shiftLoop k xs d i out=out++(List.range' i k).map (shiftBit xs d) := by
  induction k generalizing i out with
  | zero=>simp [shiftLoop]
  | succ k ih=>simp [shiftLoop,ih,List.range'_succ,List.append_assoc]
lemma shiftLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d curr : ℕ) (hc : curr ≤ w) (out : AIG.RefVec g curr) :
    VecRel (r,shiftLoop (w-curr) (eraseVec xs) d curr (eraseVec out))
      (blastShiftLeftConst.go g xs d curr hc out) := by
  rw [blastShiftLeftConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,shiftLoop]
    by_cases he : curr<d
    · rw [dite_eq_left he,shiftBit,ite_eq_left he]
      have hh:=shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (g.mkConstCached false))
      simpa only [eraseVec_push,AIG.mkConstCached] using hh
    · rw [dite_eq_right he,shiftBit,ite_eq_right he,eraseVec_get xs (by omega)]
      simpa only [eraseVec_push] using
        shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (xs.get (curr-d) (by omega)))
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,shiftLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma shift_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d : ℕ) :
    VecRel (r,shift (eraseVec xs) d) (blastShiftLeftConst g ⟨xs,d⟩) := by
  simpa only [blastShiftLeftConst,shiftLoop_value,eraseVec_empty,List.nil_append,
    AIG.RefVec.emptyWithCapacity_eq,Nat.sub_zero,List.range_eq_range',shift,eraseVec_length] using
    shiftLoop_rel hr xs d 0 (Nat.zero_le _) (.emptyWithCapacity w)

lemma const_zero_go {n w : ℕ} (g : AIG (Fin n)) (curr : ℕ) (hc : curr ≤ w)
    (out : AIG.RefVec g curr) :
    eraseVec (blastConst.go g (0 : BitVec w) curr out hc)=
      eraseVec out++List.replicate (w-curr) (0,false) := by
  rw [blastConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi,const_zero_go,eraseVec_push]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    simp only [AIG.mkConstCached]
    rw [hd,List.replicate_succ]
    simp [List.append_assoc]
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    simp
termination_by w-curr
lemma const_zero {n w : ℕ} (g : AIG (Fin n)) :
    eraseVec (blastConst g (0 : BitVec w))=List.replicate w (0,false) := by
  simpa only [blastConst,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,Nat.sub_zero]
    using const_zero_go g 0 (Nat.zero_le _) (.emptyWithCapacity w)

end ExactQuantumFactoring.NativeAIG

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma isZero_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (a : AIG.Ref g) :
    isZero r (a.gate,a.invert)=g.isConstant a false := by
  rw [isZero,constant_eq hr,AIG.isConstant,AIG.getConstant]
  cases g.decls[a.gate]'a.hgate <;> simp

lemma mulLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (acc : AIG.RefVec g w) :
    VecRel (mulLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (eraseVec acc))
      (blastMul.go g lhs rhs curr acc) := by
  rw [blastMul.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,mulLoop,eraseVec_get rhs hi,isZero_eq hr]
    split
    · exact mulLoop_rel hr lhs rhs (curr+1) acc
    · let sh:=blastShiftLeftConst g ⟨lhs,curr⟩
      have hsh:=shift_rel hr lhs curr
      let h₁:=AIG.LawfulVecOperator.le_size (f:=blastShiftLeftConst) g (⟨lhs,curr⟩ : AIG.ShiftTarget g w)
      let ai : AIG.BinaryRefVec sh.aig w:=⟨acc.cast h₁,sh.vec⟩
      let ad:=blastAdd sh.aig ai
      have had:=add_rel hsh.1 ai
      change VecRel (add r (eraseVec acc) (eraseVec sh.vec)) ad at had
      rw [←hsh.2] at had
      let h₂:=AIG.LawfulVecOperator.le_size (f:=blastAdd) sh.aig ai
      let ii : AIG.RefVec.IfInput ad.aig w:=⟨((rhs.cast h₁).cast h₂).get curr hi,ad.vec,(acc.cast h₁).cast h₂⟩
      let it:=AIG.RefVec.ite ad.aig ii
      have hit:=ifVec_rel had.1 ii
      change VecRel (ifVec _ ((rhs.get curr hi).gate,(rhs.get curr hi).invert)
        (eraseVec ad.vec) (eraseVec acc)) it at hit
      rw [←had.2] at hit
      let h₃:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) ad.aig ii
      have hh:=mulLoop_rel hit.1 (((lhs.cast h₁).cast h₂).cast h₃)
        (((rhs.cast h₁).cast h₂).cast h₃) (curr+1) it.vec
      simp only [eraseVec_cast] at hh
      rw [←hit.2] at hh
      exact hh
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi),mulLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma mulBlast_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (mulBlast r (eraseVec i.lhs) (eraseVec i.rhs)) (blastMul.blast g i) := by
  cases i with
  | mk lhs rhs=>
    unfold mulBlast blastMul.blast
    rw [eraseVec_length]
    by_cases hw : w=0
    · rw [ite_eq_left hw,dite_eq_left hw]
      subst w
      exact ⟨hr,rfl⟩
    · rw [ite_eq_right hw,dite_eq_right hw]
      have hw' : 0<w:=Nat.pos_of_ne_zero hw
      let ii : AIG.RefVec.IfInput g w:=⟨rhs.get 0 hw',lhs,blastConst g 0⟩
      let it:=AIG.RefVec.ite g ii
      have hit:=ifVec_rel hr ii
      change VecRel (ifVec r ((rhs.get 0 hw').gate,(rhs.get 0 hw').invert)
        (eraseVec lhs) (eraseVec (blastConst g (0 : BitVec w)))) it at hit
      rw [const_zero] at hit
      have hget:=eraseVec_get rhs hw'
      simp only [List.drop_zero] at hget
      rw [hget]
      let h₁:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) g ii
      have hh:=mulLoop_rel hit.1 (lhs.cast h₁) (rhs.cast h₁) 1 it.vec
      simp only [eraseVec_cast] at hh
      rw [←hit.2] at hh
      exact hh
lemma mul_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (mul r (eraseVec i.lhs) (eraseVec i.rhs)) (blastMul g i) := by
  cases i with
  | mk lhs rhs=>
    unfold mul blastMul
    rw [countKnown_eq hr,countKnown_eq hr]
    split
    · exact mulBlast_rel hr ⟨lhs,rhs⟩
    · exact mulBlast_rel hr ⟨rhs,lhs⟩
end ExactQuantumFactoring.NativeAIG

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGNot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma notMap_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++notVec ((eraseVec xs).drop curr))
      (AIG.RefVec.map.go g curr hc out xs AIG.mkNotCached) := by
  rw [AIG.RefVec.map.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hh:=notMap_rel hr xs (curr+1) (by omega) (out.push (xs.get curr hi).not)
    have hl : curr<(eraseVec xs).length:=by simpa only [eraseVec_length] using hi
    rw [List.drop_eq_getElem_cons hl]
    have he : (eraseVec xs)[curr]'hl=((xs.get curr hi).gate,(xs.get curr hi).invert):=by simp [eraseVec]
    rw [he]
    simpa only [notVec,List.map_cons,eraseVec_push,AIG.mkNotCached,AIG.RefVec.cast,AIG.RefVec.cast',AIG.Ref.not,AIG.Ref.flip,
      Bool.true_xor,notRef,List.append_assoc,List.singleton_append] using hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [List.drop_eq_nil_of_le (by rw [eraseVec_length])]
    simp only [notVec,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma notVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,notVec (eraseVec xs)) (blastNot g xs) := by
  simpa only [blastNot,AIG.RefVec.map,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,
    List.nil_append,List.drop_zero] using notMap_rel hr xs 0 (Nat.zero_le _) (.emptyWithCapacity w)
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma const_go {n w : ℕ} (g : AIG (Fin n)) (v : BitVec w) (curr : ℕ) (hc : curr≤w)
    (out : AIG.RefVec g curr) :
    eraseVec (blastConst.go g v curr out hc)=
      eraseVec out++(List.range' curr (w-curr)).map (fun i=>(0,v.getLsbD i)) := by
  rw [blastConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi,const_go,eraseVec_push]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,List.range'_succ,List.map_cons]
    simp only [AIG.mkConstCached,List.append_assoc,List.singleton_append]
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    simp
termination_by w-curr
lemma const_erase {n w : ℕ} (g : AIG (Fin n)) (v : BitVec w) :
    eraseVec (blastConst g v)=(List.range w).map (fun i=>(0,v.getLsbD i)) := by
  simpa only [blastConst,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,Nat.sub_zero,
    List.range_eq_range'] using const_go g v 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma const_one {n w : ℕ} (g : AIG (Fin n)) :
    eraseVec (blastConst g (BitVec.ofNat w 1))=oneVec w := by
  rw [const_erase,oneVec]
  apply List.map_congr_left
  intro i hi
  have hw : 0<w:=by have:=List.mem_range.mp hi;omega
  simp [BitVec.getLsbD_one,hw]
lemma neg_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (neg r (eraseVec xs)) (blastNeg g xs) := by
  let nt:=blastNot g xs
  have hn:=notVec_rel hr xs
  have hh:=add_rel hn.1 ⟨nt.vec,blastConst nt.aig (BitVec.ofNat w 1)⟩
  rw [const_one,←hn.2] at hh
  simpa only [neg,eraseVec_length,blastNeg,nt] using hh
lemma sub_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) : VecRel (sub r (eraseVec i.lhs) (eraseVec i.rhs)) (blastSub g i) := by
  let nr:=blastNeg g i.rhs
  have hn:=neg_rel hr i.rhs
  let hle:=AIG.LawfulVecOperator.le_size (f:=blastNeg) g i.rhs
  have hh:=add_rel hn.1 ⟨i.lhs.cast hle,nr.vec⟩
  simpa only [eraseVec_cast,nr,←hn.2,sub,blastSub] using hh
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGCarry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma carryLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (cin : AIG.Ref g) :
    EPRel (carryLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (cin.gate,cin.invert))
      (mkOverflowBit.go g lhs rhs curr cin) := by
  rw [mkOverflowBit.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,carryLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let ii : FullAdderInput g:=⟨lhs.get curr hi,rhs.get curr hi,cin⟩
    let cc:=mkFullAdderCarry g ii
    have hh:=fullCarry_rel hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=mkFullAdderCarry) g ii
    have ht:=carryLoop_rel hh.1 (lhs.cast hle) (rhs.cast hle) (curr+1) cc.ref
    simp only [eraseVec_cast] at ht
    rw [←hh.2] at ht
    exact ht
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi),carryLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma overflow_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : OverflowInput g) :
    EPRel (overflow r (eraseVec i.vec.lhs) (eraseVec i.vec.rhs) (i.cin.gate,i.cin.invert))
      (mkOverflowBit g i) := by
  cases i with
  | mk w v c=>
    simpa only [overflow,eraseVec_length,Nat.sub_zero,mkOverflowBit] using carryLoop_rel hr v.lhs v.rhs 0 c
lemma ult_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    EPRel (ult r (eraseVec i.lhs) (eraseVec i.rhs)) (Std.Tactic.BVDecide.BVPred.mkUlt g i) := by
  let nt:=blastNot g i.rhs
  have hn:=notVec_rel hr i.rhs
  let hle:=AIG.LawfulVecOperator.le_size (f:=blastNot) g i.rhs
  let oi : OverflowInput nt.aig:=⟨w,⟨i.lhs.cast hle,nt.vec⟩,nt.aig.mkConstCached true⟩
  have hh:=overflow_rel hn.1 oi
  change EPRel (overflow r (eraseVec i.lhs) (eraseVec nt.vec) (0,true)) (mkOverflowBit nt.aig oi) at hh
  rw [←hn.2] at hh
  refine ⟨hh.1,?_⟩
  simpa only [notRef,Std.Tactic.BVDecide.BVPred.mkUlt,AIG.mkNotCached,AIG.Ref.not,AIG.Ref.flip,
    Bool.true_xor,ult] using congrArg notRef hh.2
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma eraseVec_getD {n w : ℕ} {g : AIG (Fin n)} (xs : AIG.RefVec g w) (i : ℕ) :
    ((eraseVec xs).drop i).headD (0,false)=
    ((xs.getD i (g.mkConstCached false)).gate,(xs.getD i (g.mkConstCached false)).invert) := by
  by_cases hi : i<w
  · rw [AIG.RefVec.get_in_bound _ _ _ hi,eraseVec_get xs hi]
  · rw [AIG.RefVec.get_out_bound _ _ _ (by omega),List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
    rfl
lemma eraseVec_append {n w v : ℕ} {g : AIG (Fin n)} (lhs : AIG.RefVec g w) (rhs : AIG.RefVec g v) :
    eraseVec (lhs.append rhs)=eraseVec lhs++eraseVec rhs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [eraseVec,List.getElem_ofFn]
    rw [AIG.RefVec.get_append,List.getElem_append]
    by_cases hh : i<w
    · simp only [List.length_ofFn,hh,dite_eq_left,List.getElem_ofFn]
    · simp [hh]

lemma extend_go_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤v) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++(List.range' curr (v-curr)).map (fun i=>((eraseVec xs).drop i).headD (0,false)))
      (blastZeroExtend.go g w xs v curr hc out) := by
  rw [blastZeroExtend.go]
  by_cases hi : curr<v
  · rw [dite_eq_left hi]
    have hd : v-curr=(v-(curr+1))+1:=by omega
    rw [hd,List.range'_succ,List.map_cons]
    by_cases he : curr<w
    · rw [dite_eq_left he,eraseVec_get xs he]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (xs.get curr he))
    · rw [dite_eq_right he,List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append,AIG.mkConstCached,List.headD_nil] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (g.mkConstCached false))
  · rw [dite_eq_right hi]
    have he : curr=v:=by omega
    subst curr
    simp only [Nat.sub_self,List.range'_zero,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by v-curr
lemma extend_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,extend (eraseVec xs) v) (blastZeroExtend (newWidth:=v) g ⟨w,xs⟩) := by
  simpa only [blastZeroExtend,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,
    extend,Nat.sub_zero,List.range_eq_range'] using
    extend_go_rel (v:=v) hr xs 0 (Nat.zero_le _) (.emptyWithCapacity v)
lemma shiftConcat_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (a : AIG.Ref g) :
    VecRel (r,shiftConcat (eraseVec xs) (a.gate,a.invert)) (blastUdiv.blastShiftConcat g ⟨xs,a⟩) := by
  have hh:=extend_rel (v:=w) hr ((AIG.RefVec.empty.push a).append xs)
  simpa only [eraseVec_append,eraseVec_push,eraseVec_empty,List.nil_append,List.singleton_append,
    shiftConcat,eraseVec_length,blastUdiv.blastShiftConcat,AIG.RefVec.emptyWithCapacity_eq] using hh
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGZipFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

section Relations
variable {n : ℕ} (op : BinOp)
variable (f : (g : AIG (Fin n))→AIG.BinaryInput g→AIG.Entrypoint (Fin n))
variable [AIG.LawfulOperator (Fin n) AIG.BinaryInput f]
variable (hf : ∀{r : Graph} {g : AIG (Fin n)},Rel r g→∀i : AIG.BinaryInput g,
  EPRel (op r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) (f g i))
include hf
lemma zipLoop_rel [AIG.RefVec.LawfulZipOperator (Fin n) f]
    {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (out : AIG.RefVec g curr) :
    VecRel (zipLoop op (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (eraseVec out))
      (AIG.RefVec.zip.go g curr out hc lhs rhs f) := by
  rw [AIG.RefVec.zip.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,zipLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let ii : AIG.BinaryInput g:=⟨lhs.get curr hi,rhs.get curr hi⟩
    let ss:=f g ii
    have hs:=hf hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=f) g ii
    have ht:=zipLoop_rel hs.1 (lhs.cast hle) (rhs.cast hle) (curr+1) (by omega)
      ((out.cast hle).push ss.ref)
    simp only [eraseVec_push,eraseVec_cast] at ht
    rw [←hs.2] at ht
    exact ht
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,zipLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma zipVec_rel [AIG.RefVec.LawfulZipOperator (Fin n) f]
    {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryRefVec g w) :
    VecRel (zipVec op r (eraseVec i.lhs) (eraseVec i.rhs)) (AIG.RefVec.zip g i f) := by
  simpa only [zipVec,eraseVec_length,AIG.RefVec.zip,Nat.sub_zero,AIG.RefVec.emptyWithCapacity_eq,
    eraseVec_empty] using zipLoop_rel op f hf hr i.lhs i.rhs 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma foldLoop_rel {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (acc : AIG.Ref g) :
    EPRel (foldLoop op (w-curr) r (eraseVec xs) curr (acc.gate,acc.invert))
      (AIG.RefVec.fold.go g acc curr w xs f) := by
  rw [AIG.RefVec.fold.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,foldLoop,eraseVec_get xs hi]
    let ii : AIG.BinaryInput g:=⟨acc,xs.get curr hi⟩
    let ss:=f g ii
    have hs:=hf hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=f) g ii
    have ht:=foldLoop_rel hs.1 (xs.cast hle) (curr+1) ss.ref
    simp only [eraseVec_cast] at ht
    rw [←hs.2] at ht
    exact ht
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (by omega),foldLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma foldVec_rel {w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (xs : AIG.RefVec g w) :
    EPRel (foldVec op r (eraseVec xs)) (AIG.RefVec.fold g xs f) := by
  simpa only [foldVec,eraseVec_length,AIG.RefVec.fold,Nat.sub_zero,AIG.mkConstCached] using
    foldLoop_rel op f hf hr xs 0 (g.mkConstCached true)
end Relations

lemma eqGate_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (eqGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) (g.mkBEqCached i) := by
  let j:=i.invert false true
  let s:=g.mkGateCached j
  let sr:=gate r (i.lhs.gate,i.lhs.invert) (notRef (i.rhs.gate,i.rhs.invert))
  have hs : EPRel sr s:=by
    simpa only [sr,s,j,notRef,AIG.BinaryInput.invert,AIG.Ref.flip,Bool.false_xor,Bool.true_xor]
      using gate_rel hr j
  let i':=i.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) g j)
  let t:=s.aig.mkGateCached (i'.invert true false)
  let tr:=gate sr.1 (notRef (i.lhs.gate,i.lhs.invert)) (i.rhs.gate,i.rhs.invert)
  have ht : EPRel tr t:=by
    simpa only [tr,t,i',notRef,AIG.BinaryInput.cast,AIG.BinaryInput.invert,
      AIG.Ref.cast,AIG.Ref.flip,Bool.true_xor,Bool.false_xor] using gate_rel hs.1 (i'.invert true false)
  let a:=s.ref.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) s.aig (i'.invert true false))
  have hh:=gate_rel ht.1 (⟨a.not,t.ref.not⟩ : AIG.BinaryInput t.aig)
  have ha : (a.not.gate,a.not.invert)=notRef sr.2:=by
    simpa only [a,AIG.Ref.cast,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef hs.2.symm
  have hb : (t.ref.not.gate,t.ref.not.invert)=notRef tr.2:=by
    simpa only [AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef] using congrArg notRef ht.2.symm
  change EPRel (gate tr.1 (a.not.gate,a.not.invert) (t.ref.not.gate,t.ref.not.invert)) _ at hh
  rw [ha,hb] at hh
  have hn : t.aig.mkGateCached ⟨a.not,t.ref.not⟩ = g.mkBEqCached i := by rfl
  rw [hn] at hh
  simpa only [eqGate,xorGate,tr,sr,notRef,Bool.not_not] using hh

lemma eqVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g) (i : AIG.BinaryRefVec g w) :
    EPRel (eqVec r (eraseVec i.lhs) (eraseVec i.rhs)) (Std.Tactic.BVDecide.BVPred.mkEq g i) := by
  have hs:=zipVec_rel eqGate AIG.mkBEqCached (fun h i=>eqGate_rel h i) hr i
  have ht:=foldVec_rel gate AIG.mkAndCached (fun h i=>gate_rel h i) hs.1
    (AIG.RefVec.zip g i AIG.mkBEqCached).vec
  rw [←hs.2] at ht
  exact ht
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGDiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

lemma divStep_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divStep r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  let ri : blastUdiv.ShiftConcatInput g w:=⟨rem,lhs.getD (wn-1) (g.mkConstCached false)⟩
  let rs:=blastUdiv.blastShiftConcat g ri
  have hrs:=shiftConcat_rel hr rem ri.bit
  change VecRel (r,shiftConcat (eraseVec rem)
    ((lhs.getD (wn-1) (g.mkConstCached false)).gate,(lhs.getD (wn-1) (g.mkConstCached false)).invert)) rs at hrs
  rw [←eraseVec_getD] at hrs
  let h₁:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) g ri
  let qi : blastUdiv.ShiftConcatInput rs.aig w:=⟨q.cast h₁,rs.aig.mkConstCached false⟩
  let qs:=blastUdiv.blastShiftConcat rs.aig qi
  have hqs:=shiftConcat_rel hrs.1 qi.lhs qi.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,false)) qs at hqs
  let h₂:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) rs.aig qi
  let ni : blastUdiv.ShiftConcatInput qs.aig w:=⟨(q.cast h₁).cast h₂,qs.aig.mkConstCached true⟩
  let ns:=blastUdiv.blastShiftConcat qs.aig ni
  have hns:=shiftConcat_rel hqs.1 ni.lhs ni.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,true)) ns at hns
  let h₃:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) qs.aig ni
  let si : AIG.BinaryRefVec ns.aig w:=⟨(rs.vec.cast h₂).cast h₃,((rhs.cast h₁).cast h₂).cast h₃⟩
  let ss:=blastSub ns.aig si
  have hss:=sub_rel hns.1 si
  change VecRel (sub r (eraseVec rs.vec) (eraseVec rhs)) ss at hss
  rw [←hrs.2] at hss
  let h₄:=AIG.LawfulVecOperator.le_size (f:=blastSub) ns.aig si
  let ui : AIG.BinaryRefVec ss.aig w:=⟨((rs.vec.cast h₂).cast h₃).cast h₄,
    (((rhs.cast h₁).cast h₂).cast h₃).cast h₄⟩
  let us:=BVPred.mkUlt ss.aig ui
  have hus:=ult_rel hss.1 ui
  change EPRel (ult _ (eraseVec rs.vec) (eraseVec rhs)) us at hus
  rw [←hrs.2] at hus
  let h₅:=AIG.LawfulOperator.le_size (f:=BVPred.mkUlt) ss.aig ui
  let qi' : AIG.RefVec.IfInput us.aig w:=⟨us.ref,((qs.vec.cast h₃).cast h₄).cast h₅,
    (ns.vec.cast h₄).cast h₅⟩
  let qs':=AIG.RefVec.ite us.aig qi'
  have hqs':=ifVec_rel hus.1 qi'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec qs.vec) (eraseVec ns.vec)) qs' at hqs'
  rw [←hus.2,←hqs.2,←hns.2] at hqs'
  let h₆:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) us.aig qi'
  let ri' : AIG.RefVec.IfInput qs'.aig w:=⟨us.ref.cast h₆,
    (((rs.vec.cast h₂).cast h₃).cast h₄ |>.cast h₅).cast h₆,(ss.vec.cast h₅).cast h₆⟩
  let rs':=AIG.RefVec.ite qs'.aig ri'
  have hrs':=ifVec_rel hqs'.1 ri'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec rs.vec) (eraseVec ss.vec)) rs' at hrs'
  rw [←hus.2,←hrs.2,←hss.2] at hrs'
  exact ⟨hrs'.1,hqs'.2,hrs'.2⟩

lemma divLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (k wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divLoop k r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.go g k lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  induction k generalizing r g wn wr with
  | zero=>exact ⟨hr,rfl,rfl⟩
  | succ k ih=>
    let ss:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    have hs:=divStep_rel hr lhs rhs wn wr q rem
    have ht:=ih hs.1 (lhs.cast ss.hle) (rhs.cast ss.hle) ss.wn ss.wr ss.q ss.r
    simp only [eraseVec_cast] at ht
    rw [←hs.2.1,←hs.2.2] at ht
    exact ht
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGInputs
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_eq _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
lemma rawInputs_succ (n : ℕ) : rawInputs (n+1)=(atom (rawInputs n) n).1 := by
  simp [rawInputs,atom,List.range_succ]
lemma inputsPrefix_rel (n k : ℕ) (h : k≤n) : Rel (rawInputs k) (AIGCompiler.inputsPrefix n k h).1 := by
  induction k with
  | zero=>exact empty_rel n
  | succ k ih=>
    rw [rawInputs_succ]
    exact (atom_rel (ih (by omega)) ⟨k,by omega⟩).1
lemma inputs_rel (n : ℕ) : Rel (rawInputs n) (AIGCompiler.inputs n).1 := inputsPrefix_rel n n le_rfl
lemma inputsPrefix_ref (n k : ℕ) (h : k≤n) (i : Fin k) :
    (((AIGCompiler.inputsPrefix n k h).2 i).gate,
      ((AIGCompiler.inputsPrefix n k h).2 i).invert)=(i.val+1,false) := by
  induction k with
  | zero=>exact Fin.elim0 i
  | succ k ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_last,AIG.mkAtom,AIGCompiler.inputsPrefix_size]
      rfl
    · simp only [AIGCompiler.inputsPrefix,Fin.snoc_castSucc]
      exact ih (by omega) j
lemma inputs_ref (n : ℕ) (i : Fin n) :
    (((AIGCompiler.inputs n).2 i).gate,((AIGCompiler.inputs n).2 i).invert)=(i.val+1,false) :=
  inputsPrefix_ref n n le_rfl i

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

lemma remainder_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (remainder r (eraseVec i.lhs) (eraseVec i.rhs)) (blastUmod g i) := by
  let zi:=blastConst g (0 : BitVec w)
  let ei : AIG.BinaryRefVec g w:=⟨i.rhs,zi⟩
  let es:=BVPred.mkEq g ei
  have hes:=eqVec_rel hr ei
  change EPRel (eqVec r (eraseVec i.rhs) (eraseVec zi)) es at hes
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hes
  let h₁:=AIG.LawfulOperator.le_size (f:=BVPred.mkEq) g ei
  let ds:=blastUdiv.go es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  have hds:=divLoop_rel hes.1 (i.lhs.cast h₁) (i.rhs.cast h₁) w w 0 (zi.cast h₁) (zi.cast h₁)
  simp only [eraseVec_cast] at hds
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hds
  let h₂:=blastUdiv.go_le_size es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  let qi : AIG.RefVec.IfInput ds.aig w:=⟨es.ref.cast h₂,(i.lhs.cast h₁).cast h₂,ds.r⟩
  have hq:=ifVec_rel hds.1 qi
  change VecRel (ifVec _ (es.ref.gate,es.ref.invert) (eraseVec i.lhs) (eraseVec ds.r)) _ at hq
  rw [←hes.2,←hds.2.2] at hq
  have hn : AIG.RefVec.ite ds.aig qi = blastUmod g i := by rfl
  change VecRel _ (AIG.RefVec.ite ds.aig qi) at hq
  rw [hn] at hq
  simpa only [remainder,eraseVec_length] using hq
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBinaryInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure Std.Sat
lemma eraseVec_binaryInputs_lhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).lhs=rawWord 0 w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_castAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,Nat.zero_add]
lemma eraseVec_binaryInputs_rhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).rhs=rawWord w w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_natAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  rfl
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGBitArithmeticEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open BitStackProgram BitStackProgram.Procedure NetworkEmission

lemma binaryPack_value (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) (res : AIG.RefVecEntry (Fin (w+w)) w)
    (hr : NativeAIG.VecRel (op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)) res) :
    (binaryPack op w).val.value=erase (AIGCompiler.compileVec res.aig res.vec):=by
  dsimp only [binaryPack]
  rw [hr.2]
  exact compilePack_value hr.1 _
lemma addPack_value (w : ℕ) : (binaryPack NativeAIG.add w).val.value=erase (BitArithmetic.add w):=by
  apply binaryPack_value
  have hh:=NativeAIG.add_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma mulPack_value (w : ℕ) : (binaryPack NativeAIG.mul w).val.value=erase (BitArithmetic.mul w):=by
  apply binaryPack_value
  have hh:=NativeAIG.mul_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma subPack_value (w : ℕ) : (binaryPack NativeAIG.sub w).val.value=erase (BitArithmetic.sub w):=by
  apply binaryPack_value
  have hh:=NativeAIG.sub_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma modPack_value (w : ℕ) : (binaryPack NativeAIG.remainder w).val.value=erase (BitArithmetic.mod w):=by
  apply binaryPack_value
  have hh:=NativeAIG.remainder_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh

lemma ultPack_value (w : ℕ) : (ultPack w).val.value=erase (BitArithmetic.ult w):=by
  have hr:=NativeAIG.ult_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simp only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] at hr
  unfold ultPack BitArithmetic.ult
  have hh:=compilePack_value hr.1 (fun _ : Fin 1=>(Std.Tactic.BVDecide.BVPred.mkUlt
    (AIGCompiler.inputs (w+w)).1 (BitArithmetic.binaryInputs w)).ref)
  simpa only [List.ofFn_succ,List.ofFn_zero,hr.2] using hh

end ExactQuantumFactoring.AIGNetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionWords
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma pairPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork n l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (pairPack a b).val.value=erase (f.pair g):=by
  rw [pairPack_value,ha,hb,erase_pair]
  rw [ha,hb];rfl
lemma compPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork m l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (compPack a b).val.value=erase (f.comp g):=by
  rw [compPack_value,ha,hb,erase_comp]
  rw [ha,hb];simp [erase]
lemma borPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (borPack a b).val.value=erase (f.bor g):=
  bnotPack_value _ _ (bandPack_value _ _ _ _ (bnotPack_value _ _ ha) (bnotPack_value _ _ hb))
lemma muxPack_value {n : ℕ} (c a b : Pack) (f g h : BooleanNetwork n 1)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (muxPack c a b).val.value=erase (BooleanNetwork.mux f g h):=
  borPack_value _ _ _ _ (bandPack_value _ _ _ _ hc ha)
    (bandPack_value _ _ _ _ (bnotPack_value _ _ hc) hb)

lemma wordConstPack_value (n w c : ℕ) : (wordConstPack n w c).val.value=
    erase (BitArithmetic.wordConstant (n:=n) (BitVec.ofNat w c)):=by
  unfold wordConstPack BitArithmetic.wordConstant
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  simpa [←BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat,i.isLt] using constantPack_value n (c.testBit i.val)

lemma wordMuxPack_value {n w : ℕ} (c a b : Pack) (f : BooleanNetwork n 1) (g h : BooleanNetwork n w)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (wordMuxPack w c a b).val.value=erase (BitArithmetic.wordMux f g h):=by
  unfold wordMuxPack BitArithmetic.wordMux
  apply compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (pairPack_spec _ _ _ _ hc ha) hb)
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  exact muxPack_value _ _ _ _ _ _ (bitPack_value ⟨0,by omega⟩)
    (bitPack_value ⟨1+i.val,by omega⟩) (bitPack_value ⟨1+w+i.val,by omega⟩)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Emits
variable {α β γ δ : Type} {ea : α→List Bool} {eb : β→List Bool}
  {ec : γ→List Bool} {ed : δ→List Bool}
lemma congr {f g : α→β} (h : Emits ea eb f) (hh : ∀x,f x=g x) : Emits ea eb g:=by
  obtain ⟨p⟩:=h;exact ⟨p.congrFun hh⟩
lemma precompose {f : β→γ} (h : Emits eb ec f) (g : α→β) : Emits (fun x=>eb (g x)) ec (fun x=>f (g x)):=by
  obtain ⟨p⟩:=h;exact ⟨p.precompose g⟩
lemma natSub {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x-g x):=(ofProcedure Procedure.binarySub).comp (h.pair j)
lemma natMul {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x*g x):=(ofProcedure Procedure.binaryMul).comp (h.pair j)
lemma natDiv {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x/g x):=(ofProcedure Procedure.binaryDiv).comp (h.pair j)
lemma natMod {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x%g x):=(ofProcedure Procedure.binaryMod).comp (h.pair j)
lemma unaryNat {f : α→ℕ} (h : Emits ea unaryCode f) : Emits ea Nat.bits f:=
  (ofProcedure Procedure.unaryToBits).comp h
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackDependentChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
lemma splitOn (c : α→Prop) [DecidablePred c]
    (test : Emits ea Procedure.boolCode (fun a=>decide (c a)))
    (yes : Emits (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Emits (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Emits ea eb f:=by
  obtain ⟨p⟩:=test;obtain ⟨q⟩:=yes;obtain ⟨r⟩:=no
  exact ⟨Procedure.splitOn c p q r⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Emits
variable {α : Type} {ea : α→List Bool}
lemma natPow {f k : α→ℕ} (hf : Emits ea Nat.bits f) (hk : Emits ea unaryCode k) :
    Emits ea Nat.bits (fun x=>(f x)^(k x)):=(ofProcedure Procedure.binaryPow).comp (hk.pair hf)
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
lemma eraseOp_place {q r : ℕ} (w : Register q r) (o : Instruction q) (f : ℕ→ℕ)
    (h : ∀i,(w i).val=f i.val) : eraseOp (o.place w)=(eraseOp o).map f := by
  simp only [eraseOp,Instruction.place,Op.map,List.map_ofFn,Function.comp_apply,h]
  rfl
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitBooleanEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open NetworkEmission

lemma erase_node_compile {n q : ℕ} (h : n+1≤q) (o : BoolNode n) :
    (o.compileOp h).compile.map eraseOp=nodeOps n (eraseNode o):=by
  cases o with
  | constant b=>cases b <;> rfl
  | copy a=>rfl
  | neg a=>rfl
  | conj a b=>
    simp only [BoolNode.compileOp,BooleanOp.compile,eraseNode,nodeOps]
    simp only [Fin.ext_iff,Fin.val_castLE]
    split_ifs <;> rfl

lemma netOps_append_one (n : ℕ) (xs : List Node) (o : Node) :
    netOps n (xs++[o])=netOps n xs++nodeOps (n+xs.length) o:=by
  simp [netOps]
lemma erase_net_compile {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    (p.program h).compile.map eraseOp=netOps n (eraseNet p):=by
  induction p with
  | input=>rfl
  | @add k p o ih=>
    simp only [BoolNet.program,BooleanProgram.compile,List.flatMap_append,List.flatMap_singleton,
      List.map_append,eraseNet,netOps_append_one]
    rw [←BooleanProgram.compile,ih,erase_node_compile,eraseNet_length,←p.width_eq]

lemma erase_copyPrefix {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    (BooleanNetwork.copyPrefix f t h).compile.map eraseOp=
      copyOps k (List.ofFn (fun i : Fin t=>(f (i.castLE h)).val)):=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [BooleanNetwork.copyPrefix,BooleanProgram.compile,List.flatMap_append,
      List.flatMap_singleton,List.map_append]
    rw [←BooleanProgram.compile,ih]
    rw [List.ofFn_succ',List.concat_eq_append]
    simp only [copyOps,List.mapIdx_append_one,List.length_ofFn]
    rfl

lemma erase_oracle {n m : ℕ} (a : BooleanNetwork n m) :
    a.oracle.map eraseOp=oracleOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracle,List.map_append,List.map_map,List.map_reverse]
  have hr : (eraseOp ∘ (Instruction.reverse : Instruction (a.width+m)→_))=Op.reverse ∘ eraseOp:=rfl
  rw [hr,←List.map_map,erase_net_compile,erase_copyPrefix]
  have hw:=a.net.width_eq
  simp only [oracleOps,NetworkEmission.erase,eraseNet_length,←hw,copyOps]
  simp only [Fin.castLE_rfl,List.map_reverse,id_eq]
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma listAppend (b : β) {f g : α→List β} (hf : Emits ea (listCode eb) f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x++g x):=(ofProcedure (Procedure.listAppend eb b)).comp (hf.pair hg)
lemma unaryAdd {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x+g x):=(ofProcedure Procedure.unaryAdd).comp (h.pair j)
lemma unaryMul {f g : α→ℕ} (h : Emits ea unaryCode f) (j : Emits ea unaryCode g) :
    Emits ea unaryCode (fun x=>f x*g x):=(ofProcedure Procedure.unaryMul).comp (h.pair j)
lemma unarySucc {f : α→ℕ} (h : Emits ea unaryCode f) :
    Emits ea unaryCode (fun x=>f x+1):=(ofProcedure Procedure.unarySuccessor).comp h
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionCombinators
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m l : α→ℕ}
lemma comp {f : ∀x,BooleanNetwork (n x) (m x)} {g : ∀x,BooleanNetwork (m x) (l x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) : NetEmits ea (fun x=>(f x).comp (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  refine ⟨fun x=>compPack (p x) (q x),(ofProcedure Emission.compPackP).comp (hp.pair hq),?_⟩
  intro x
  rw [compPack_value]
  · rw [ep,eq];exact (erase_comp _ _).symm
  · rw [ep,eq];simp [erase]
lemma pair {f : ∀x,BooleanNetwork (n x) (m x)} {g : ∀x,BooleanNetwork (n x) (l x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) : NetEmits ea (fun x=>(f x).pair (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  refine ⟨fun x=>pairPack (p x) (q x),(ofProcedure Emission.pairPackP).comp (hp.pair hq),?_⟩
  intro x
  rw [pairPack_value]
  · rw [ep,eq];exact (erase_pair _ _).symm
  · rw [ep,eq];rfl
lemma rewire {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f)
    (is : ∀x,Fin (l x)→Fin (m x))
    (hi : BitStackProgram.Emits ea (listCode Nat.bits) (fun x=>List.ofFn (fun j=>(is x j).val))) :
    NetEmits ea (fun x=>(f x).rewire (is x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  refine ⟨fun x=>rewirePack (p x) (List.ofFn (fun j=>(is x j).val)),
    (ofProcedure Emission.rewirePackP).comp (hp.pair hi),?_⟩
  intro x;exact rewirePack_value _ _ _ (ep x)
lemma identity (hn : BitStackProgram.Emits ea unaryCode n) : NetEmits ea (fun x=>BooleanNetwork.select (id : Fin (n x)→Fin (n x))):=
  ⟨fun x=>identityPack (n x),(ofProcedure Emission.identityPackP).comp hn,fun _=>identityPack_value _⟩
lemma select (hn : BitStackProgram.Emits ea unaryCode n) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : BitStackProgram.Emits ea (listCode Nat.bits) (fun x=>List.ofFn (fun j=>(is x j).val))) :
    NetEmits ea (fun x=>BooleanNetwork.select (is x)):=
  (identity hn).rewire is hi
lemma constant (hn : BitStackProgram.Emits ea unaryCode n) {b : α→Bool}
    (hb : BitStackProgram.Emits ea Procedure.boolCode b) :
    NetEmits ea (fun x=>BooleanNetwork.constant (n:=n x) (b x)):=
  ⟨fun x=>constantPack (n x) (b x),(ofProcedure Emission.constantPackP).comp (hn.pair hb),fun _=>constantPack_value _ _⟩
lemma bnot {f : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) :
    NetEmits ea (fun x=>BooleanNetwork.bnot (f x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  exact ⟨fun x=>bnotPack (p x),(ofProcedure Emission.bnotPackP).comp hp,fun x=>bnotPack_value _ _ (ep x)⟩
lemma band {f g : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>BooleanNetwork.band (f x) (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  obtain ⟨q,hq,eq⟩:=hg
  exact ⟨fun x=>bandPack (p x) (q x),(ofProcedure Emission.bandPackP).comp (hp.pair hq),
    fun x=>bandPack_value _ _ _ _ (ep x) (eq x)⟩
lemma wordConst (hn : BitStackProgram.Emits ea unaryCode n) (hm : BitStackProgram.Emits ea unaryCode m)
    {c : α→ℕ} (hc : BitStackProgram.Emits ea Nat.bits c) :
    NetEmits ea (fun x=>BitArithmetic.wordConstant (n:=n x) (BitVec.ofNat (m x) (c x))):=
  ⟨fun x=>wordConstPack (n x) (m x) (c x),
    (ofProcedure Emission.wordConstPackP).comp (hn.pair (hm.pair hc)),fun _=>wordConstPack_value _ _ _⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkExpressionEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma congr {f g : ∀x,BooleanNetwork (n x) (w x)} (h : NetEmits ea f) (he : ∀x,f x=g x) :
    NetEmits ea g:=by
  obtain ⟨p,hp,hh⟩:=h
  exact ⟨p,hp,fun x=>(hh x).trans (congrArg erase (he x))⟩
lemma bor {f g : ∀x,BooleanNetwork (n x) 1} (hf : NetEmits ea f) (hg : NetEmits ea g) :
    NetEmits ea (fun x=>BooleanNetwork.bor (f x) (g x)):=((hf.bnot).band hg.bnot).bnot
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ParallelPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma parallelProgram_length {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    (parallelProgram A B).length=A.length+B.length := by
  simp [parallelProgram,leftProgram,rightProgram]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

lemma maskRegister_val (n : ℕ) (i : Fin (n+n)) : (maskRegister n i).val=n+i.val := rfl

end ExactQuantumFactoring.ListSampler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

lemma tensorWidth_eq (q K : ℕ) : tensorWidth q K=K*q := by
  induction K with
  | zero => simp [tensorWidth]
  | succ K ih => simp [tensorWidth,ih,Nat.add_mul,Nat.add_comm]

lemma tensorProgram_length {q : ℕ} (ops : List (Instruction q)) (K : ℕ) :
    (tensorProgram ops K).length=K*ops.length := by
  induction K with
  | zero => simp [tensorProgram]
  | succ K ih => rw [tensorProgram,parallelProgram_length,ih]; ring

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitProgramEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ}
lemma data {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea dataCode (fun x=>erase (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.packValueP).comp hp).congr he
lemma count {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    Emits ea unaryCode (fun x=>(f x).net.count):=by
  exact ((ofProcedure ((NativeAIG.Emission.listUnaryLength nodeCode (.constant false)).comp
    Emission.dataNodesP)).comp hf.data).congr (by intro x;exact eraseNet_length _)
end NetworkEmission.NetEmits

namespace CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits

lemma erase_oracleOn {n m r : ℕ} (a : BooleanNetwork n m) (hr : a.net.count ≤ r) :
    (BooleanNetwork.oracleOn a hr).map eraseOp=oracleOnOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracleOn,List.map_map]
  rw [show (eraseOp ∘ Instruction.place (BooleanNetwork.oraclePlacement a hr))=
    (fun o=>(eraseOp o).map (BooleanNetwork.oracleIndex n m a.width)) by
      funext o;exact eraseOp_place _ _ _ (fun _=>rfl)]
  change List.map ((Op.map (BooleanNetwork.oracleIndex n m a.width)) ∘ eraseOp) a.oracle=_
  rw [←List.map_map,erase_oracle]
  simp only [oracleOnOps,NetworkEmission.erase,List.length_ofFn,NetworkEmission.Data.width,
    NetworkEmission.eraseNet_length,←a.net.width_eq]
lemma erase_firstProgram {n m r : ℕ} (ops : List (Instruction n)) :
    (firstProgram m r ops).map eraseOp=ops.map eraseOp:=by
  simp only [firstProgram,List.map_map]
  apply List.map_congr_left
  intro o ho
  rw [Function.comp_apply,eraseOp_place _ _ id (fun _=>rfl)]
  simp [Op.map]
lemma erase_reverseProgram {q : ℕ} (ops : List (Instruction q)) :
    (ops.reverse.map Instruction.reverse).map eraseOp=(ops.map eraseOp).reverse.map Op.reverse:=by
  simp only [List.map_map,List.map_reverse]
  rfl

namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q m r : α→ℕ}
lemma congr {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (h : ∀x,p x=s x) : OpsEmits ea s:=
  BitStackProgram.Emits.congr hp (fun x=>congrArg (List.map eraseOp) (h x))
lemma append {p s : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hs : OpsEmits ea s) :
    OpsEmits ea (fun x=>p x++s x):=
  (hp.listAppend ⟨plainGate .not,[]⟩ hs).congr (fun _=>List.map_append.symm)
lemma first {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (m r : α→ℕ) :
    OpsEmits ea (fun x=>firstProgram (m x) (r x) (p x)):=BitStackProgram.Emits.congr hp (fun _=>(erase_firstProgram _).symm)
lemma reverse {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>(p x).reverse.map Instruction.reverse):=
  ((ofProcedure Emission.opsReverseP).comp hp).congr (fun _=>(erase_reverseProgram _).symm)
lemma oracleOn {f : ∀x,BooleanNetwork (q x) (m x)} (hf : NetworkEmission.NetEmits ea f)
    (h : ∀x,(f x).net.count ≤ r x) : OpsEmits ea (fun x=>BooleanNetwork.oracleOn (f x) (h x)):=
  ((ofProcedure Emission.oracleOnOpsP).comp hf.data).congr (fun _=>(erase_oracleOn _ _).symm)
end OpsEmits
end CircuitEmission
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitFinalEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma range {f : α→ℕ} (hf : Emits ea unaryCode f) : Emits ea (listCode Nat.bits) (fun x=>List.range (f x)):=
  (ofProcedure NetworkEmission.Emission.rangeP).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r : α→ℕ}
lemma place {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (w : ∀x,Register (q x) (r x)) (f : α→ℕ→ℕ)
    (hw : ∀x i,(w x i).val=f x i.val)
    (hf : Emits (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    OpsEmits ea (fun x=>(p x).map (Instruction.place (w x))):=by
  obtain ⟨pf⟩:=hf
  exact ((ofProcedure (Emission.opsMapWith pf)).comp ((BitStackProgram.Emits.id ea).pair hp)).congr (by
    intro x
    simp only [List.map_map]
    apply List.map_congr_left
    intro o ho
    exact (eraseOp_place (w x) o (f x) (hw x)).symm)
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Emits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma natLt {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x<g x)):=(ofProcedure binaryLt).comp (hf.pair hg)
lemma boolNot {f : α→Bool} (hf : Emits ea boolCode f) : Emits ea boolCode (fun x=>!f x):=
  (ofProcedure Procedure.boolNot).comp hf
lemma boolAnd {f g : α→Bool} (hf : Emits ea boolCode f) (hg : Emits ea boolCode g) :
    Emits ea boolCode (fun x=>f x&&g x):=(ofProcedure Procedure.boolAnd).comp (hf.pair hg)
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkLoopEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma ofFn_nat_eq_map {β : Type} (k : ℕ) (f : ℕ→β) :
    List.ofFn (fun i:Fin k=>f i.val)=(List.range k).map f:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp

namespace NetEmits
open BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : α→ℕ}
lemma compInput {n m : β→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)} {g : α→β}
    (hf : NetEmits eb f) (hg : BitStackProgram.Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,ep⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>ep (g x)⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkIndexedEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma vectorIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.vector (f x)):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>vectorPack (n x) ((List.range (k x)).map (p x)),
    (ofProcedure Emission.vectorPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact vectorPack_value _ _ (he x)
lemma selectSlice (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m)
    {s : α→ℕ} (hs : Emits ea Nat.bits s) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : ∀x i,(is x i).val=s x+i.val) : NetEmits ea (fun x=>BooleanNetwork.select (is x)):=by
  apply select hn is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hm))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma rewireSlice {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f)
    (hk : Emits ea unaryCode k) {s : α→ℕ} (hs : Emits ea Nat.bits s)
    (is : ∀x,Fin (k x)→Fin (m x)) (hi : ∀x i,(is x i).val=s x+i.val) :
    NetEmits ea (fun x=>(f x).rewire (is x)):=by
  apply hf.rewire is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hk))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
lemma padRight (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BooleanNetwork.padRight (n x) (m x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=he.fst.unaryNat
  have hN:=hn.comp he.snd
  have hc:=(ofProcedure Procedure.binaryLt).comp (hi.pair hN.unaryNat)
  obtain ⟨pc⟩:=hc
  obtain ⟨pa⟩:=(ofProcedure Emission.bitPackP).comp (hN.pair hi)
  obtain ⟨pb⟩:=(ofProcedure Emission.constantPackP).comp (hN.pair (const _ _ false))
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=
    ofProcedure ((Procedure.conditional pc pa pb).congrFun (by intro x;simp only [p,decide_eq_true_eq]))
  exact vectorIndexed hn (hn.unaryAdd hm) p hp (by
    intro x i
    dsimp only [p]
    split
    · rename_i hi
      simpa only [BooleanNetwork.padRight,hi,dite_true] using bitPack_value (⟨i.val,hi⟩ : Fin (n x))
    · rename_i hi
      exact constantPack_value _ _)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitCleanEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma ite {c : α→Bool} {a b : α→β} (hc : Emits ea boolCode c)
    (ha : Emits ea eb a) (hb : Emits ea eb b) :
    Emits ea eb (fun x=>if c x then a x else b x):=by
  obtain ⟨pc⟩:=hc;obtain ⟨pa⟩:=ha;obtain ⟨pb⟩:=hb
  exact ofProcedure (Procedure.conditional pc pa pb)
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma Gate.arity_le (g : Gate) : g.arity≤4 := by
  rcases g with ⟨p,i,c⟩
  cases p <;> cases c <;> cases i <;> decide
lemma Primitive.code_le (p : Primitive) : p.code≤4 := by
  cases p <;> decide

end ExactQuantumFactoring




end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitPreparationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

lemma erase_hadamardPrefix (q k : ℕ) (h : k≤q) :
    (hadamardPrefix q k h).map eraseOp=(List.range k).map hadamardOp:=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [hadamardPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {q r m : α→ℕ}
lemma hadamards {k : α→ℕ} (hk : Emits ea unaryCode k) (h : ∀x,k x≤q x) :
    OpsEmits ea (fun x=>hadamardPrefix (q x) (k x) (h x)):=
  ((ofProcedure Emission.hadamardPrefixP).comp hk).congr (fun _=>(erase_hadamardPrefix _ _ _).symm)
lemma left {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (r : α→ℕ) :
    OpsEmits ea (fun x=>leftProgram (r x) (p x)):=by
  exact place hp (fun x=>leftRegister (q x) (r x)) (fun _ i=>i) (by intros;rfl)
    (BitStackProgram.Emits.id (prodCode ea Nat.bits)).snd
lemma right {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hr : Emits ea unaryCode r) :
    OpsEmits ea (fun x=>rightProgram (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>rightRegister (r x) (q x)) (fun x i=>r x+i) (by intros;rfl)
    ((hr.comp he.fst).unaryNat.natAdd he.snd)
lemma parallel {p : ∀x,List (Instruction (q x))} {s : ∀x,List (Instruction (r x))}
    (hp : OpsEmits ea p) (hs : OpsEmits ea s) (hq : Emits ea unaryCode q) :
    OpsEmits ea (fun x=>parallelProgram (p x) (s x)):=
  (hp.left r).append (hs.right hq)
lemma target {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) (hm : Emits ea unaryCode m) (r : α→ℕ) :
    OpsEmits ea (fun x=>targetProgram (m x) (r x) (p x)):=by
  have he:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact place hp (fun x=>targetRegister (m x) (q x) (r x)) (fun x i=>m x+i) (by intros;rfl)
    ((hm.comp he.fst).unaryNat.natAdd he.snd)
lemma prepared {f : ∀x,BooleanNetwork (m x) (q x)} (hf : NetworkEmission.NetEmits ea f)
    (hm : Emits ea unaryCode m) (h : ∀x,(f x).net.count ≤ r x)
    {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p) :
    OpsEmits ea (fun x=>preparedOracle (f x) (h x) (p x)):=
  (oracleOn hf h).append (hp.target hm r)
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitRecursionEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits
lemma gateCode_bound (g : Gate) : (gateCode g).length≤20:=by
  have h:=Primitive.code_le g.primitive
  simp only [gateCode,gatePayload,gateView,prodCode, pairBits_length,primitiveCode,unaryCode,List.length_replicate,
    Procedure.boolCode,List.length_cons,List.length_nil]
  omega
lemma opCode_bound {q : ℕ} (o : Instruction q) : (opCode (eraseOp o)).length≤100+16*q:=by
  have h:=NativeAIG.listCode_length_bound Nat.bits (List.ofFn (fun i=>(o.wire i).val)) q (by
    intro i hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    exact (NativeAIG.nat_bits_length_bound _).trans (Nat.le_of_lt (o.wire j).isLt))
  rw [List.length_ofFn] at h
  have hg:=gateCode_bound o.gate
  have ha:=Gate.arity_le o.gate
  change (prodCode gateCode (listCode Nat.bits) (o.gate,List.ofFn (fun i=>(o.wire i).val))).length≤_
  simp only [prodCode, pairBits_length]
  nlinarith
lemma opsCode_bound {q : ℕ} (p : List (Instruction q)) :
    (listCode opCode (p.map eraseOp)).length≤p.length*(202+32*q)+1:=by
  have h:=NativeAIG.listCode_length_bound opCode (p.map eraseOp) (100+16*q) (by
    intro o ho;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ho;exact opCode_bound i)
  simp only [List.length_map] at h
  nlinarith

end ExactQuantumFactoring.CircuitEmission
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionDependentLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {k : α→ℕ}
lemma ofFnDep (d : β) {f : ∀x,Fin (k x)→β} (hk : Emits ea unaryCode k)
    (hf : Emits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) eb (fun x=>f x.1 x.2)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (f x)):=by
  let c:=fun x:ℕ×α=>x.1<k x.2
  let g:=fun x i=>if h:i<k x then f x ⟨i,h⟩ else d
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hc:=hx.fst.unaryNat.natLt (hk.comp hx.snd).unaryNat
  have hy : Emits (fun x:{a:ℕ×α // c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (hf.precompose (fun x:{a:ℕ×α // c a}=>(⟨x.val.2,⟨x.val.1,x.property⟩⟩ : Σa,Fin (k a)))).congr
      (by intro x;dsimp only [g];rw [dite_eq_left x.property])
  have hn : Emits (fun x:{a:ℕ×α // ¬c a}=>prodCode unaryCode ea x.val) eb (fun x=>g x.val.2 x.val.1):=by
    exact (const _ _ d).congr (by intro x;dsimp only [g];rw [dite_eq_right x.property])
  obtain ⟨p⟩:=splitOn (f:=fun x:ℕ×α=>g x.2 x.1) c hc hy hn
  exact ((ofProcedure (Procedure.tabulate (f:=g) d p)).comp (hk.pair (id ea))).congr (by
    intro x;rw [←NetworkEmission.ofFn_nat_eq_map];congr 1;funext i;simp only [g,i.isLt,dite_eq_left])
lemma flatten (d : β) {f : α→List (List β)} (hf : Emits ea (listCode (listCode eb)) f) :
    Emits ea (listCode eb) (fun x=>(f x).flatten):=
  (ofProcedure (Procedure.listFlatten eb d)).comp hf
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma concat {p : ∀x,Fin (k x)→List (Instruction (q x))} (hk : Emits ea unaryCode k)
    (hp : OpsEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>p x.1 x.2)) :
    OpsEmits ea (fun x=>(List.ofFn (p x)).flatten):=by
  exact ((ofFnDep (f:=fun x i=>(p x i).map eraseOp) [] hk hp).flatten (⟨plainGate .not,[]⟩ : Op)).congr (by
    intro x;simp only [List.map_flatten,List.map_ofFn];rfl)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

lemma erase_swapPrefix (n r k : ℕ) (h : k≤n) :
    (BooleanNetwork.swapPrefix n r k h).map eraseOp=((List.range k).map (swapOps n)).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [BooleanNetwork.swapPrefix,List.map_append,ih,List.range_succ,List.map_append,List.flatten_append]
    rfl
namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {n r : α→ℕ}
lemma swapBlocks (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>BooleanNetwork.swapPrefix (n x) (r x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=swapOps) 0 [] swapOpsP)).comp (hn.unaryNat.pair hn.range)
  exact (h.flatten (⟨plainGate .not,[]⟩ : Op)).congr (fun _=>(erase_swapPrefix _ _ _ _).symm)
lemma cleanPermutation {f g : ∀x,BooleanNetwork (n x) (n x)}
    (hf : NetworkEmission.NetEmits ea f) (hg : NetworkEmission.NetEmits ea g)
    (hn : Emits ea unaryCode n) (h : ∀x,(f x).net.count ≤ r x) (j : ∀x,(g x).net.count ≤ r x) :
    OpsEmits ea (fun x=>BooleanNetwork.cleanPermutation (f x) (g x) (h x) (j x)):=
  ((oracleOn hf h).append (swapBlocks hn)).append (oracleOn hg j)
lemma singletonHadamard (i : ∀x,Fin (n x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    OpsEmits ea (fun x=>[hadamardAt (i x)]):=
  ((ofProcedure Emission.hadamardOpP).comp hi).listCons (const _ _ [])
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkModularEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma mul (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mul (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.mul (w x),
    (ofProcedure AIGNetworkEmission.Emission.mulPackP).comp hw,fun x=>AIGNetworkEmission.mulPack_value (w x)⟩
lemma mod (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mod (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.remainder (w x),
    (ofProcedure AIGNetworkEmission.Emission.modPackP).comp hw,fun x=>AIGNetworkEmission.modPack_value (w x)⟩
lemma mulMod {a b c : ∀x,BooleanNetwork (n x) (w x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hc : NetEmits ea c)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.mulMod (a x) (b x) (c x)):=by
  have hp:=padRight hw hw
  exact (((((ha.comp hp).pair (hb.comp hp)).comp (mul (hw.unaryAdd hw))).pair
    (hc.comp hp)).comp (mod (hw.unaryAdd hw))).rewireSlice hw (const _ _ 0)
      (fun _=>Fin.castAdd _) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma wordMux {c : ∀x,BooleanNetwork (n x) 1} {a b : ∀x,BooleanNetwork (n x) (w x)}
    (hc : NetEmits ea c) (ha : NetEmits ea a) (hb : NetEmits ea b)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordMux (c x) (a x) (b x)):=by
  obtain ⟨p,hp,ep⟩:=hc;obtain ⟨q,hq,eq⟩:=ha;obtain ⟨r,hr,er⟩:=hb
  exact ⟨fun x=>wordMuxPack (w x) (p x) (q x) (r x),
    (ofProcedure Emission.wordMuxPackP).comp (hw.pair (hp.pair (hq.pair hr))),
    fun x=>wordMuxPack_value _ _ _ (c x) (a x) (b x) (ep x) (eq x) (er x)⟩
end NetEmits

open BitArithmetic
lemma powerStep_emission : ∃p : (ℕ×ℕ)→ℕ→Pack,
    Emits (prodCode unaryCode (prodCode unaryCode unaryCode)) packCode (fun x=>p x.2 x.1) ∧
    ∀w b (i : Fin b),(p (w,b) i.val).val.value=erase (_root_.OAI.ExactQuantumFactoring.BitArithmetic.powerStep w i):=by
  let ea:=prodCode unaryCode (prodCode unaryCode unaryCode)
  have hx:=BitStackProgram.Emits.id ea
  have hi:=hx.fst
  have hw:=hx.snd.fst
  have hb:=hx.snd.snd
  have hW:=((hw.unaryAdd hw).unaryAdd hb).unaryAdd hw
  have hB : NetEmits ea (fun x=>powerBase x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  have hM : NetEmits ea (fun x=>powerModulus x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw hw.unaryNat _ (by intros;simp only [Fin.val_castAdd,Fin.val_natAdd])
  have hA : NetEmits ea (fun x=>powerAcc x.2.1 x.2.2):=
    NetEmits.selectSlice hW hw ((hw.unaryAdd hw).unaryAdd hb).unaryNat _ (by intros;simp only [Fin.val_natAdd])
  have hS:=hA.mulMod hA hM hw
  have hP:=hS.mulMod hB hM hw
  have hF : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.castAdd x.2.1 : Fin ((x.2.1+x.2.1)+x.2.2)→Fin (powerWidth x.2.1 x.2.2))):=
    NetEmits.selectSlice hW ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
  obtain ⟨s,hs,es⟩:=hS
  obtain ⟨q,hq,eq⟩:=hP
  obtain ⟨f,hf,ef⟩:=hF
  let c:=fun x:ℕ×(ℕ×ℕ)=>bitPack (powerWidth x.2.1 x.2.2) ((x.2.1+x.2.1)+x.1)
  have hc : Emits ea packCode c:=(ofProcedure Emission.bitPackP).comp
    (hW.pair ((hw.unaryNat.natAdd hw.unaryNat).natAdd hi.unaryNat))
  let p:=fun wb i=>pairPack (f (i,wb)) (wordMuxPack wb.1 (c (i,wb)) (q (i,wb)) (s (i,wb)))
  refine ⟨p,(ofProcedure Emission.pairPackP).comp (hf.pair
    ((ofProcedure Emission.wordMuxPackP).comp (hw.pair (hc.pair (hq.pair hs))))),?_⟩
  intro w b i
  apply pairPack_spec _ _ _ _ (ef _)
  exact wordMuxPack_value _ _ _ (powerBit w i)
    (mulMod (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)) (powerBase w b) (powerModulus w b))
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (bitPack_value ((Fin.natAdd (w+w) i).castAdd w)) (eq _) (es _)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkPredicateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma ult (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.ult (w x)):=
  ⟨fun x=>AIGNetworkEmission.ultPack (w x),(ofProcedure AIGNetworkEmission.Emission.ultPackP).comp hw,
    fun x=>AIGNetworkEmission.ultPack_value (w x)⟩
lemma wordEq (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordEq (w x)):=by
  have hs : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.addCases (Fin.natAdd (w x)) (Fin.castAdd (w x)))):=
    select (hw.unaryAdd hw) _ ((ofProcedure Emission.swapIndicesP).comp hw)
  exact ((ult hw).bor (hs.comp (ult hw))).bnot
lemma equalOn {f g : ∀x,BooleanNetwork (n x) (w x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) (hw : BitStackProgram.Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.equalOn (f x) (g x)):=(hf.pair hg).comp (wordEq hw)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {W t d q : α→ℕ}
lemma coinBits (hW : Emits ea unaryCode W) (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    Emits ea unaryCode (fun x=>Completion.coinBits (W x) (t x) (d x)):=
  (((hW.unaryAdd ht).unaryAdd (const _ _ 2)).unaryAdd ht).unaryAdd hd
lemma completionWidth (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    Emits ea unaryCode (fun x=>Completion.totalWidth (q x) (W x) (t x) (d x)):=
  ht.unaryAdd (hq.unaryAdd (hW.unaryAdd (coinBits hW ht hd)))
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {q W t d : α→ℕ}
lemma rareWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.rareWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) ht (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma ordinaryWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.ordinaryWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) hq ht.unaryNat _ (by intros;rfl)
lemma guessWires (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.guessWires (q x) (W x) (t x) (d x)):=
  selectSlice (completionWidth hq hW ht hd) hW (ht.unaryNat.natAdd hq.unaryNat) _ (by intros;simp only [Fin.val_natAdd,Fin.val_castAdd];omega)
lemma rareNet (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    NetEmits ea (fun x=>Completion.rareNet (q x) (W x) (t x) (d x)):=
  (rareWires hq hW ht hd).equalOn (wordConst (completionWidth hq hW ht hd) ht (const _ _ 0)) ht
lemma completionOutput {f : ∀x,BooleanNetwork (q x) (W x)}
    (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>Completion.outputNet (f x) (t x) (d x)):=
  wordMux (rareNet hq hW ht hd) (guessWires hq hW ht hd) ((ordinaryWires hq hW ht hd).comp hf) hW
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkDependentEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma extendPack (hk : Emits ea unaryCode k)
    (p : (Σx,Fin (k x))→Pack)
    (hp : Emits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) packCode p) :
    ∃q : α→ℕ→Pack, Emits (prodCode unaryCode ea) packCode (fun x=>q x.2 x.1) ∧
      ∀x i,q x i.val=p ⟨x,i⟩:=by
  let c:=fun x:ℕ×α=>x.1<k x.2
  let q:=fun x i=>if h:i<k x then p ⟨x,⟨i,h⟩⟩ else emptyPack
  have he:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hc:=(ofProcedure Procedure.binaryLt).comp
    (he.fst.unaryNat.pair (hk.comp he.snd).unaryNat)
  have hy : Emits (fun x:{a:ℕ×α // c a}=>prodCode unaryCode ea x.val) packCode
      (fun x=>q x.val.2 x.val.1):=by
    have h:=hp.precompose (fun x:{a:ℕ×α // c a}=>(⟨x.val.2,⟨x.val.1,x.property⟩⟩ : Σx,Fin (k x)))
    exact h.congr (by intro x;dsimp only [q];rw [dite_eq_left x.property])
  have hn : Emits (fun x:{a:ℕ×α // ¬c a}=>prodCode unaryCode ea x.val) packCode
      (fun x=>q x.val.2 x.val.1):=by
    exact (const _ _ emptyPack).congr (by intro x;dsimp only [q];rw [dite_eq_right x.property])
  exact ⟨q,BitStackProgram.Emits.splitOn c hc hy hn,by intro x i;simp only [q,i.isLt,dite_eq_left]⟩
lemma vectorOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.vector (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  exact vectorIndexed hn hk q hq (by intro x i;rw [eq];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MachineWiringEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n p q r : α→ℕ}
lemma firstSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (firstRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hp (const _ _ 0) _ (by intros;simp only [Nat.zero_add];rfl)
lemma targetSelect (hp : Emits ea unaryCode p) (hq : Emits ea unaryCode q) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.select (targetRegister (p x) (q x) (r x))):=
  selectSlice ((hp.unaryAdd hq).unaryAdd hr) hq hp.unaryNat _ (by intros;rfl)
lemma zeros (hn : Emits ea unaryCode n) (hp : Emits ea unaryCode p) :
    NetEmits ea (fun x=>Completion.zeros (n x) (p x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (p a)=>(x.2.val,x.1))
  exact vectorOfFn hn hp (constant (hn.comp hx.snd) (const _ _ false))
lemma packNet {a : ∀x,BooleanNetwork (n x) (p x)} {b : ∀x,BooleanNetwork (n x) (q x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hn : Emits ea unaryCode n) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BooleanNetwork.packNet (r x) (a x) (b x)):=
  (ha.pair hb).pair (zeros hn hr)
end ExactQuantumFactoring.NetworkEmission.NetEmits

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p q r : α→ℕ}
lemma appendPrepared {a : ∀x,List (Instruction (p x))} {f : ∀x,BooleanNetwork (p x) (q x)}
    (ha : OpsEmits ea a) (hf : NetworkEmission.NetEmits ea f) (hp : Emits ea unaryCode p)
    (h : ∀x,(f x).net.count ≤ r x) {b : ∀x,List (Instruction (q x))} (hb : OpsEmits ea b) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.appendPrepared (a x) (f x) (h x) (b x)):=
  (ha.first q r).append (prepared hf hp h hb)
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionPreparationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k q W t d : α→ℕ}
lemma completionInitial {f : ∀x,BooleanNetwork (k x) (q x)}
    (hk : Emits ea unaryCode k) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>Completion.initialNet (f x) (W x) (t x) (d x)):=
  (zeros hk ht).pair (hf.pair ((zeros hk hW).pair (zeros hk (coinBits hW ht hd))))
end ExactQuantumFactoring.NetworkEmission.NetEmits
namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q W t d : α→ℕ}
lemma completion {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hW : Emits ea unaryCode W)
    (ht : Emits ea unaryCode t) (hd : Emits ea unaryCode d) :
    OpsEmits ea (fun x=>Completion.program (p x) (W x) (t x) (d x)):=
  parallel (hadamards ht (fun _=>le_rfl)) (parallel hp
    (parallel (hadamards hW (fun _=>le_rfl)) (hadamards (coinBits hW ht hd) (fun _=>le_rfl)) hW) hq) ht
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyAt
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
namespace PolyAt
variable {α : Sort*} {len f g : α→ℕ}
lemma const (len : α→ℕ) (c : ℕ) : PolyAt len (fun _=>c) :=
  ⟨Polynomial.C c,fun _=>by simp⟩
lemma add (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a+g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun a=>by simpa using Nat.add_le_add (hp a) (hq a)⟩
lemma mul (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a*g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun a=>by simpa using Nat.mul_le_mul (hp a) (hq a)⟩
lemma of_le (hg : PolyAt len g) (h : ∀a,f a≤g a) : PolyAt len f := by
  obtain ⟨p,hp⟩:=hg
  exact ⟨p,fun a=>(h a).trans (hp a)⟩
lemma pull {β : Sort*} (hf : PolyAt len f) (g : β→α) :
    PolyAt (fun b=>len (g b)) (fun b=>f (g b)) := by
  obtain ⟨p,hp⟩:=hf; exact ⟨p,fun b=>hp (g b)⟩
end PolyAt

end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionPolynomialUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool}
lemma unaryPow {f : α→ℕ} (hf : Emits ea unaryCode f) (k : ℕ) : Emits ea unaryCode (fun x=>(f x)^k):=by
  induction k with
  | zero=>simpa only [pow_zero] using (const ea unaryCode 1)
  | succ k ih=>simpa only [pow_succ] using ih.unaryMul hf
lemma boundedUnary {f B : α→ℕ} (hf : Emits ea Nat.bits f) (hB : Emits ea unaryCode B)
    (h : ∀x,f x≤B x) : Emits ea unaryCode f:=by
  obtain ⟨p⟩:=hf;obtain ⟨q⟩:=hB
  exact ⟨Procedure.boundedUnary p q h⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkSequenceEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma add (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>BitArithmetic.add (n x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.add (n x),
    (ofProcedure AIGNetworkEmission.Emission.addPackP).comp hn,fun _=>AIGNetworkEmission.addPack_value _⟩
lemma wordLt {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLt (a x) (b x)):=(ha.pair hb).comp (ult hm)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocksEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
lemma result {f : α→β} {g : α→γ} (hf : Emits ea eb f) (h : ∀x,eb (f x)=ec (g x)) :
    Emits ea ec g:=by
  obtain ⟨p⟩:=hf
  exact ⟨p.result h⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionBoundedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}

lemma recursionNext_iterate (K : α→ℕ) (x : Σa,Fin (K a+1)) (j : ℕ) :
    ((recursionNext K)^[j]) x=⟨x.1,⟨min (x.2.val+j) (K x.1),by omega⟩⟩:=by
  rcases x with ⟨a,i⟩
  induction j with
  | zero=>
    change (⟨a,i⟩ : Σa,Fin (K a+1))=⟨a,_⟩
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    have := i.isLt
    omega
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    dsimp only [recursionNext]
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    omega
/-- A charged finite-stack loop over an explicitly implemented next-stage
construction. The size invariant is a bound on actual intermediate encodings,
not an assumption that an arbitrary bounded function is computable. -/
lemma boundedRecursion (K : α→ℕ) (f : α→ℕ→β)
    (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>f x 0))
    (hs : Emits (recursionCode (ea:=ea) (eb:=eb) K f) eb
      (fun x=>f x.1 (min (x.2.val+1) (K x.1))))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(eb (f x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>f x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K f
  have hx : Emits ec (prodCode ea (prodCode unaryCode eb))
      (fun x=>(x.1,(x.2.val,f x.1 x.2.val))):=
    (id (prodCode ea (prodCode unaryCode eb))).precompose _
  have hcount:=hx.snd.fst
  have hk:=hK.comp hx.fst
  have hi : Emits ec unaryCode (fun x=>min (x.2.val+1) (K x.1)):=
    ((ofProcedure clippedUnary).comp (hk.pair hcount.unarySucc.unaryNat)).congr (by intro x;exact Nat.min_comm _ _)
  have hn : Emits ec ec (recursionNext K):=
    (hx.fst.pair (hi.pair hs)).result (by intro x;rfl)
  obtain ⟨pn⟩:=hn
  obtain ⟨pk⟩:=hK
  obtain ⟨P,hP⟩:=hb
  let Q : Polynomial ℕ:=Polynomial.C 4*Polynomial.X+Polynomial.C 2*pk.bound+P+Polynomial.C 4
  have bound : ∀x:Σa,Fin (K a+1),(ec x).length≤Q.eval (ea x.1).length:=by
    intro x
    have ha:=pk.output_length_le x.1
    have hv:=hP x
    dsimp only at hv
    have hi:=x.2.isLt
    simp only [unaryCode,List.length_replicate] at ha
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    simp only [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  let pi:=pn.iterate Q (by
    intro j x i hi
    rw [recursionNext_iterate]
    apply (bound _).trans
    apply eval_nat_mono
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega)
  have hz : Emits ea ec (fun x=>(⟨x,⟨0,by omega⟩⟩ : Σa,Fin (K a+1))):=
    ((id ea).pair ((const ea unaryCode 0).pair h0)).result (by intro x;rfl)
  have hout:=hx.snd.snd.comp ((ofProcedure pi).comp ((ofProcedure pk).pair hz))
  exact hout.congr (by intro x;dsimp only;rw [recursionNext_iterate];simp only [Nat.zero_add,min_self])
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkModularPowerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
lemma modularPower_emission : NetEmits (prodCode unaryCode unaryCode) (fun x=>modularPower x.1 x.2):=by
  obtain ⟨p,hp,ep⟩:=powerStep_emission
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode unaryCode)
  have hw:=hx.fst
  have hb:=hx.snd
  have hI:=((hw.unaryAdd hw).unaryAdd hb)
  have hW:=hI.unaryAdd hw
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hb.pair hx)
  let q:=fun wb k=>((List.range k).map (p wb)).foldl compPack (identityPack (powerWidth wb.1 wb.2))
  have hq : Emits (prodCode unaryCode unaryCode) packCode (fun wb=>q wb wb.2):=
    (ofProcedure Emission.foldCompP).comp (hps.pair ((ofProcedure Emission.identityPackP).comp hW))
  have eq : ∀w b k (hk:k ≤ b),(q (w,b) k).val.value=erase (powerPrefix w b k hk):=by
    intro w b k
    induction k with
    | zero=>intro hk;exact identityPack_value _
    | succ k ih=>
      intro hk
      dsimp only [q]
      rw [List.range_succ,List.map_append,List.foldl_append,List.map_singleton,List.foldl_cons,List.foldl_nil]
      exact compPack_spec _ _ _ _ (ih (by omega)) (ep w b ⟨k,by omega⟩)
  have hprefix : NetEmits (prodCode unaryCode unaryCode) (fun x=>powerPrefix x.1 x.2 x.2 le_rfl):=
    ⟨fun x=>q x x.2,hq,fun x=>eq x.1 x.2 x.2 le_rfl⟩
  have hstart:= (NetEmits.identity hI).pair (NetEmits.wordConst hI hw (const _ _ 1))
  exact hstart.comp (hprefix.rewireSlice hw hI.unaryNat _ (by intros;rfl))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w b : α→ℕ}
lemma modularPower (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BitArithmetic.modularPower (w x) (b x)):=by
  obtain ⟨pack, hpack, hvalue⟩ := modularPower_emission
  exact ⟨fun value => pack (w value, b value),
    hpack.comp (hw.pair hb), fun value => hvalue (w value, b value)⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.ListSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.work (n x)):=
  hn.unaryMul (((const _ _ 49).unaryMul hn).unaryAdd (const _ _ 8))
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.width (n x)):=
  (hn.unaryAdd hn).unaryAdd (hn.unaryAdd (work hn))
lemma mask (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>listMaskNet (n x)):=by
  apply vectorOfFn hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact wordLt (wordConst hN hN ((const _ Nat.bits 2).natPow hx.fst)) (identity hN) hN

lemma erase_maskedPrefix (n k : ℕ) (h : k≤n) :
    (maskedPrefix n k h).map eraseOp=(List.range k).map (maskOp n):=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [maskedPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
lemma masked (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>maskedPrefix (n x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=maskOp) 0 (maskOp 0 0) maskOpP)).comp (hn.unaryNat.pair hn.range)
  exact h.congr (fun _=>(erase_maskedPrefix _ _ _).symm)
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>ListSampler.circuit (n x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.oracleOn (mask hn) (fun x=>(listMaskNet_count (n x)).trans (Nat.le_add_left _ _))).append
    (OpsEmits.place (masked hn) (fun x=>ListSampler.maskRegister (n x)) (fun x i=>n x+i)
      (fun _ _=>ListSampler.maskRegister_val _ _) ((hn.comp hx.fst).unaryNat.natAdd hx.snd))
lemma singleZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.singleZeroNet (n x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hN:=hn.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=by
    exact ((hi.natLt hN.unaryNat).ite
      ((ofProcedure NetworkEmission.Emission.bitPackP).comp (hN.pair hi))
      ((ofProcedure NetworkEmission.Emission.constantPackP).comp (hN.pair (const _ _ false)))).congr
      (by intro x;simp only [p,decide_eq_true_eq])
  apply vectorIndexed hn (width hn) p hp
  intro x i
  dsimp only [p]
  split
  · rename_i hi
    exact bitPack_value (⟨i.val,hi⟩ : Fin (n x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.ListSamplerEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkCanonicalEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
lemma canonicalPack_erase {n m : ℕ} (p : Pack) (a : BooleanNetwork n m)
    (h : p.val.value=erase a) : canonicalPack p=erasePack a:=by
  apply Subtype.ext
  change PackData.mk _ _=PackData.mk _ _
  congr 1
  · rw [h]
    simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn]
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n m : α→ℕ} {f : ∀x,BooleanNetwork (n x) (m x)}
lemma canonical (hf : NetEmits ea f) : Emits ea packCode (fun x=>erasePack (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ((ofProcedure Emission.canonicalPackP).comp hp).congr
    (fun x=>Emission.canonicalPack_erase _ _ (he x))
lemma ofCanonical (hf : Emits ea packCode (fun x=>erasePack (f x))) : NetEmits ea f:=
  ⟨fun x=>erasePack (f x),hf,fun _=>rfl⟩
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionLengthBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma lengthPoly {f : α→β} (hf : Emits ea eb f) :
    PolyAt (fun x=>(ea x).length) (fun x=>(eb (f x)).length):=by
  obtain ⟨p⟩:=hf
  exact ⟨Polynomial.X+p.bound,fun x=>by simpa using p.output_length_le x⟩
lemma unaryPoly {f : α→ℕ} (hf : Emits ea unaryCode f) :
    PolyAt (fun x=>(ea x).length) f:=by
  simpa only [unaryCode,List.length_replicate] using hf.lengthPoly
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OpsEmits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

namespace OpsEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {q : α→ℕ→ℕ}
    {f : ∀x j,List (Instruction (q x j))}
lemma lengthPoly {w : α→ℕ} {p : ∀x,List (Instruction (w x))} (hp : OpsEmits ea p) :
    PolyAt (fun x=>(ea x).length) (fun x=>(p x).length):=by
  exact (BitStackProgram.Emits.lengthPoly hp).of_le (fun x=>by
    simpa only [List.length_map] using list_length_le_code opCode ((p x).map eraseOp))
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : OpsEmits ea (fun x=>f x 0))
    (hs : OpsEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode (listCode opCode))
        (x.1,(x.2.val,(f x.1 x.2.val).map eraseOp)))
      (fun x=>f x.1 (x.2.val+1)))
    (hq : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>q x.1 x.2.val))
    (hl : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(f x.1 x.2.val).length)) :
    OpsEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>(f x j).map eraseOp
  let ec:=recursionCode (ea:=ea) (eb:=listCode opCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) (listCode opCode)
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec (listCode opCode) (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(listCode opCode (F x.1 x.2.val)).length):=
    ((hl.mul ((PolyAt.const _ 202).add ((PolyAt.const _ 32).mul hq))).add (PolyAt.const _ 1)).of_le
      (fun x=>opsCode_bound _)
  exact BitStackProgram.Emits.boundedRecursion K F hK h0 ht hb
end OpsEmits
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensorWidth (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    Emits ea unaryCode (fun x=>ExactQuantumFactoring.tensorWidth (q x) (k x)):=
  (hk.unaryMul hq).congr (fun _=>(tensorWidth_eq _ _).symm)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma tensorWire_val (q K : ℕ) (i : Fin K) (j : Fin q) :
    (tensorWire q K i j).val=q*i.val+j.val:=by
  induction K with
  | zero=>exact Fin.elim0 i
  | succ K ih=>
    refine Fin.cases ?_ (fun i=>?_) i
    · simp only [tensorWire,Fin.cases_zero,Fin.val_castAdd,Fin.val_zero,Nat.mul_zero,Nat.zero_add]
    · simp only [tensorWire,Fin.cases_succ,Fin.val_natAdd,ih,Fin.val_succ,Nat.mul_add,Nat.mul_one];omega
lemma tensorPack_value {n q K : ℕ} (fs : Fin K→BooleanNetwork n q) (ps : Fin K→Pack)
    (h : ∀i,(ps i).val.value=erase (fs i)) :
    ((List.ofFn ps).foldr pairPack (emptyAt n)).val.value=erase (tensorNetwork fs):=by
  induction K with
  | zero=>simp only [List.ofFn_zero,List.foldr_nil,tensorNetwork,emptyAt,selectPack];rw [erase_select];rfl
  | succ K ih=>
    rw [List.ofFn_succ,List.foldr_cons,tensorNetwork]
    exact pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n q k : α→ℕ}
lemma tensorSelect (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k)
    (i : ∀x,Fin (k x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>ExactQuantumFactoring.tensorSelect (q x) (k x) (i x)):=
  selectSlice (hq.tensorWidth hk) hq (hq.unaryNat.natMul hi) _ (fun _ _=>tensorWire_val _ _ _ _)
lemma tensor {f : ∀x,Fin (k x)→BooleanNetwork (n x) (q x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>tensorNetwork (f x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨s,hs,es⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hs
  have hps:=(ofProcedure (Procedure.tabulate (f:=s) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (s x)).foldr pairPack (emptyAt (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.pairPackP)).comp
      (hps.pair ((ofProcedure Emission.emptyAtP).comp hn)),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact tensorPack_value _ _ (fun i=>by rw [es];exact he ⟨x,i⟩)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring.CircuitEmission.OpsEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {q k : α→ℕ}
lemma tensor {p : ∀x,List (Instruction (q x))} (hp : OpsEmits ea p)
    (hq : Emits ea unaryCode q) (hk : Emits ea unaryCode k) :
    OpsEmits ea (fun x=>tensorProgram (p x) (k x)):=by
  apply boundedStages hk (f:=fun x j=>tensorProgram (p x) j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (k a)=>(x.1,(x.2.val,(tensorProgram (p x.1) x.2.val).map eraseOp)))
    exact parallel (hp.comp hx.fst) hx.snd.snd (hq.comp hx.fst)
  · exact ((hq.tensorWidth hk).unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hk.unaryPoly.mul hp.lengthPoly).pull (fun x:Σa,Fin (k a+1)=>x.1)).of_le (by
      intro x;rw [tensorProgram_length];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.CircuitEmission.OpsEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma transitionWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>Completion.transitionWidth (n x)):=
  hn.unaryMul ((hn.unaryPow 5).unaryAdd (const _ _ 1))
lemma sampleExponent (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.sampleExponent (n x)):=by
  have h:=(const _ unaryCode 16).unaryMul hn
  exact (h.unaryNat.natSub (const _ _ 2)).boundedUnary h (fun _=>Nat.sub_le _ _)
lemma retentionBits (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.retentionBits (n x)):=
  ((const _ _ 80).unaryMul hn).unaryAdd (const _ _ 20)
end ExactQuantumFactoring.BitStackProgram.Emits
namespace ExactQuantumFactoring.PhysicalListEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.ordinaryWidth (n x)):=
  (ListSamplerEmission.width hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (ListSamplerEmission.program hn) (ListSamplerEmission.width hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.initialNet (n x)):=by
  apply completionInitial hn (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
  apply tensor hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact ListSamplerEmission.singleZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (work hn)
lemma launch (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>PhysicalListSlots.launch (n x)):=
  OpsEmits.prepared (initial hn) hn (fun _=>le_rfl) (program hn)
end ExactQuantumFactoring.PhysicalListEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularNetworkEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {p b : α→ℕ}
lemma sub (hb : Emits ea unaryCode b) : NetEmits ea (fun x=>BitArithmetic.sub (b x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.sub (b x),
    (ofProcedure AIGNetworkEmission.Emission.subPackP).comp hb,fun _=>AIGNetworkEmission.subPack_value _⟩
lemma translateInput {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.addInput (f x)):=
  (selectSlice (hp.unaryAdd hb) hb hp.unaryNat (fun x=>Fin.natAdd (p x)) (by intros;rfl)).pair
    ((selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).comp hf)
lemma translateForward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.forward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (add hb))
lemma translateBackward {f : ∀x,BooleanNetwork (p x) (b x)} (hf : NetEmits ea f)
    (hp : Emits ea unaryCode p) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>ControlledTranslation.backward (f x)):=
  (selectSlice (hp.unaryAdd hb) hp (const _ _ 0) (fun x i=>i.castAdd (b x)) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])).pair
    ((translateInput hf hp hb).comp (sub hb))
lemma triangularRow (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : NetEmits ea (fun x=>Triangular.rowNetwork (j x)):=by
  let f : α→ℕ→Pack:=fun x i=>if (j x).val ≤ i ∧ i<b x-1 then
    bandPack (bitPack (b x) ((b x-1+(j x).val-i)%b x)) (bitPack (b x) (j x).val)
    else constantPack (b x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hn:=hb.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hJ:=hj.comp hx.snd
  have hB:=hn.unaryNat.natSub (const _ _ 1)
  have hc:=((hi.natLt hJ).boolNot).boolAnd (hi.natLt hB)
  have hr:=((hB.natAdd hJ).natSub hi).natMod hn.unaryNat
  have hA:=(ofProcedure Emission.bitPackP).comp (hn.pair hr)
  have hD:=(ofProcedure Emission.bitPackP).comp (hn.pair hJ)
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>f x.2 x.1):=by
    exact (hc.ite ((ofProcedure Emission.bandPackP).comp (hA.pair hD))
      ((ofProcedure Emission.constantPackP).comp (hn.pair (const _ _ false)))).congr (by
        intro x;simp only [f,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,not_lt,decide_eq_true_eq])
  apply vectorIndexed hb hb f hp
  intro x i
  dsimp only [f,Triangular.rowNetwork]
  split
  · exact bandPack_value _ _ _ _ (bitPack_value (Triangular.rowIndex (j x) i)) (bitPack_value (j x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularProgramEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.TriangularEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {b a : α→ℕ}
lemma work (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.work (b x)):=
  ((const _ _ 159).unaryMul hb).unaryAdd (const _ _ 6)
lemma width (hb : Emits ea unaryCode b) : Emits ea unaryCode (fun x=>Triangular.width (b x)):=
  ((hb.unaryAdd hb).unaryAdd (hb.unaryAdd hb)).unaryAdd (work hb)
lemma preparePhase (hb : Emits ea unaryCode b) (h : ∀x,2≤b x) :
    OpsEmits ea (fun x=>ExactQuantumFactoring.preparePhase (b x) (h x)):=by
  have hOne:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 1))
  have hTwo:=(ofProcedure CircuitEmission.Emission.phaseOpP).comp (hb.unaryNat.natSub (const _ _ 2))
  exact ((OpsEmits.hadamards hb (fun _=>le_rfl)).listAppend (⟨plainGate .not,[]⟩ : Op)
    (hOne.listCons (hOne.listCons (hTwo.listCons (const _ _ []))))).congr (by
      intro x;simp only [ExactQuantumFactoring.preparePhase,List.map_append,List.map_cons,List.map_nil];rfl)
lemma preparation (ha : Emits ea unaryCode a) :
    OpsEmits ea (fun x=>Triangular.preparation (a x)):=by
  have hb:=ha.unaryAdd (const _ _ 2)
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (preparePhase hb (by intro x;omega)).place (fun x=>Triangular.phaseRegister (a x+2))
    (fun x i=>a x+2+i) (by intros;rfl) ((hb.comp hx.fst).unaryNat.natAdd hx.snd)
lemma row (hb : Emits ea unaryCode b) (j : ∀x,Fin (b x))
    (hj : Emits ea Nat.bits (fun x=>(j x).val)) : OpsEmits ea (fun x=>Triangular.rowCircuit (j x)):=by
  have hR:=triangularRow hb j hj
  exact (OpsEmits.singletonHadamard (fun x=>Triangular.dataWire (j x)) hj).append
    (OpsEmits.cleanPermutation (translateForward hR hb hb) (translateBackward hR hb hb) (hb.unaryAdd hb)
      (fun x=>Triangular.translation_count_forward (j x)) (fun x=>Triangular.translation_count_backward (j x)))
lemma triPrefix_eq (b k : ℕ) (h : k≤b) :
    Triangular.triPrefix b k h=(List.ofFn (fun i:Fin k=>Triangular.rowCircuit (i.castLE h))).flatten:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [Triangular.triPrefix,ih (by omega),List.ofFn_succ',List.concat_eq_append,List.flatten_append]
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
    apply congrArg₂ List.append
    · apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
    · apply congrArg Triangular.rowCircuit
      apply Fin.ext
      rfl
lemma fullPrefix (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.triPrefix (b x) (b x) le_rfl):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σz,Fin (b z)=>(x.2.val,x.1))
  have h:=OpsEmits.concat (p:=fun x (i:Fin (b x))=>Triangular.rowCircuit i) hb (row (hb.comp hx.snd) (fun x:Σz,Fin (b z)=>x.2) hx.fst.unaryNat)
  exact h.congr (by intro x;rw [triPrefix_eq];rfl)
lemma transform (ha : Emits ea unaryCode a) : OpsEmits ea (fun x=>Triangular.transform (a x)):=
  ((preparation ha).append (fullPrefix (ha.unaryAdd (const _ _ 2)))).append (preparation ha).reverse
lemma uniform (hb : Emits ea unaryCode b) : OpsEmits ea (fun x=>Triangular.uniformPreparation (b x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.hadamards hb (fun _=>le_rfl)).place (fun x=>Triangular.dataRegister (b x))
    (fun _ i=>i) (by intros;rfl) hx.snd
end ExactQuantumFactoring.TriangularEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.OrderSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {w b s n : α→ℕ}
lemma inputWidth (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.inputWidth (w x) (b x)):=
  (hw.unaryAdd hw).unaryAdd (TriangularEmission.width hb)
lemma scratch (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.scratch (w x) (b x)):=
  hw.unaryAdd (hb.unaryMul (((((const _ _ 3672).unaryMul hw).unaryMul hw).unaryAdd
    ((const _ _ 436).unaryMul hw)).unaryAdd (const _ _ 36)))
lemma width (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.width (w x) (b x)):=
  ((inputWidth hw hb).unaryAdd hw).unaryAdd (scratch hw hb)
lemma powerInputs (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerInputs (w x) (b x)):=by
  apply selectSlice (inputWidth hw hb) ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _
  intro x i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,Nat.zero_add]
  · simp only [Fin.addCases_right,Fin.val_natAdd,Nat.zero_add];rfl
lemma powerNetwork (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerNetwork (w x) (b x)):=
  (powerInputs hw hb).comp (modularPower hw hb)
lemma initial (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    OpsEmits ea (fun x=>OrderSample.initial (w x) (b x)):=
  ((TriangularEmission.uniform hb).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (b x))
lemma program (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.program (w x) (s x)):=by
  have hb:=hs.unaryAdd (const _ _ 2)
  exact (OpsEmits.oracleOn (powerNetwork hw hb) (fun x=>OrderSample.powerNetwork_count (w x) (s x+2))).append
    (((TriangularEmission.transform hs).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (s x+2)))
lemma complete (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.completeSampler (w x) (s x)):=
  (initial hw (hs.unaryAdd (const _ _ 2))).append (program hw hs)
lemma guessWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.guessWidth (n x)):=
  hn.unaryAdd (hn.unaryAdd (hn.unaryAdd (retentionBits hn)))
lemma guessProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderTrial.guessProgram (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
    (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
      (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
        (OpsEmits.hadamards (retentionBits hn) (fun _=>le_rfl)) hn) hn) hn
lemma rawWidth (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.rawWidth (w x) (s x) (n x)):=
  (const _ _ 2).unaryAdd ((width hw (hs.unaryAdd (const _ _ 2))).unaryAdd (guessWidth hn))
lemma rawProgram (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>OrderTrial.rawProgram (w x) (s x) (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards (const _ _ 2) (fun _=>le_rfl))
    (OpsEmits.parallel (complete hw hs) (guessProgram hn) (width hw (hs.unaryAdd (const _ _ 2)))) (const _ _ 2)
end ExactQuantumFactoring.OrderSamplerEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w k : α→ℕ}
lemma splitOn {a b : α→ℕ} {f : ∀x,BooleanNetwork (a x) (b x)}
    (c : α→Prop) [DecidablePred c] (hc : Emits ea Procedure.boolCode (fun x=>decide (c x)))
    (hy : NetEmits (fun x:{a // c a}=>ea x.val) (fun x=>f x.val))
    (hz : NetEmits (fun x:{a // ¬c a}=>ea x.val) (fun x=>f x.val)) : NetEmits ea f:=
  ofCanonical (BitStackProgram.Emits.splitOn c hc hy.canonical hz.canonical)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilterEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
lemma recode {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→β} {g : α→γ} (h : Emits ea eb f) (he : ∀x,eb (f x)=ec (g x)) : Emits ea ec g:=by
  obtain ⟨p⟩:=h;exact ⟨p.result he⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionEncodingEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k n K : α→ℕ}
lemma transitionEncode {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>TransitionWords.encodeNet (f x)):=by
  apply vectorOfFn hk (hn.unaryMul (hK.unaryAdd (const _ _ 1)))
  let X:=Σa,Fin (n a*(K a+1))
  let ix:=fun x:X=>finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) x.2)
  let c:=fun x:X=>(ix x).1.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:X=>(x.2.val,x.1))
  have row:=hx.fst.unaryNat.natDiv (hn.comp hx.snd).unaryNat
  have col:=hx.fst.unaryNat.natMod (hn.comp hx.snd).unaryNat
  have hc : Emits (fun x:X=>prodCode unaryCode ea (x.2.val,x.1)) Procedure.boolCode (fun x=>decide (c x)):=
    row.natLt (hK.comp hx.snd).unaryNat
  apply NetEmits.splitOn c hc
  · have hy:=hx.precompose (fun x:{x:X // c x}=>x.val)
    have hp : Emits (fun x:{x:X // c x}=>prodCode unaryCode ea (x.val.2.val,x.val.1))
        (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1))
        (fun x=>(⟨x.val.1,⟨(ix x.val).1.val,x.property⟩⟩ : Σa,Fin (K a))):=by
      exact (((row.precompose (fun x:{x:X // c x}=>x.val)).boundedUnary
        (hK.comp hy.snd) (fun x=>x.property.le)).pair hy.snd).recode (by intro x;rfl)
    have hnf:=hf.compInput hp
    have hsel:=hnf.rewire (fun x (_ : Fin 1)=>(ix x.val).2)
      (((col.precompose (fun x:{x:X // c x}=>x.val)).listCons (const _ _ [])).congr
        (by intro x;simp [ix]))
    exact hsel.congr (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_left x.property])
  · exact (constant (hk.comp (hx.precompose (fun x:{x:X // ¬c x}=>x.val)).snd) (const _ _ false)).congr
      (by intro x;dsimp only [TransitionWords.encodeNet];rw [dite_eq_right x.property])
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListOutputEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalListEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma sample (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.sampleNet (n x)):=
  selectSlice (ListSamplerEmission.width hn) hn (hn.unaryNat.natAdd hn.unaryNat) _ (by intros;rfl)
lemma ordinary (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.ordinaryNet (n x)):=by
  apply transitionEncode (ordinaryWidth hn) hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  have hn':=hn.comp hx.snd
  exact (NetEmits.tensorSelect (ListSamplerEmission.width hn') (hn'.unaryPow 5) (fun x=>x.2) hx.fst.unaryNat).comp
    (sample hn')
lemma output (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.outputNet (n x)):=
  completionOutput (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    (hn.unaryMul (hn.unaryPow 5)) (ordinary hn)
end ExactQuantumFactoring.PhysicalListEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalOrderEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n w b : α→ℕ}
lemma samplerZero (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSlots.samplerZeroNet (w x) (b x)):=by
  have hi:=hw.unaryAdd hw
  exact ((identity hi).pair (zeros hi (TriangularEmission.width hb))).packNet
    (zeros hi hw) hi (OrderSamplerEmission.scratch hw hb)
lemma rawZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.rawZeroNet (n x)):=
  (zeros (hn.unaryAdd hn) (const _ _ 2)).pair
    ((samplerZero hn ((sampleExponent hn).unaryAdd (const _ _ 2))).pair
      (zeros (hn.unaryAdd hn) (OrderSamplerEmission.guessWidth hn)))
lemma ordinaryWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.ordinaryWidth (n x)):=
  (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn).tensorWidth (hn.unaryPow 5)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderSlots.width (n x)):=
  completionWidth (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderSlots.program (n x)):=
  OpsEmits.completion (OpsEmits.tensor (OrderSamplerEmission.rawProgram hn (sampleExponent hn) hn)
    (OrderSamplerEmission.rawWidth hn (sampleExponent hn) hn) (hn.unaryPow 5))
    (ordinaryWidth hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>OrderSlots.initialNet (n x)):=by
  apply completionInitial (hn.unaryAdd hn) (transitionWidth hn) ((const _ _ 2).unaryMul hn)
    ((hn.unaryAdd (const _ _ 10)).unaryMul (hn.unaryPow 5))
  apply tensor (hn.unaryAdd hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact rawZero (hn.comp hx.snd)
end ExactQuantumFactoring.PhysicalOrderEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalSplitEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma ordersProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.ordersProgram (n x)):=
  OpsEmits.tensor (PhysicalOrderEmission.program hn) (PhysicalOrderEmission.width hn) (hn.unaryPow 5)
lemma listWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.listWires (n x)):=
  targetSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma modulusWires (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.modulusWires (n x)):=
  firstSelect hn (PhysicalListEmission.width hn) (PhysicalListEmission.work hn)
lemma base (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.baseNet (i x)):=
  ((listWires hn).comp (PhysicalListEmission.output hn)).rewireSlice hn (hn.unaryNat.natMul hi) _
    (by intro x j; change j.val+n x*(i x).val=n x*(i x).val+j.val; omega)
lemma orderInitial (hn : Emits ea unaryCode n) (i : ∀x,Fin ((n x)^5))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>FixedSplit.orderInitialNet (i x)):=
  ((base hn i hi).pair (modulusWires hn)).comp (PhysicalOrderEmission.initial hn)
lemma ordersInitial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.ordersInitialNet (n x)):=by
  apply tensor (PhysicalListEmission.launchWidth hn) (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact orderInitial (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma program_oai (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>FixedSplit.program (n x)):=
  OpsEmits.appendPrepared (PhysicalListEmission.launch hn) (ordersInitial hn)
    (PhysicalListEmission.launchWidth hn) (fun _=>le_rfl) (ordersProgram hn)
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalSplitEmission.program_oai := @OAI.ExactQuantumFactoring.PhysicalSplitEmission.program_oai

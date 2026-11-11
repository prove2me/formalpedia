-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:18:04.953519+00:00
-- url     : https://prove2.me/submissions/a8049f94-80e2-41cb-b197-d70ba05a4175

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
import Definitions.Def_OAIQ222A004
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_machineWidth
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_retainedOrder

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
lemma mulPack_value (w : ℕ) : (binaryPack NativeAIG.mul w).val.value=erase (BitArithmetic.mul w):=by
  apply binaryPack_value
  have hh:=NativeAIG.mul_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkResizeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma resizePack_value (u w : ℕ) : (resizePack u w).val.value=erase (BitArithmetic.resizeWord u w):=by
  unfold resizePack BitArithmetic.resizeWord
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  by_cases h : i.val<u
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact bitPack_value ⟨i.val,h⟩
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact constantPack_value _ _
end ExactQuantumFactoring.NetworkEmission

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
lemma resize (hn : BitStackProgram.Emits ea unaryCode n) (hm : BitStackProgram.Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.resizeWord (n x) (m x)):=
  ⟨fun x=>resizePack (n x) (m x),(ofProcedure Emission.resizePackP).comp (hn.pair hm),fun _=>resizePack_value _ _⟩
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
end ExactQuantumFactoring.BitStackProgram.Emits

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
lemma selectSlice (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m)
    {s : α→ℕ} (hs : Emits ea Nat.bits s) (is : ∀x,Fin (m x)→Fin (n x))
    (hi : ∀x i,(is x i).val=s x+i.val) : NetEmits ea (fun x=>BooleanNetwork.select (is x)):=by
  apply select hn is
  have h := (ofProcedure (Procedure.listMapWith (f:=fun s i=>s+i) 0 0 Procedure.binaryAdd)).comp
    (hs.pair ((ofProcedure Emission.rangeP).comp hm))
  exact h.congr (by intro x;rw [←ofFn_nat_eq_map];congr 1;funext i;exact (hi x i).symm)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

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
lemma wordMux {c : ∀x,BooleanNetwork (n x) 1} {a b : ∀x,BooleanNetwork (n x) (w x)}
    (hc : NetEmits ea c) (ha : NetEmits ea a) (hb : NetEmits ea b)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordMux (c x) (a x) (b x)):=by
  obtain ⟨p,hp,ep⟩:=hc;obtain ⟨q,hq,eq⟩:=ha;obtain ⟨r,hr,er⟩:=hb
  exact ⟨fun x=>wordMuxPack (w x) (p x) (q x) (r x),
    (ofProcedure Emission.wordMuxPackP).comp (hw.pair (hp.pair (hq.pair hr))),
    fun x=>wordMuxPack_value _ _ _ (c x) (a x) (b x) (ep x) (eq x) (er x)⟩
end NetEmits

open BitArithmetic
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
end NetEmits
end ExactQuantumFactoring.NetworkEmission

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
lemma iterate {f : ∀x,BooleanNetwork (n x) (n x)}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetEmits ea (fun x=>(f x).iterate (k x)):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨pp⟩:=hp.comp (BitStackProgram.Emits.id (prodCode unaryCode ea)).snd
  have hps:=(ofProcedure (Procedure.tabulate (f:=fun x _=>p x) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (fun _=>p x)).foldr compPack (identityPack (n x)),
    (ofProcedure (Emission.foldRightPack 0 (by intros;rfl) Emission.compPackP)).comp
      (hps.pair ((ofProcedure Emission.identityPackP).comp hn)),?_⟩
  intro x
  suffices ∀j,(((List.range j).map (fun _=>p x)).foldr compPack (identityPack (n x))).val.value=
      erase ((f x).iterate j) from this (k x)
  intro j
  simp only [List.map_const',List.length_range,BooleanNetwork.iterate]
  induction j with
  | zero=>exact identityPack_value _
  | succ j ih=>
    simp only [List.replicate_succ,List.foldr_cons,BooleanNetwork.sequence] at *
    exact compPack_spec _ _ _ _ (he x) ih
end NetEmits
end ExactQuantumFactoring.NetworkEmission

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuitEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {w e k : α→ℕ}
lemma rootModulus (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootModulus (w x)):=
  selectSlice (hw.unaryAdd hw) hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma rootGuess (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.rootGuess (w x)):=
  selectSlice (hw.unaryAdd hw) hw hw.unaryNat _ (by intros;rfl)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GcdEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {w K : α→ℕ}
lemma euclidStep (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.euclidStep (w x)):=by
  have hz:=wordConst (hw.unaryAdd hw) hw (const _ _ 0)
  have hd:=(rootGuess hw).equalOn hz hw
  exact (hd.wordMux (rootModulus hw) (rootGuess hw) hw).pair (hd.wordMux hz (mod hw) hw)
lemma euclidPrefix (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K) :
    NetEmits ea (fun x=>BitArithmetic.euclidPrefix (w x) (K x)):=by
  apply ((euclidStep hw).iterate (hw.unaryAdd hw) hK).congr
  intro x
  have h : ∀j,BooleanNetwork.iterate (BitArithmetic.euclidStep (w x)) j=BitArithmetic.euclidPrefix (w x) j:=by
    intro j;induction j with
    | zero=>rfl
    | succ j ih=>simpa only [BooleanNetwork.iterate, List.replicate_succ, BooleanNetwork.sequence, BitArithmetic.euclidPrefix] using congrArg (BooleanNetwork.comp (BitArithmetic.euclidStep (w x))) ih
  exact h _
lemma gcd (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.gcdNet (w x)):=
  (euclidPrefix hw ((const _ _ 2).unaryMul hw)).comp (rootModulus hw)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifierEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w K : α→ℕ}
lemma productOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.productNet (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hK p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hK.pair (id ea))
  obtain ⟨c,hc,ec⟩:=mul hw
  obtain ⟨b,hb,eb⟩:=wordConst hk hw (const _ _ 1)
  refine ⟨fun x=>((List.range (K x)).map (q x)).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x),
    (ofProcedure Emission.foldChoiceP).comp (hps.pair (hc.pair hb)),?_⟩
  intro x
  dsimp only
  rw [←ofFn_nat_eq_map]
  have hh:∀j (g:Fin j→BooleanNetwork (k x) (w x)) (ps:Fin j→Pack),
      (∀i,(ps i).val.value=erase (g i))→
      ((List.ofFn ps).foldr (fun a b=>compPack (pairPack a b) (c x)) (b x)).val.value=erase (BitArithmetic.productNet (List.ofFn g)):=by
    intro j;induction j with
    | zero=>intro g ps h;simpa only [List.ofFn_zero,List.foldr_nil,BitArithmetic.productNet,BitVec.ofNat_eq_ofNat] using eb x
    | succ j ih=>
      intro g ps h
      rw [List.ofFn_succ,List.foldr_cons,List.ofFn_succ,BitArithmetic.productNet]
      exact compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (h 0) (ih _ _ (fun i=>h i.succ))) (ec x)
  exact hh _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkListEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m K : α→ℕ} {f : ∀x,List (BooleanNetwork (n x) (m x))}
lemma ofFn {g : ∀x,Fin (K x)→BooleanNetwork (n x) (m x)} (hK : Emits ea unaryCode K)
    (hg : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>g x.1 x.2)) :
    NetsEmits ea (fun x=>List.ofFn (g x)):=by
  exact (ofFnDep emptyPack hK hg.canonical).congr (fun x=>by rw [List.map_ofFn])
lemma length (hf : NetsEmits ea f) : Emits ea unaryCode (fun x=>(f x).length):=by
  exact ((ofProcedure (NativeAIG.Emission.listUnaryLength packCode emptyPack)).comp hf).congr (by intro x;exact List.length_map ..)
lemma get (hf : NetsEmits ea f) : NetEmits
    (fun x:Σa,Fin ((f a).length)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>(f x.1).get x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((f a).length)=>(x.2.val,x.1))
  have h:=(ofProcedure (Procedure.listGet packCode emptyPack)).comp (hx.fst.unaryNat.pair (hf.comp hx.snd))
  apply NetEmits.ofCanonical
  exact h.congr (by
    intro x
    simp only [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,List.getElem?_eq_getElem x.2.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem])
lemma product (hn : Emits ea unaryCode n) (hm : Emits ea unaryCode m) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>BitArithmetic.productNet (f x)):=by
  exact (NetEmits.productOfFn hn hm hf.length hf.get).congr (by intro x;rw [List.ofFn_get])
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkListOperationsEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma congrList {f g : ∀x,List (BooleanNetwork (n x) (m x))} (hf : NetsEmits ea f)
    (h : ∀x,f x=g x) : NetsEmits ea g:=hf.congr (fun x=>congrArg (List.map erasePack) (h x))
lemma replicate {f : ∀x,BooleanNetwork (n x) (m x)} (hk : Emits ea unaryCode k) (hf : NetEmits ea f) :
    NetsEmits ea (fun x=>List.replicate (k x) (f x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (k a)=>(x.2.val,x.1))
  exact (ofFn hk (hf.compInput hx.snd)).congrList (by intro x;exact List.ofFn_const _ _)
end NetsEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableArithmeticEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
open BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma componentWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>BitArithmetic.componentWidth (n x)):=
  (hn.unaryMul hn).unarySucc
lemma primeComponent {m p : ∀x,BooleanNetwork (k x) (n x)} (hk : Emits ea unaryCode k)
    (hn : Emits ea unaryCode n) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>BitArithmetic.primeComponent (m x) (p x)):=by
  have hw:=componentWidth hn
  exact (((hm.comp (resize hn hw)).pair ((NetsEmits.replicate hn (hp.comp (resize hn hw))).product hk hw)).comp
    (gcd hw)).comp (resize hw hn)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedArithmeticEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma retainedComponentOrder_oai {a m p : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (n x)}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (ha : NetEmits ea a) (hm : NetEmits ea m) (hp : NetEmits ea p) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedComponentOrder (t x) (a x) (m x) (p x)):=
  retainedOrder hn ht ha (primeComponent (machineWidth hn ht) hn hm hp)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder_oai := @OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder_oai

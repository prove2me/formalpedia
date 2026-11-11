-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:16:33.547398+00:00
-- url     : https://prove2.me/submissions/a0a1b2d4-ae15-4f1b-99c1-42db3065b1dc

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
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalNodeEmission_kernelInitial
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalNodeEmission_update
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_lastNode
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_machineWidth
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_paddedHistory
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_previous

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

lemma wordLe_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLe a b).net.count ≤ a.net.count+b.net.count+48*w+9 := by
  simp only [wordLe,count_bnot]
  have := wordLt_count b a
  omega

lemma wordEq_count (w : ℕ) : (wordEq w).net.count ≤ 96*w+21 := by
  simp only [wordEq,count_bnot,count_bor,count_comp,count_select,zero_add]
  have := ult_count w
  omega

end ExactQuantumFactoring.BitArithmetic


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
lemma subPack_value (w : ℕ) : (binaryPack NativeAIG.sub w).val.value=erase (BitArithmetic.sub w):=by
  apply binaryPack_value
  have hh:=NativeAIG.sub_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma equalOn_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (equalOn a b).net.count ≤ a.net.count+b.net.count+96*w+21 := by
  simp only [equalOn,count_comp,count_pair]
  have := wordEq_count w
  omega

end ExactQuantumFactoring.BitArithmetic


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

lemma any_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (any cs).net.count ≤ cs.length*(c+4)+1 := by
  induction cs with
  | nil => simp [any]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [any,count_bor,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

lemma wordBlocks_count {n s w c : ℕ} (f : Fin s → BooleanNetwork n w)
    (h : ∀ i, (f i).net.count ≤ c) : (wordBlocks f).net.count ≤ s*w*c := by
  apply count_vector_le
  intro i
  simpa only [count_rewire] using h (finProdFinEquiv.symm i).1

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma stackPush_count {k s w : ℕ} (a : BooleanNetwork k w) (v : BooleanNetwork k (s*w)) :
    (stackPush a v).net.count ≤ s*w*(a.net.count+v.net.count) := by
  apply wordBlocks_count
  intro i
  by_cases hi : i.val=0
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=a := dite_eq_left hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh]
    omega
  · have he : (if h : i.val=0 then a else v.comp (blockNet s w ⟨i.val-1,by omega⟩))=
        v.comp (blockNet s w ⟨i.val-1,by omega⟩) := dite_eq_right hi
    have hh := congrArg (fun c : BooleanNetwork k w => c.net.count) he
    rw [hh,count_comp,blockNet_count]
    omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open BooleanNetwork

lemma wordMember_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (wordMember a as).net.count ≤ as.length*(2*c+96*w+25)+1 := by
  have h := any_count (as.map (fun b=>(a.pair b).comp (wordEq w))) (c:=2*c+96*w+21) (by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
    have hh := hs b hb
    have he := wordEq_count w
    simp only [count_comp,count_pair]
    omega)
  simpa only [wordMember,List.length_map,Nat.add_assoc] using h

lemma active_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (active a as).net.count ≤ c+49*w+11+as.length*(2*c+96*w+25) := by
  have hm := wordMember_count a as ha hs
  have hl := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 2)) a
  rw [wordConstant_count] at hl
  simp only [active,count_band,count_bnot]
  omega

lemma pushOne_count {k w c : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushOne s a as).net.count ≤ oneBound s w c as.length := by
  have hac := active_count a as ha hs
  have hsub := sub_count w
  have hh : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))).net.count ≤
      c+159*w+6 := by
    simp only [count_comp,count_pair,liftWord,source,count_select,zero_add,wordConstant_count]
    omega
  have hpush := stackPush_count (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w)
  simp only [queue,count_select,add_zero] at hpush
  have hpush' := hpush.trans (Nat.mul_le_mul_left (s*w) hh)
  simp only [pushOne,count_pair,wordMux_count,count_comp,source,queue,count_select,zero_add,add_zero]
  dsimp only [oneBound]
  omega

lemma oneBound_mono (s w c : ℕ) {r t : ℕ} (h : r ≤ t) : oneBound s w c r ≤ oneBound s w c t := by
  have hh := Nat.mul_le_mul_right (2*c+96*w+25) h
  dsimp only [oneBound]
  omega

/-- The all-child queue update is quadratic in the number of prime fields,
not an exponentially duplicated expression. Bounds hold on ALL inputs. -/
theorem pushAll_count {k w c : ℕ} (s : ℕ) (as : List (BooleanNetwork k w))
    (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushAll s as).net.count ≤ as.length*oneBound s w c as.length := by
  induction as with
  | nil=>simp [pushAll,count_select]
  | cons a as ih=>
    have ha := hs a (by simp)
    have ht : ∀ b∈as,b.net.count ≤ c := fun b hb=> hs b (by simp [hb])
    have hi := ih ht
    have hp := pushOne_count s a as ha ht
    have hb := oneBound_mono s w c (Nat.le_succ as.length)
    simp only [pushAll,count_comp,List.length_cons]
    calc
      _ ≤ as.length*oneBound s w c as.length+oneBound s w c as.length := Nat.add_le_add hi hp
      _ ≤ as.length*oneBound s w c (as.length+1)+oneBound s w c (as.length+1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) hb
      _ = _ := by ring

end ExactQuantumFactoring.BitArithmetic.ChildQueue


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound

lemma eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

end PolyBound




end ExactQuantumFactoring

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
lemma self (len : α→ℕ) : PolyAt len len := ⟨Polynomial.X,fun _=>by simp⟩
lemma add (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a+g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun a=>by simpa using Nat.add_le_add (hp a) (hq a)⟩
lemma mul (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a*g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun a=>by simpa using Nat.mul_le_mul (hp a) (hq a)⟩
lemma pow (hf : PolyAt len f) (k : ℕ) : PolyAt len (fun a=>f a^k) := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨p^k,fun a=>by simpa using Nat.pow_le_pow_left (hp a) k⟩
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
lemma constant (hn : BitStackProgram.Emits ea unaryCode n) {b : α→Bool}
    (hb : BitStackProgram.Emits ea Procedure.boolCode b) :
    NetEmits ea (fun x=>BooleanNetwork.constant (n:=n x) (b x)):=
  ⟨fun x=>constantPack (n x) (b x),(ofProcedure Emission.constantPackP).comp (hn.pair hb),fun _=>constantPack_value _ _⟩
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
lemma precompose {β : Type} {eb : β→List Bool} {n m : β→ℕ}
    {f : ∀x,BooleanNetwork (n x) (m x)} (h : NetEmits eb f) (g : α→β) :
    NetEmits (fun x=>eb (g x)) (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=h
  exact ⟨fun x=>p (g x),hp.precompose g,fun x=>he (g x)⟩
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkLoopEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma anyPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr borPack (constantPack n false)).val.value=erase (BooleanNetwork.any fs):=by
  induction h with
  | nil=>exact constantPack_value n false
  | cons hp hs ih=>exact borPack_value _ _ _ _ hp ih
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
lemma ofFn_forall₂ {α β : Type} {k : ℕ} (f : Fin k→α) (g : Fin k→β)
    (R : α→β→Prop) (h : ∀i,R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g):=by
  induction k with
  | zero=>simp
  | succ k ih=>rw [List.ofFn_succ,List.ofFn_succ];exact .cons (h 0) (ih _ _ (fun i=>h i.succ))
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifierBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (zeroWord a).net.count ≤ a.net.count+97*n+21 := by
  have h := equalOn_count a (wordConstant (n:=k) (BitVec.ofNat n 0))
  rw [wordConstant_count] at h
  dsimp [zeroWord]
  omega

lemma paddedPair_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (paddedPair a b).net.count ≤ 2*a.net.count+2*b.net.count+242*n+57 := by
  have h₁ := zeroWord_count a
  have h₂ := zeroWord_count b
  have h₃ := wordLe_count a b
  simp only [paddedPair,count_bor,count_band,count_bnot]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalCompletionOutput
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork BitArithmetic
namespace Completion

lemma zeros_count (k m : ℕ) : (zeros k m).net.count=m := by
  simp [zeros]

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderNetworks
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
open BooleanNetwork

namespace BooleanNetwork

lemma packNet_count {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    (packNet r a b).net.count=a.net.count+b.net.count+r := by
  simp only [packNet,count_pair,Completion.zeros_count]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachine
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork RecordedHistory

namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

lemma width_eq (t : ℕ) : M.width t=c+t*(FixedSplit.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMachine
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork RecordedHistory

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma width_eq (t : ℕ) : M.width t=c+t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [width]
  | succ t ih=>simp only [width,ih];ring

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortingCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace SortedWords

lemma keepHead_count {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    (keepHead c).net.count=c.net.count := by
  simp only [keepHead,count_pair,count_comp,headNet,tailNet,count_select,zero_add]

lemma compareStep_count (w r : ℕ) : (compareStep w r).net.count ≤ 498*w+114 := by
  have hp := paddedPair_count (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))
  simp only [headNet,tailNet,count_comp,count_select,mul_zero,zero_add] at hp
  simp only [compareStep,count_pair,wordMux_count,headNet,tailNet,count_comp,count_select]
  omega

lemma insertNet_count (w r : ℕ) : (insertNet w r).net.count ≤ r*(498*w+114) := by
  induction r with
  | zero=>simp [insertNet,count_select]
  | succ r ih=>
    have hc := compareStep_count w r
    rw [insertNet,count_comp,keepHead_count,Nat.succ_mul]
    omega
/-- Quadratic number of word comparisons, each a polynomial Boolean network.
No expanded sorting expression duplicates its recursively generated circuits. -/
theorem sortNet_count (w r : ℕ) : (sortNet w r).net.count ≤ r*r*(498*w+114) := by
  induction r with
  | zero=>simp [sortNet,count_select]
  | succ r ih=>
    have hc := insertNet_count w r
    rw [sortNet,count_comp,keepHead_count]
    calc
      _ ≤ r*r*(498*w+114)+r*(498*w+114) := Nat.add_le_add ih hc
      _ ≤ (r+1)*(r+1)*(498*w+114) := by nlinarith

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryAccess
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
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma firstNodeNet_count (t : ℕ) : (M.firstNodeNet t).net.count=0 := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [firstNodeNet,count_comp,previousNet,count_comp,count_select,ih,add_zero]

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeInitialization
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

end NodeMachine
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

end ExactQuantumFactoring

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
lemma natEq {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x=g x)):=(ofProcedure binaryEq).comp (hf.pair hg)
end Emits
end ExactQuantumFactoring.BitStackProgram

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

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {n m : β→ℕ}
lemma input {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits eb f)
    {g : α→β} (hg : Emits ea eb g) : NetEmits ea (fun x=>f (g x)):=by
  obtain ⟨p,hp,he⟩:=hf
  exact ⟨fun x=>p (g x),hp.comp hg,fun x=>he (g x)⟩
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
lemma anyOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.any (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  obtain ⟨pp⟩:=hq
  have hps:=(ofProcedure (Procedure.tabulate (f:=q) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (q x)).foldr borPack (constantPack (n x) false),
    (ofProcedure Emission.anyPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact anyPack_value _ _ (ofFn_forall₂ _ _ _ (fun i=>by rw [eq];exact he ⟨x,i⟩))
lemma wordLt {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLt (a x) (b x)):=(ha.pair hb).comp (ult hm)
lemma wordLe {a b : ∀x,BooleanNetwork (n x) (m x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : Emits ea unaryCode m) :
    NetEmits ea (fun x=>BitArithmetic.wordLe (a x) (b x)):=(wordLt hb ha hm).bnot
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

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w : α→ℕ}
lemma blockNet (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (i : ∀x,Fin (s x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>BitArithmetic.blockNet (s x) (w x) (i x)):=
  selectSlice (hs.unaryMul hw) hw (hw.unaryNat.natMul hi) _ (by intro x j;change j.val+w x*(i x).val=w x*(i x).val+j.val;omega)
lemma wordBlocks {f : ∀x,Fin (s x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (hf : NetEmits (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.wordBlocks (f x)):=by
  let eb:=fun x:Σx,Fin (s x*w x)=>prodCode unaryCode ea (x.2.val,x.1)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σx,Fin (s x*w x)=>(x.2.val,x.1))
  have hW:=hw.comp hx.snd
  have hI:=hx.fst.unaryNat
  have hdiv:= (hI.natDiv hW.unaryNat).boundedUnary hx.fst (by intro x;exact Nat.div_le_self _ _)
  have harg : Emits eb (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1))
      (fun x=>⟨x.1,(finProdFinEquiv.symm x.2).1⟩):=
    (hdiv.pair hx.snd).result (by intro x;rfl)
  have hF:=hf.input harg
  have ho:=hI.natMod hW.unaryNat
  have hb:=hF.rewireSlice (const _ _ 1) ho (fun x _=>(finProdFinEquiv.symm x.2).2)
    (by
      intro x i
      change x.2.val % w x.1 = x.2.val % w x.1 + i.val
      have := i.isLt
      omega)
  exact vectorOfFn hn (hs.unaryMul hw) hb
end NetEmits
end ExactQuantumFactoring.NetworkEmission

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkRecursionEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {K : α→ℕ} {n m : α→ℕ→ℕ}
    {f : ∀x j,BooleanNetwork (n x j) (m x j)}
/-- Saturation makes the loop's intermediate-state bound valid for every
possible invocation, not merely for the one starting at stage zero. -/
lemma boundedStages (hK : Emits ea unaryCode K)
    (h0 : NetEmits ea (fun x=>f x 0))
    (hs : NetEmits
      (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
        (x.1,(x.2.val,erasePack (f x.1 x.2.val))))
      (fun x=>f x.1 (x.2.val+1)))
    (hn : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>n x.1 x.2.val))
    (hm : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>m x.1 x.2.val))
    (hc : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>f x.1 x.2.val)) :
    NetEmits ea (fun x=>f x (K x)):=by
  let F:=fun x j=>erasePack (f x j)
  let ec:=recursionCode (ea:=ea) (eb:=packCode) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.canonical.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>
      (⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;dsimp only [F];rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) packCode
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  have ht : Emits ec packCode (fun x=>F x.1 (min (x.2.val+1) (K x.1))):=
    BitStackProgram.Emits.splitOn c htest hy hz
  have hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(packCode (F x.1 x.2.val)).length):=
    ((PolyAt.const _ 104).mul ((((hn.add hc).add hm).add (PolyAt.const _ 1)).pow 2)).of_le
      (fun x=>packCode_bound _)
  exact ofCanonical (BitStackProgram.Emits.boundedRecursion K F hK h0.canonical ht hb)
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

namespace ExactQuantumFactoring.PolyAt
variable {α : Sort*} {l k f : α→ℕ}
lemma rebase (hf : PolyAt k f) (hk : PolyAt l k) : PolyAt l f:=by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hk
  exact ⟨p.comp q,fun x=>by
    simpa only [Polynomial.eval_comp] using (hp x).trans (PolyBound.eval_mono p (hq x))⟩
end ExactQuantumFactoring.PolyAt

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma lengthPoly {f : α→β} (hf : Emits ea eb f) :
    PolyAt (fun x=>(ea x).length) (fun x=>(eb (f x)).length):=by
  obtain ⟨p⟩:=hf
  exact ⟨Polynomial.X+p.bound,fun x=>by simpa using p.output_length_le x⟩
lemma unaryPoly {f : α→ℕ} (hf : Emits ea unaryCode f) :
    PolyAt (fun x=>(ea x).length) f:=by
  simpa only [unaryCode,List.length_replicate] using hf.lengthPoly
lemma indexCode_poly {k : α→ℕ} (hk : Emits ea unaryCode k) :
    PolyAt (fun x:Σa,Fin (k a)=>(ea x.1).length)
      (fun x=> (prodCode unaryCode ea (x.2.val,x.1)).length):=by
  have hb:=hk.unaryPoly.pull (fun x:Σa,Fin (k a)=>x.1)
  exact (((PolyAt.const _ 2).mul hb).add (PolyAt.self _)).add (PolyAt.const _ 2) |>.of_le (by
    intro x
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate]
    have := x.2.isLt
    omega)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma countPoly {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    NetworkAt (fun x=>(ea x).length) f:=hf.count.unaryPoly
lemma countPolyIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) (m x)}
    (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetworkAt (fun x:Σa,Fin (k a)=>(ea x.1).length) (fun x=>f x.1 x.2):=
  hf.countPoly.rebase hk.indexCode_poly
end ExactQuantumFactoring.NetworkEmission.NetEmits

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
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.initialNet (n x)):=by
  apply completionInitial hn (transitionWidth hn) ((const _ _ 2).unaryMul hn) (hn.unaryMul (hn.unaryPow 5))
  apply tensor hn (hn.unaryPow 5)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin ((n a)^5)=>(x.2.val,x.1))
  exact ListSamplerEmission.singleZero (hn.comp hx.snd)
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.work (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalListSlots.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (work hn)
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
lemma guessWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.guessWidth (n x)):=
  hn.unaryAdd (hn.unaryAdd (hn.unaryAdd (retentionBits hn)))
lemma rawWidth (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.rawWidth (w x) (s x) (n x)):=
  (const _ _ 2).unaryAdd ((width hw (hs.unaryAdd (const _ _ 2))).unaryAdd (guessWidth hn))
end ExactQuantumFactoring.OrderSamplerEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialFieldsEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k u s n b : α→ℕ}
lemma left (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.leftNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hu (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma right (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>BooleanNetwork.rightNet (u x) (b x)):=
  selectSlice (hu.unaryAdd hb) hb hu.unaryNat _ (by intros;rfl)
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProperDivisorEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k w e : α→ℕ}
lemma zeroWord {a : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.zeroWord (a x)):=
  ha.equalOn (by simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)) hw
end ExactQuantumFactoring.NetworkEmission.NetEmits

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_StackEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k s w : α→ℕ}
lemma stackPop (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.stackPop (s x) (w x)):=by
  unfold BitArithmetic.stackPop
  apply wordBlocks (hs.unaryMul hw) hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hS:=hs.comp hx.snd
  have hW:=hw.comp hx.snd
  apply splitOn (fun x=>x.2.val+1 < s x.1) (hx.fst.unarySucc.unaryNat.natLt hS.unaryNat)
  · let inc : {x : Σa,Fin (s a) // x.2.val+1 < s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet (hS.precompose inc) (hW.precompose inc)
      (fun x=>⟨x.val.2.val+1,x.property⟩) (hx.fst.unarySucc.unaryNat.precompose inc)
    exact hb.congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val+1 < s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hz:=wordConst ((hS.unaryMul hW).precompose inc) (hW.precompose inc) (const _ _ 0)
    exact hz.congr (by intro x;rw [dite_eq_right x.property];rfl)
lemma stackPush {a : ∀x,BooleanNetwork (k x) (w x)} {v : ∀x,BooleanNetwork (k x) (s x*w x)}
    (hk : Emits ea unaryCode k) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>BitArithmetic.stackPush (a x) (v x)):=by
  unfold BitArithmetic.stackPush
  apply wordBlocks hk hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  apply splitOn (fun x=>x.2.val=0) (hx.fst.unaryNat.natEq (const _ _ 0))
  · exact ((ha.compInput hx.snd).precompose Subtype.val).congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val=0} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet ((hs.comp hx.snd).precompose inc) ((hw.comp hx.snd).precompose inc)
      (fun x=>⟨x.val.2.val-1,by dsimp only [inc];have:=x.val.2.isLt;omega⟩)
      ((hx.fst.unaryNat.natSub (const _ _ 1)).precompose inc)
    exact (((hv.compInput hx.snd).precompose inc).comp hb).congr (by intro x;rw [dite_eq_right x.property])
end ExactQuantumFactoring.NetworkEmission.NetEmits

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_FirstProperEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_step {β : Type} {K j : ℕ} (f : Fin K→β) (hj : j<K) :
    (List.ofFn f).drop (K-(j+1))=f ⟨K-(j+1),by omega⟩ :: (List.ofFn f).drop (K-j):=by
  rw [List.drop_eq_getElem_cons (by simp only [List.length_ofFn];omega)]
  simp only [List.getElem_ofFn]
  congr 2;omega
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_eq {β : Type} {K : ℕ} (f : Fin K→β) (d : ℕ) :
    (List.ofFn f).drop d=List.ofFn (fun i:Fin (K-d)=>f ⟨d+i.val,by have:=i.isLt;omega⟩):=by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn]
  · intro i h h'
    simp only [List.getElem_drop,List.getElem_ofFn]
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {k w K s : α→ℕ}
lemma wordMemberOfFn {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) (List.ofFn (f x))):=by
  simp only [BitArithmetic.ChildQueue.wordMember,List.map_ofFn]
  apply anyOfFn hk hK
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (K a)=>(x.2.val,x.1))
  exact ((ha.compInput hx.snd).pair hf).comp (wordEq (hw.comp hx.snd))
lemma wordMemberDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) ((List.ofFn (f x)).drop (d x))):=by
  have len:=(hK.unaryNat.natSub hd).boundedUnary hK (fun _=>Nat.sub_le _ _)
  have hh : NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x)
      (List.ofFn (fun i:Fin (K x-d x)=>f x ⟨d x+i.val,by have:=i.isLt;omega⟩))):=by
    apply wordMemberOfFn hk hw len ha
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin (K a-d a)=>(x.2.val,x.1))
    let inc:(Σa,Fin (K a-d a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨d x.1+x.2.val,by have:=x.2.isLt;omega⟩⟩
    have hi:=((hd.comp hx.snd).natAdd hx.fst.unaryNat).boundedUnary (hK.comp hx.snd) (by
      intro x;dsimp only;have:=x.2.isLt;omega)
    exact hf.compInput ((hi.pair hx.snd).recode (by intros;rfl) : Emits _ _ inc)
  exact hh.congr (fun x=>by rw [dropOfFn_eq])
lemma childPushOneDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s) (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushOne (s x) (a x) ((List.ofFn (f x)).drop (d x))):=by
  have hsource:=left hk (hs.unaryMul hw)
  have hqueue:=right hk (hs.unaryMul hw)
  have hwidth:=hk.unaryAdd (hs.unaryMul hw)
  have active:=((wordConst hk hw (const _ _ 2)).wordLt ha hw).band (wordMemberDrop hk hw hK hd ha hf).bnot
  exact hsource.pair ((hsource.comp active).wordMux
    (stackPush hwidth hs hw (((hsource.comp ha).pair (wordConst hwidth hw (const _ _ 1))).comp (sub hw)) hqueue) hqueue (hs.unaryMul hw))
lemma childPushAll {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushAll (s x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.ChildQueue.pushAll (s x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    refine (identity (hk.unaryAdd (hs.unaryMul hw))).congr ?_
    intro x
    dsimp only [F]
    rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp only [List.length_ofFn];exact le_rfl)]
    rfl
  have step : NetEmits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
      (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    have hLen:=hK.comp hx.fst
    let y : (Σa,Fin (K a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨K x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩⟩
    have hi:=(hLen.unaryNat.natSub (hx.snd.fst.unaryNat.natAdd (const _ _ 1))).boundedUnary hLen (fun _=>Nat.sub_le _ _)
    have hy : Emits _ (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) y:=
      (hi.pair hx.fst).recode (by intros;rfl)
    have hfields : NetEmits (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>prodCode unaryCode
        (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (z.2.val,z.1))
        (fun z=>f z.1.1 z.2):=by
      have hz:=(BitStackProgram.Emits.id (prodCode unaryCode (prodCode ea (prodCode unaryCode packCode)))).precompose
        (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(z.2.val,(z.1.1,(z.1.2.val,erasePack (F z.1.1 z.1.2.val)))))
      exact hf.compInput ((hz.fst.pair hz.snd.fst).recode (g:=fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(⟨z.1.1,z.2⟩ : Σa,Fin (K a))) (by intros;rfl))
    have hnew:=(ofCanonical hx.snd.snd).comp (childPushOneDrop (f:=fun x=>f x.1) (a:=fun x=>f (y x).1 (y x).2) (hk.comp hx.fst) (hw.comp hx.fst)
      hLen (hs.comp hx.fst) (hLen.unaryNat.natSub hx.snd.fst.unaryNat) (hf.compInput hy) hfields)
    convert hnew using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.ChildQueue.pushAll]
  have hwidth:=(hk.unaryPoly.add (hs.unaryPoly.mul hw.unaryPoly)).pull (fun x:Σa,Fin (K a+1)=>x.1)
  obtain ⟨p,hp⟩:=countPolyIndexed hK hf
  have hc : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>p.eval (ea x.1).length):=⟨p,fun _=>le_rfl⟩
  have hS:=hs.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hW:=hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hL:=hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hone:=(((hc.add ((PolyAt.const _ 49).mul hW)).add (PolyAt.const _ 11)).add
    (hL.mul ((((PolyAt.const _ 2).mul hc).add ((PolyAt.const _ 96).mul hW)).add (PolyAt.const _ 25)))).add
    ((hS.mul hW).mul ((hc.add ((PolyAt.const _ 159).mul hW)).add (PolyAt.const _ 6))) |>.add
      ((PolyAt.const _ 7).mul (hS.mul hW))
  have hb : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>F x.1 x.2.val):=by
    exact (hL.mul hone).of_le (by
      intro x
      have h:=BitArithmetic.ChildQueue.pushAll_count (s x.1) ((List.ofFn (f x.1)).drop (K x.1-x.2.val))
        (c:=p.eval (ea x.1).length) (by
          intro b hb
          obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hb)
          exact hp ⟨x.1,i⟩)
      have hl:((List.ofFn (f x.1)).drop (K x.1-x.2.val)).length≤K x.1:=by
        simp only [List.length_drop,List.length_ofFn];omega
      exact h.trans (Nat.mul_le_mul hl (BitArithmetic.ChildQueue.oneBound_mono _ _ _ hl)))
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 step hwidth hwidth hb
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NodeControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
open BitArithmetic.NodeCircuit
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma stackWidth (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>(s x+1)*w x):=hs.unarySucc.unaryMul hw
end ExactQuantumFactoring.NodeControlEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeMachineEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NodeMachineEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
lemma width (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(M x).width (t x)):=
  (hc.unaryAdd (ht.unaryMul (((hk.unaryAdd hi).unaryAdd hc).unaryAdd hu))).congr
    (fun x=>((M x).width_eq (t x)).symm)
lemma initial (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initialNet (t x)):=by
  apply NetEmits.boundedStages ht (f:=fun x j=>(M x).initialNet j)
  · exact identity hc
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((M x.1).initialNet x.2.val))))
    have hprev:=ofCanonical hx.snd.snd
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    exact ((hprev.packNet (zeros hC hKW) hC (hi.comp hx.fst)).packNet (zeros hC hC) hC (hu.comp hx.fst))
  · exact hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact ((width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have hb:=(ht.unaryPoly.mul (((hk.unaryPoly.add hi.unaryPoly).add hc.unaryPoly).add hu.unaryPoly)).pull
      (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).initialNet_count]
      exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.NodeMachineEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NodeStateEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {s w : α→ℕ}
lemma width (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : Emits ea unaryCode (fun x=>BitArithmetic.NodeStateCircuit.width (s x) (w x)):=
  ((NodeControlEmission.stackWidth hs hw).unaryAdd (NodeControlEmission.stackWidth hs hw)).unarySucc
lemma pending (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.pending (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (const _ _ 0) _ (by intros;simp only [Function.comp_apply,Fin.val_castAdd,Nat.zero_add])
lemma output (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.output (s x) (w x)):=by
  exact selectSlice (width hs hw) (NodeControlEmission.stackWidth hs hw) (NodeControlEmission.stackWidth hs hw).unaryNat _ (by intros;rfl)
lemma top (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.NodeStateCircuit.top (s x) (w x)):=
  (pending hs hw).comp (blockNet hs.unarySucc hw (fun _=>0) (const _ _ 0))
end ExactQuantumFactoring.NodeStateEmission

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
lemma ordersWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.ordersWidth (n x)):=
  (PhysicalOrderEmission.width hn).tensorWidth (hn.unaryPow 5)
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
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.work (n x)):=(ordersInitial hn).count
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>FixedSplit.width (n x)):=
  ((PhysicalListEmission.launchWidth hn).unaryAdd (ordersWidth hn)).unaryAdd (work hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>FixedSplit.initialNet (n x)):=
  ((identity hn).packNet (zeros hn (PhysicalListEmission.width hn)) hn (PhysicalListEmission.work hn)).packNet
    (zeros hn (ordersWidth hn)) hn (work hn)
end ExactQuantumFactoring.PhysicalSplitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortingEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.SortingEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k w r : α→ℕ}
lemma paddedPair {a b : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.paddedPair (a x) (b x)):=
  (zeroWord hk hw hb).bor ((zeroWord hk hw ha).bnot.band (ha.wordLe hb hw))
lemma head (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.headNet (w x) (r x)):=left hw (hw.tensorWidth hr)
lemma tail (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.tailNet (w x) (r x)):=right hw (hw.tensorWidth hr)
lemma keepHead {a : ∀x,BooleanNetwork (tensorWidth (w x) (r x)) (tensorWidth (w x) (r x))}
    (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.keepHead (a x)):=
  (head hw hr).pair ((tail hw hr).comp ha)
lemma compareStep (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.compareStep (w x) (r x)):=by
  have ha:=head hw hr.unarySucc
  have hb:=(tail hw hr.unarySucc).comp (head hw hr)
  have hrest:=(tail hw hr.unarySucc).comp (tail hw hr)
  have hp:=paddedPair (hw.tensorWidth hr.unarySucc.unarySucc) hw ha hb
  exact (hp.wordMux ha hb hw).pair ((hp.wordMux hb ha hw).pair hrest)
lemma insert (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.insertNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.insertNet (w x) j)
  · exact identity (hw.tensorWidth (const _ _ 1))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.insertNet (w x.1) x.2.val))))
    exact (compareStep (hw.comp hx.fst) hx.snd.fst).comp
      (keepHead (hw.comp hx.fst) hx.snd.fst.unarySucc (ofCanonical hx.snd.snd))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=(hr.unaryPoly.mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.insertNet_count _ _).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma sort (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.sortNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.sortNet (w x) j)
  · exact identity (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.sortNet (w x.1) x.2.val))))
    exact (keepHead (hw.comp hx.fst) hx.snd.fst (ofCanonical hx.snd.snd)).comp (insert (hw.comp hx.fst) hx.snd.fst)
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=((hr.unaryPoly.mul hr.unaryPoly).mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.sortNet_count _ _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by have:=x.2.isLt;omega) (by have:=x.2.isLt;omega))))
end ExactQuantumFactoring.SortingEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitMachineEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.SplitMachineEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n c t : α→ℕ} {M : ∀x,SplitMachine (n x) (c x)}
lemma width (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(M x).width (t x)):=
  (hc.unaryAdd (ht.unaryMul (((hk.unaryAdd hi).unaryAdd hc).unaryAdd hu))).congr
    (fun x=>((M x).width_eq (t x)).symm)
lemma current (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>FixedSplit.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).currentNet (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (by intro x;exact Nat.sub_le _ _)
  have hs:=((ht.unaryNat.natEq (const _ _ 0)).ite (const _ Nat.bits 0)
    (((width hc hk hi hu ht').unaryNat.natAdd hk.unaryNat).natAdd hi.unaryNat))
  apply selectSlice (width hc hk hi hu ht) hc hs (fun x=>(M x).current (t x))
  intro x i
  cases h : t x with
  | zero=>simp only [SplitMachine.current,decide_true,ite_true, if_true,Nat.zero_add];rfl
  | succ j=>simp only [Nat.succ_ne_zero,decide_false,Nat.add_sub_cancel,SplitMachine.current];rfl
end ExactQuantumFactoring.SplitMachineEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma configWidth (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>PhysicalNode.configWidth (n x) (s x)):=
  NodeStateEmission.width hs hn.unarySucc
lemma query (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : NetEmits ea (fun x=>PhysicalNode.query (n x) (s x)):=
  (NodeStateEmission.top hs hn.unarySucc).comp (resize hn.unarySucc hn)
lemma initWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).initWork):=
  (query hn hs).count.unaryAdd (PhysicalSplitEmission.initial hn).count
lemma updateWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).updateWork):=(update hn hs).count
lemma width (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).width (t x)):=
  SplitMachineEmission.width (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma current (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).currentNet (t x)):=
  SplitMachineEmission.current (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma resultField (hn : Emits ea unaryCode n) (i : ∀x,Fin (n x))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>PhysicalNode.resultField (n x) (i x)):=
  ((NodeStateEmission.output ((const _ _ 2).unaryMul hn) hn.unarySucc).comp
    (blockNet ((const _ _ 2).unaryMul hn).unarySucc hn.unarySucc (fun x=>⟨(i x).val,by have:=(i x).isLt;omega⟩) hi)).comp (resize hn.unarySucc hn)
lemma sortedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalNode.sortedOutput (n x)):=by
  apply NetEmits.comp (g:=fun x=>BitArithmetic.SortedWords.sortNet (n x) (n x)) _ (SortingEmission.sort hn hn)
  apply tensor (configWidth hn ((const _ _ 2).unaryMul hn)) hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact resultField (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma kernelWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeKernel.width (n x)):=
  width hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)
end ExactQuantumFactoring.PhysicalNodeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma capacity (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.capacity (n x)):=
  ((const _ _ 2).unaryMul (hn.unaryPow 2)).unarySucc
lemma configWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.configWidth (n x)):=(capacity hn).unaryMul hn
lemma query (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.query (n x)):=
  blockNet (capacity hn) hn (fun _=>0) (const _ _ 0)
lemma nodeResult (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.nodeResult (n x)):=
  (PhysicalNodeEmission.current hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)).comp
    (PhysicalNodeEmission.sortedOutput hn)
lemma fields (hn : Emits ea unaryCode n) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.nodeResult (n x.1)).comp (ExactQuantumFactoring.tensorSelect (n x.1) (n x.1) x.2)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (nodeResult hN).comp (NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat)
lemma old (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.old (n x)):=
  left (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma localNode (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.localNode (n x)):=
  right (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma pushed (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.pushed (n x)):=
  (((localNode hn).pair ((old hn).comp (stackPop (capacity hn) hn))).comp
    (childPushAll (PhysicalNodeEmission.kernelWidth hn) hn hn (capacity hn) (fields hn))).comp
      (right (PhysicalNodeEmission.kernelWidth hn) (configWidth hn))
lemma update (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.update (n x)):=
  (zeroWord ((configWidth hn).unaryAdd (PhysicalNodeEmission.kernelWidth hn)) hn ((old hn).comp (query hn))).wordMux (old hn) (pushed hn) (configWidth hn)
lemma initWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).initWork):=
  (query hn).count.unaryAdd (PhysicalNodeEmission.kernelInitial hn).count
lemma updateWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).updateWork):=(update hn).count
lemma machineInitial (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).initialNet (t x)):=
  NodeMachineEmission.initial (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma start (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.startNet (n x)):=
  stackPush hn (capacity hn) hn (identity hn) (zeros hn (configWidth hn))
lemma steps (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.steps (n x)):=(const _ _ 2).unaryMul (hn.unaryPow 2)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.width (n x)):=machineWidth hn (steps hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.initialNet (n x)):=(start hn).comp (machineInitial hn (steps hn))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma firstNode (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).firstNodeNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).firstNodeNet j)
  · exact lastNode hn (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).firstNodeNet x.2.val))))
    exact (previous (hn.comp hx.fst) hx.snd.fst.unarySucc).comp (ofCanonical hx.snd.snd)
  · exact ((machineWidth hn ht.unarySucc).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact (PhysicalNodeEmission.kernelWidth hn).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact (PolyAt.const _ 0).of_le (fun x=>by rw [NodeMachine.firstNodeNet_count])
lemma flattenWords (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.flattenWords (n x)):=by
  apply wordBlocks (hn.tensorWidth hn) hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat
lemma rootFlat (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>PhysicalTree.rootFlat (n x) (t x)):=by
  apply NetEmits.splitOn (fun x=>t x=0) (ht.unaryNat.natEq (const _ _ 0))
  · let inc:{x:α // t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have h:=(zeros (configWidth hN) (hN.unaryMul hN))
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=0:=x.property
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    rw [hx]
    exact hh
  · let inc:{x:α // ¬t x=0}→α:=Subtype.val
    have hN:=hn.precompose inc
    have hT:=ht.precompose inc
    have hg:=(hT.unaryNat.natSub (const _ _ 1)).boundedUnary hT (fun _=>Nat.sub_le _ _)
    have h:=((firstNode hN hg).comp (nodeResult hN)).comp (flattenWords hN)
    obtain ⟨p,hp,he⟩:=h
    refine ⟨p,hp,?_⟩
    intro x
    have hx : t x.val=(t x.val-1)+1:=by have:=x.property;omega
    have hh:=he x
    dsimp only [inc] at hh
    change (p x).val.value=erase (PhysicalTree.rootFlat (n x.val) (t x.val))
    conv_rhs => rw [hx]
    exact hh
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePreparationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma launchWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWork (n x)):=(initial hn).count
lemma launchWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.launchWidth (n x)):=
  (hn.unaryAdd (width hn)).unaryAdd (launchWork hn)
lemma slots (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.slots (n x)):=
  (((hn.unaryPow 5).unarySucc).unaryMul ((const _ _ 2).unaryMul hn)).unaryMul ((const _ _ 2).unaryMul (hn.unaryPow 2))
lemma padding (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.padding (n x)):=
  ((hn.unaryPow 10).unaryNat.natSub (slots hn).unaryNat).boundedUnary (hn.unaryPow 10) (fun _=>Nat.sub_le _ _)
lemma paddedWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.paddedWidth (n x)):=
  (launchWidth hn).unaryAdd (hn.tensorWidth (padding hn))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeVerificationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma paddedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.paddedOutputNet (n x)):=
  (paddedHistory hn).comp (rootFlat hn (steps hn))
lemma quarterOutput_oai (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.quarterOutputNet (n x)):=
  completionOutput (paddedWidth hn) (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11) (paddedOutput hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput_oai := @OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput_oai

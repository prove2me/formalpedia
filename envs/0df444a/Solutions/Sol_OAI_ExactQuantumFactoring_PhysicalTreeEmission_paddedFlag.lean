-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:12.292905+00:00
-- url     : https://prove2.me/submissions/cef708b0-05c6-409f-a998-1c736429e3d9

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
import Theorems.Thm_OAI_ExactQuantumFactoring_NetworkEmission_NetEmits_factorVerifier
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalNodeEmission_update
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_lastNode
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_machineWidth
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_paddedHistory
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_paddedPad
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_previous
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_retainedSplitFilter
import Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_rowQuery

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanAlgebra
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.BooleanNetwork.count_vector _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

lemma count_sequence {n : ℕ} (cs : List (BooleanNetwork n n)) :
    (sequence cs).net.count = (cs.map (fun c => c.net.count)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [sequence, count_comp, ih]

lemma count_iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) :
    (iterate c k).net.count = k * c.net.count := by
  simp [iterate, count_sequence, List.sum_replicate]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

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

lemma staticPower_count (w e : ℕ) : (staticPower w e).net.count ≤
    w+e*(90*w*w+14*w+6) := by
  simp only [staticPower,count_comp,count_pair,count_select,wordConstant_count,zero_add,
    count_rewire,count_iterate,staticPowerStep]
  have h := mul_count w
  exact Nat.add_le_add_left (Nat.mul_le_mul_left e h) w

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
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.countKnown_nil _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_cast _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_empty _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_get _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_length _root_.OAI.ExactQuantumFactoring.NativeAIG.eraseVec_push _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma all_count {n c : ℕ} (cs : List (BooleanNetwork n 1))
    (h : ∀ a ∈ cs, a.net.count ≤ c) : (all cs).net.count ≤ cs.length*(c+1)+1 := by
  induction cs with
  | nil => simp [all]
  | cons a cs ih =>
    have ha := h a (by simp)
    have hc := ih (fun b hb => h b (by simp [hb]))
    simp only [all,count_band,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BooleanNetwork


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

lemma constMod_count (w d : ℕ) : (constMod w d).net.count ≤ 216*w*w+57*w+6 := by
  simp only [constMod,count_comp,count_pair,count_select,wordConstant_count,zero_add]
  have := mod_count w
  omega

lemma dividesNet_count (w d : ℕ) : (dividesNet w d).net.count ≤ 216*w*w+154*w+27 := by
  have h := equalOn_count (constMod w d) (wordConstant (BitVec.ofNat w 0))
  rw [wordConstant_count] at h
  have := constMod_count w d
  change (equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))).net.count ≤ _
  omega

lemma constPowMod_count (w s j : ℕ) :
    (constPowMod w s j).net.count ≤ 3*w+w*(3672*w*w+436*w+36) := by
  simp only [constPowMod,count_comp,count_pair,count_select,wordConstant_count,count_rewire,zero_add]
  have := modularPower_count w w
  omega

lemma powerOneNet_count (w s j : ℕ) :
    (powerOneNet w s j).net.count ≤ 100*w+21+w*(3672*w*w+436*w+36) := by
  have h := equalOn_count (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))
  rw [wordConstant_count] at h
  have := constPowMod_count w s j
  change (equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))).net.count ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma orderTests_count (w s k : ℕ) : (orderTests w s k).net.count ≤
    k*(100*w+23+w*(3672*w*w+436*w+36))+1 := by
  have h := all_count (c := 100*w+22+w*(3672*w*w+436*w+36))
    (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := powerOneNet_count w s (i.val+1)
      omega)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [orderTests,List.length_ofFn])
  ring

lemma properDivisor_count (w d : ℕ) :
    (properDivisor w d).net.count ≤ 216*w*w+203*w+36 := by
  have h := wordLt_count (wordConstant (n := w) (BitVec.ofNat w d)) (select id)
  rw [wordConstant_count,count_select] at h
  have hd := dividesNet_count w d
  rw [properDivisor,count_band]
  omega

lemma noSmallDivisor_count (w B : ℕ) : (noSmallDivisor w B).net.count ≤
    (B-1)*(216*w*w+203*w+38)+1 := by
  have h := all_count (c := 216*w*w+203*w+37)
    (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot)) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      rw [count_bnot]
      have := properDivisor_count w (i.val+2)
      omega)
  simpa only [noSmallDivisor,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
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
open scoped BigOperators

lemma wordBlocks_count {n s w c : ℕ} (f : Fin s → BooleanNetwork n w)
    (h : ∀ i, (f i).net.count ≤ c) : (wordBlocks f).net.count ≤ s*w*c := by
  apply count_vector_le
  intro i
  simpa only [count_rewire] using h (finProdFinEquiv.symm i).1

lemma addMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (addMod a b m).net.count ≤ a.net.count+b.net.count+m.net.count+
      216*(w+1)^2+142*(w+1)+15 := by
  have h₁ := add_count (w+1)
  have h₂ := mod_count (w+1)
  simp only [addMod,count_rewire,count_comp,count_pair,count_padRight]
  nlinarith

lemma sumMod_count {n w c : ℕ} (m : BooleanNetwork n w) (as : List (BooleanNetwork n w))
    (h : ∀ a ∈ as, a.net.count ≤ c) :
    (sumMod m as).net.count ≤ w+as.length*(c+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  induction as with
  | nil => simp [sumMod,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun b hb => h b (by simp [hb]))
    have hh := addMod_count a (sumMod m as) m
    simp only [sumMod,List.length_cons]
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

lemma cyclicTerm_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) :
    (cyclicTerm a b m k i).net.count ≤ a.net.count+b.net.count+m.net.count+
      (1224*w*w+143*w+12) := by
  have h := mulMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m
  simpa only [cyclicTerm,count_comp,blockNet_count,add_zero] using h

lemma cyclicMulNet_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicMulNet a b m).net.count ≤
      cyclicMulBound s w a.net.count b.net.count m.net.count := by
  apply wordBlocks_count
  intro k
  have h := sumMod_count m (List.ofFn (cyclicTerm a b m k)) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact cyclicTerm_count a b m k i)
  simp only [List.length_ofFn] at h
  
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

lemma arrayConstant_count {n s w : ℕ} (f : Fin s → ℕ) :
    (arrayConstant (n := n) s w f).net.count ≤ s*w*w := by
  apply wordBlocks_count
  intro i
  exact (wordConstant_count _).le

lemma cyclicAddNet_count {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicAddNet a b m).net.count ≤
      s*w*(a.net.count+b.net.count+m.net.count+216*(w+1)^2+142*(w+1)+15) := by
  apply wordBlocks_count
  intro i
  have h := addMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m
  simpa only [count_comp,blockNet_count,add_zero] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma cyclicMulBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicMulBound s w a b c ≤ cyclicMulBound s w a' b' c' := by
  dsimp [cyclicMulBound]
  gcongr

lemma cyclicNew_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicNew s w i).net.count ≤ cyclicStepBound s w := by
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  have hs : sq.net.count ≤ cyclicMulBound s w 0 0 0 := cyclicMulNet_count _ _ _
  have hh : (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count ≤
      cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 :=
    (cyclicMulNet_count sq (cyclicBase s w b) (cyclicMod s w b)).trans
      (cyclicMulBound_mono hs (by rfl) (by rfl))
  simp only [cyclicNew,wordMux_count,cyclicBit,count_bit,zero_add]
  change (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count +
    sq.net.count + 7*(s*w) ≤ cyclicStepBound s w
  dsimp [cyclicStepBound]
  omega

lemma cyclicStep_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicStep s w i).net.count ≤ cyclicStepBound s w := by
  simpa only [cyclicStep,count_pair,count_select,zero_add] using cyclicNew_count s w i

lemma cyclicPrefix_count (s w b k : ℕ) [NeZero s] (hk : k ≤ b) :
    (cyclicPrefix s w b k hk).net.count ≤ k*cyclicStepBound s w := by
  induction k with
  | zero => simp [cyclicPrefix]
  | succ k ih =>
    have h := cyclicStep_count s w (⟨k,by omega⟩ : Fin b)
    have hi := ih (by omega)
    simp only [cyclicPrefix,count_comp]
    nlinarith

lemma cyclicPower_count (s w b : ℕ) [NeZero s] :
    (cyclicPower s w b).net.count ≤ s*w*w+b*cyclicStepBound s w := by
  have h₁ := arrayConstant_count (n := (s*w+w)+b) (s := s) (w := w) (fun i => if i=0 then 1 else 0)
  have h₂ := cyclicPrefix_count s w b b le_rfl
  simp only [cyclicPower,count_comp,count_pair,count_select,count_rewire,zero_add]
  change (arrayConstant s w _).net.count + _ ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma cyclicPowerOn_count {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) :
    (cyclicPowerOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      s*w*w+b*cyclicStepBound s w := by
  have h := cyclicPower_count s w b
  simp only [cyclicPowerOn,count_comp,count_pair]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestBounds
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

lemma cyclicAddBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicAddBound s w a b c ≤ cyclicAddBound s w a' b' c' := by
  dsimp [cyclicAddBound]
  gcongr

lemma cyclicTest_count (s w a : ℕ) [NeZero s] :
    (cyclicTest s w a).net.count ≤ cyclicTestBound s w := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hx : X.net.count ≤ s*w*w := arrayConstant_count _
  have hc : C.net.count ≤ s*w*w := arrayConstant_count _
  have hm : m.net.count=0 := rfl
  have he : e.net.count=0 := rfl
  have ha : (cyclicAddNet X C m).net.count ≤ cyclicAddBound s w (s*w*w) (s*w*w) 0 :=
    (cyclicAddNet_count X C m).trans (cyclicAddBound_mono hx hc (by rfl))
  have hl := cyclicPowerOn_count (cyclicAddNet X C m) m e
  rw [hm,he] at hl
  have hp : (cyclicPowerOn X m e).net.count ≤ 2*(s*w*w)+w*cyclicStepBound s w := by
    have h := cyclicPowerOn_count X m e
    rw [hm,he] at h
    omega
  have hr : rhs.net.count ≤ cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0 :=
    (cyclicAddNet_count (cyclicPowerOn X m e) C m).trans
      (cyclicAddBound_mono hp hc (by rfl))
  have hq := wordEq_count (s*w)
  change ((lhs.pair rhs).comp (wordEq (s*w))).net.count ≤ _
  rw [count_comp,count_pair]
  change (cyclicPowerOn (cyclicAddNet X C m) m e).net.count+rhs.net.count+_ ≤ _
  dsimp [cyclicTestBound]
  omega

lemma cyclicStepBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicStepBound s w ≤ cyclicStepBound s' w' := by
  unfold cyclicStepBound cyclicMulBound
  gcongr

lemma cyclicTestBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicTestBound s w ≤ cyclicTestBound s' w' := by
  unfold cyclicTestBound cyclicAddBound
  gcongr <;> exact cyclicStepBound_mono hs hw

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma rootNext_count (w k : ℕ) : (rootNext w k).net.count ≤ 87*w+6 := by
  simp only [rootNext,count_comp,count_pair,rootGuess,count_select,wordConstant_count,zero_add]
  have := add_count w
  omega

lemma rootStep_count (w e k : ℕ) : (rootStep w e k).net.count ≤
    230*w+21+e*(90*w*w+14*w+6) := by
  have h₁ := rootNext_count w k
  have h₂ := staticPower_count w e
  have h₃ := wordLe_count ((rootNext w k).comp (staticPower w e)) (rootModulus w)
  simp only [count_comp,rootModulus,count_select] at h₃
  simp only [rootStep,count_pair,rootModulus,count_select,zero_add,rootNew,wordMux_count,
    rootGuess,count_select,add_zero]
  omega

lemma rootPrefix_count (w e k : ℕ) : (rootPrefix w e k).net.count ≤
    k*(230*w+21+e*(90*w*w+14*w+6)) := by
  induction k with
  | zero => simp [rootPrefix]
  | succ k ih =>
    have h := rootStep_count w e k
    rw [rootPrefix,count_comp]
    nlinarith

lemma boundedRootNet_count (n e : ℕ) : (boundedRootNet n e).net.count ≤
    rootWidth n+n*(230*rootWidth n+21+e*(90*rootWidth n*rootWidth n+14*rootWidth n+6)) := by
  have h := rootPrefix_count (rootWidth n) e n
  simp only [boundedRootNet,count_comp,count_pair,count_select,wordConstant_count,
    zero_add,count_rewire]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PerfectPowerCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma rootCheck_count (w e : ℕ) : (rootCheck w e).net.count ≤
    146*w+31+e*(90*w*w+14*w+6) := by
  have h₁ := wordLe_count (wordConstant (n := w+w) (BitVec.ofNat w 2)) (rootGuess w)
  have h₂ := wordEq_count w
  have h₃ := staticPower_count w e
  simp only [rootGuess,count_select,wordConstant_count] at h₁
  simp only [rootCheck,count_band,count_comp,count_pair,rootGuess,rootModulus,count_select,
    zero_add,add_zero]
  omega

lemma exponentCheck_count (n e : ℕ) (he : e ≤ n) : (exponentCheck n e).net.count ≤
    perfectCheckBound n := by
  have h₁ := boundedRootNet_count n e
  have h₂ := rootCheck_count (rootWidth n) e
  have h₃ := Nat.mul_le_mul_right (90*rootWidth n*rootWidth n+14*rootWidth n+6) he
  have h₄ := Nat.mul_le_mul_left n h₃
  simp only [exponentCheck,count_comp,count_pair,count_select,zero_add]
  dsimp [perfectCheckBound]
  nlinarith

lemma perfectExponent_count (n : ℕ) (e : Fin (n+1)) :
    (if 2 ≤ e.val then exponentCheck n e.val else
      (constant false : BooleanNetwork (rootWidth n) 1)).net.count ≤ perfectCheckBound n := by
  by_cases he : 2 ≤ e.val
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_left he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=exponentCheck n e.val)
    exact hh.trans_le (exponentCheck_count n e.val (by omega))
  · have hh := congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count)
      (ite_eq_right he : (if 2 ≤ e.val then exponentCheck n e.val else constant false)=constant false)
    apply hh.trans_le
    change 1 ≤ perfectCheckBound n
    dsimp [perfectCheckBound,rootWidth]
    omega

lemma perfectPowerNet_count (n : ℕ) : (perfectPowerNet n).net.count ≤
    (n+1)*(perfectCheckBound n+4)+1 := by
  have h := any_count (c := perfectCheckBound n)
    (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false)) (by
      intro c hc
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hc
      exact perfectExponent_count n e)
  simpa only [perfectPowerNet,List.length_ofFn] using h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedAKS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma allCongruences_count (s w : ℕ) [NeZero s] :
    (allCongruences s w).net.count ≤ 8*s*(cyclicTestBound s w+1)+1 := by
  simpa only [allCongruences,List.length_ofFn] using
    all_count (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1))) (by
      intro c hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact cyclicTest_count s w (i.val+1))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSBounds
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

lemma aksBranch_count (n s : ℕ) [NeZero s] :
    (aksBranch n s).net.count ≤ aksBranchBound n s (rootWidth n) := by
  have hd := dividesNet_count (rootWidth n) s
  have ho := orderTests_count (rootWidth n) s (n^2)
  have hs := noSmallDivisor_count (rootWidth n) (8*s)
  have hc := allCongruences_count s (rootWidth n)
  have hmul : (8*s-1)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) ≤
      (8*s)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) := by gcongr; omega
  simp only [aksBranch,count_band,count_bnot]
  dsimp [aksBranchBound]
  omega

lemma aksBranchBound_mono {n s s' w : ℕ} (hs : s ≤ s') :
    aksBranchBound n s w ≤ aksBranchBound n s' w := by
  unfold aksBranchBound
  gcongr
  exact cyclicTestBound_mono hs le_rfl

lemma aksStaticBranch_count (n s : ℕ) (hs : s ≤ n^8) :
    (aksStaticBranch n s).net.count ≤ aksBranchBound n (n^8) (rootWidth n) := by
  by_cases hp : s.Prime
  · let : NeZero s := ⟨hp.ne_zero⟩
    have he : aksStaticBranch n s = aksBranch n s := dite_eq_left hp
    exact (congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count) he).trans_le
      ((aksBranch_count n s).trans (aksBranchBound_mono hs))
  · have he : aksStaticBranch n s = constant false := dite_eq_right hp
    rw [he]
    change 1 ≤ aksBranchBound n (n^8) (rootWidth n)
    unfold aksBranchBound
    omega

/-- Explicit polynomial size for the full exact primality network. -/
theorem primalityNet_count (n : ℕ) : (primalityNet n).net.count ≤ primalityBound n := by
  have hp := perfectPowerNet_count n
  have ha := any_count (c := aksBranchBound n (n^8) (rootWidth n))
    (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)) (by
      intro c hc
      obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hc
      exact aksStaticBranch_count n s.val (by omega))
  simp only [List.length_ofFn] at ha
  simp only [primalityNet,count_band,count_bnot]
  dsimp [primalityBound]
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordResize
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma resizeWord_count (u w : ℕ) : (resizeWord u w).net.count≤w := by
  have hh := count_vector_le (c:=1)
    (fun i : Fin w => if h : i.val<u then bit ⟨i.val,h⟩ else constant false) (by
      intro i
      by_cases h : i.val<u
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=bit ⟨i.val,h⟩ := dite_eq_left h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp)
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=constant false := dite_eq_right h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp))
  simpa only [resizeWord,mul_one] using hh

end ExactQuantumFactoring.BitArithmetic


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
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifier
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

lemma primeWord_count (n : ℕ) : (primeWord n).net.count≤
    49*n+10+rootWidth n+primalityBound n := by
  have h₁ := wordLe_count (wordConstant (n:=n) (BitVec.ofNat n 2)) (select id)
  have h₂ := resizeWord_count n (rootWidth n)
  have h₃ := primalityNet_count n
  rw [wordConstant_count,count_select] at h₁
  simp only [primeWord,count_band,count_comp]
  omega

end ExactQuantumFactoring.BitArithmetic


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

lemma primeOrZero_count {k n : ℕ} (a : BooleanNetwork k n) :
    (primeOrZero a).net.count ≤ 2*a.net.count+146*n+35+rootWidth n+primalityBound n := by
  have h₁ := zeroWord_count a
  have h₂ := primeWord_count n
  simp only [primeOrZero,count_bor,count_comp]
  omega

lemma paddedPair_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (paddedPair a b).net.count ≤ 2*a.net.count+2*b.net.count+242*n+57 := by
  have h₁ := zeroWord_count a
  have h₂ := zeroWord_count b
  have h₃ := wordLe_count a b
  simp only [paddedPair,count_bor,count_band,count_bnot]
  omega

lemma unpadWord_count {k n : ℕ} (a : BooleanNetwork k n) :
    (unpadWord a).net.count ≤ 2*a.net.count+105*n+21 := by
  have h := zeroWord_count a
  simp only [unpadWord,wordMux_count,wordConstant_count]
  omega

lemma productNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as, a.net.count ≤ c) :
    (productNet as).net.count≤as.length*(c+90*w*w+14*w+6)+w := by
  induction as with
  | nil => simp [productNet,wordConstant_count]
  | cons a as ih =>
    have ha := h a (by simp)
    have hb := ih (fun b hb => h b (by simp [hb]))
    have hm := mul_count w
    simp only [productNet,count_comp,count_pair,List.length_cons]
    nlinarith

lemma candidateProduct_count {k n c : ℕ} (as : Fin n→BooleanNetwork k n)
    (h : ∀ i, (as i).net.count ≤ c) :
    (candidateProduct as).net.count ≤ candidateProductBound n c := by
  have hh := productNet_count (c:=2*c+105*n+21+rootWidth n)
    (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n)))) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have h₁ := unpadWord_count (as i)
      have h₂ := resizeWord_count n (rootWidth n)
      have h₃ := h i
      simp only [count_comp]
      omega)
  simpa only [candidateProduct,candidateProductBound,List.length_ofFn] using hh

lemma factorVerifierOn_count {k n c : ℕ} (N : BooleanNetwork k n)
    (as : Fin n→BooleanNetwork k n) (hN : N.net.count ≤ c) (ha : ∀ i, (as i).net.count ≤ c) :
    (factorVerifierOn N as).net.count≤factorVerifierBound n c := by
  have h₁ := all_count (c:=2*c+146*n+35+rootWidth n+primalityBound n)
    (List.ofFn (fun i => primeOrZero (as i))) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      have := primeOrZero_count (as i)
      have := ha i
      omega)
  have h₂ := all_count (c:=4*c+242*n+57)
    (List.ofFn (fun i : Fin (n*n) =>
      if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
        paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
      else constant true)) (by
      intro a hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      by_cases hij : (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) =
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2) := ite_eq_left hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have := paddedPair_count (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
        have := ha (finProdFinEquiv.symm i).1
        have := ha (finProdFinEquiv.symm i).2
        omega
      · have he : (if (finProdFinEquiv.symm i).1<(finProdFinEquiv.symm i).2 then
              paddedPair (as (finProdFinEquiv.symm i).1) (as (finProdFinEquiv.symm i).2)
            else constant true) = (constant (n:=k) true) := ite_eq_right hij
        have hc := congrArg (fun d : BooleanNetwork k 1 => d.net.count) he
        have ht : (constant (n:=k) true).net.count=1 := rfl
        omega)
  have h₃ := equalOn_count (candidateProduct as) (N.comp (resizeWord n (rootWidth n)))
  have h₄ := candidateProduct_count as ha
  have h₅ := resizeWord_count n (rootWidth n)
  simp only [List.length_ofFn] at h₁ h₂
  rw [show 4*c+242*n+57+1 = 4*c+242*n+58 by omega] at h₂
  simp only [count_comp] at h₃
  simp only [factorVerifierOn,count_band]
  dsimp [factorVerifierBound]
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorWiring
attribute [-instance] _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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
open BooleanNetwork

lemma tensorNetwork_count {n q K : ℕ} (f : Fin K → BooleanNetwork n q) :
    (tensorNetwork f).net.count=∑ i,(f i).net.count := by
  induction K with
  | zero => simp [tensorNetwork]
  | succ K ih => simp only [tensorNetwork,count_pair,ih,Fin.sum_univ_succ]
lemma tensorNetwork_count_le {n q K c : ℕ} (f : Fin K → BooleanNetwork n q)
    (hf : ∀ i,(f i).net.count ≤ c) : (tensorNetwork f).net.count ≤ K*c := by
  rw [tensorNetwork_count]
  calc
    _ ≤ ∑ _ : Fin K,c := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTreeBounds
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
namespace PhysicalNode
lemma resultField_count (n : ℕ) (i : Fin n) : (resultField n i).net.count≤n := by
  have h:=resizeWord_count (n+1) n
  simpa only [resultField,count_comp,NodeStateCircuit.output,count_select,blockNet,count_vector,
    Nat.zero_add] using h
lemma sortedOutput_count (n : ℕ) : (sortedOutput n).net.count ≤ resultBound n := by
  have h₁:=tensorNetwork_count_le (resultField n) (resultField_count n)
  have h₂:=SortedWords.sortNet_count n n
  simp only [sortedOutput,count_comp]
  unfold resultBound
  omega
end PhysicalNode
namespace PhysicalTree
lemma nodeResult_count (n : ℕ) : (nodeResult n).net.count≤PhysicalNode.resultBound n := by
  have h:=PhysicalNode.sortedOutput_count n
  simpa only [nodeResult,count_comp,SplitMachine.currentNet,count_select,Nat.zero_add] using h
lemma resultFields_count (n : ℕ) (i : Fin n) : (resultFields n i).net.count≤PhysicalNode.resultBound n := by
  simpa only [resultFields,count_comp,tensorSelect,count_select,Nat.add_zero] using nodeResult_count n
end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
lemma previousNet_count (t : ℕ) : (M.previousNet t).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastNodeNet_count (t : ℕ) : (M.lastNodeNet t).net.count=0 := by
  simp only [lastNodeNet,count_comp,count_select,Nat.add_zero]
lemma rowQuery_count (t : ℕ) : (M.rowQuery t).net.count=M.query.net.count := by
  simp only [rowQuery,count_comp,M.previousNet_count,currentNet,count_select,Nat.zero_add]
lemma rowFields_count (t : ℕ) (i : Fin n) :
    (M.rowFields t i).net.count≤PhysicalNode.resultBound n := by
  simpa only [rowFields,count_comp,M.lastNodeNet_count,Nat.zero_add] using
    PhysicalTree.resultFields_count n i
lemma rowVerifiedNet_count (t : ℕ) : (M.rowVerifiedNet t).net.count≤M.rowBound := by
  have h₁:=zeroWord_count (M.rowQuery t)
  have h₂:=factorVerifierOn_count (M.rowQuery t) (M.rowFields t)
    (c:=M.query.net.count+PhysicalNode.resultBound n) (by rw [M.rowQuery_count];omega)
    (by intro i;exact (M.rowFields_count t i).trans (Nat.le_add_left _ _))
  rw [M.rowQuery_count] at h₁
  simp only [rowVerifiedNet,count_bor]
  unfold rowBound
  omega
lemma verifiedNet_count (t : ℕ) : (M.verifiedNet t).net.count≤t*(M.rowBound+1)+1 := by
  induction t with
  | zero=>simp only [verifiedNet,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ t ih=>
    have h:=M.rowVerifiedNet_count t
    simp only [verifiedNet,count_band,count_comp,M.previousNet_count,Nat.zero_add]
    nlinarith
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkLoopEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma allPack_value {n : ℕ} (ps : List Pack) (fs : List (BooleanNetwork n 1))
    (h : List.Forall₂ (fun p f=>p.val.value=erase f) ps fs) :
    (ps.foldr bandPack (constantPack n true)).val.value=erase (BooleanNetwork.all fs):=by
  induction h with
  | nil=>exact constantPack_value n true
  | cons hp hs ih=>exact bandPack_value _ _ _ _ hp ih
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
lemma allIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k) (p : α→ℕ→Pack)
    (hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1))
    (he : ∀x i,(p x i.val).val.value=erase (f x i)) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (f x))):=by
  obtain ⟨pp⟩:=hp
  have hps:=(ofProcedure (Procedure.tabulate (f:=p) emptyPack pp)).comp (hk.pair (id ea))
  refine ⟨fun x=>((List.range (k x)).map (p x)).foldr bandPack (constantPack (n x) true),
    (ofProcedure Emission.allPackP).comp (hn.pair hps),?_⟩
  intro x
  dsimp only;rw [←ofFn_nat_eq_map]
  exact allPack_value _ _ (ofFn_forall₂ _ _ _ (he x))
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
lemma allOfFn {f : ∀x,Fin (k x)→BooleanNetwork (n x) 1}
    (hn : Emits ea unaryCode n) (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σx,Fin (k x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BooleanNetwork.all (List.ofFn (f x))):=by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨q,hq,eq⟩:=extendPack hk p hp
  exact allIndexed hn hk q hq (by intro x i;rw [eq];exact he ⟨x,i⟩)
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilter
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
lemma filterStep_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).depth=s.depth-1:=by cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_depth {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).depth=s.depth-i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_depth,ih,Nat.sub_sub]
lemma filterStep_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) :
    (filterStep prev keep s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep (filterStep prev keep s).depth (filterStep prev keep s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  cases s with | mk d v ps=>cases d <;> rfl
lemma filterRun_value {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : FilterState k w) (i : ℕ) :
    ((filterStep prev keep)^[i] s).pending.foldl BooleanNetwork.band
      (filterPrefix prev keep ((filterStep prev keep)^[i] s).depth ((filterStep prev keep)^[i] s).raw)=
    s.pending.foldl BooleanNetwork.band (filterPrefix prev keep s.depth s.raw):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',filterStep_value,ih]
lemma filterRun_result {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) (s : ℕ) (v : BooleanNetwork k (w s)) :
    ((filterStep prev keep)^[s] ⟨s,v,[]⟩).pending.foldl BooleanNetwork.band (BooleanNetwork.constant true)=
      filterPrefix prev keep s v:=by
  have h:=filterRun_value prev keep (⟨s,v,[]⟩ : FilterState k w) s
  have hd:=filterRun_depth prev keep (⟨s,v,[]⟩ : FilterState k w) s
  dsimp only at hd
  rw [Nat.sub_self] at hd
  generalize he : ((filterStep prev keep)^[s] ⟨s,v,[]⟩)=r at *
  cases r with | mk d a ps=>
    dsimp only [FilterState.depth] at hd
    subst d
    exact h
lemma filterRun_bounds {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1)
    (hp : ∀s,(prev s).net.count=0) (S B C : ℕ)
    (hc : ∀s,S>s→∀v: BooleanNetwork k (w (s+1)),v.net.count≤B→(keep s v).net.count≤C)
    (v : BooleanNetwork k (w S)) (hv : v.net.count≤B) (i : ℕ) :
    let r := ((filterStep prev keep)^[i] ⟨S,v,[]⟩);
    r.depth ≤ S ∧ r.raw.net.count ≤ B ∧ r.pending.length ≤ i ∧ (∀ a ∈ r.pending, a.net.count ≤ C) := by
  induction i with
  | zero=>exact ⟨le_rfl,hv,le_rfl,by simp⟩
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    generalize he : ((filterStep prev keep)^[i] ⟨S,v,[]⟩)=r at *
    rcases ih with ⟨hd,hv,hl,hc'⟩
    cases r with | mk d a ps=>
      cases d with
      | zero=>exact ⟨hd,hv,hl.trans (by omega),hc'⟩
      | succ d=>
        dsimp only [FilterState.depth,FilterState.raw,FilterState.pending] at hd hv hl hc'
        refine ⟨by dsimp only [filterStep];omega,?_,?_,?_⟩
        · simpa only [filterStep,BooleanNetwork.count_comp,hp,Nat.add_zero] using hv
        · dsimp only [filterStep];simp only [List.length_cons];omega
        · intro a ha
          rcases List.mem_cons.mp ha with h|h
          · subst a;exact hc d (by omega) _ hv
          · exact hc' a h
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound
lemma const (c : ℕ) : PolyBound (fun _ => c) :=
  ⟨Polynomial.C c, fun _ => by simp⟩
lemma id : PolyBound (fun n => n) := ⟨Polynomial.X, fun _ => by simp⟩
lemma add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q, fun n => by simpa using Nat.add_le_add (hp n) (hq n)⟩
lemma mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n * g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q, fun n => by simpa using Nat.mul_le_mul (hp n) (hq n)⟩
lemma pow {f : ℕ → ℕ} (hf : PolyBound f) (k : ℕ) :
    PolyBound (fun n => f n ^ k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k, fun n => by simpa using Nat.pow_le_pow_left (hp n) k⟩
lemma of_le {f g : ℕ → ℕ} (hg : PolyBound g) (h : ∀ n, f n ≤ g n) : PolyBound f := by
  obtain ⟨p,hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩
lemma max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)
lemma sub {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n-g n) :=
  hf.of_le (fun _ => Nat.sub_le _ _)
lemma div {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n/g n) :=
  hf.of_le (fun _ => Nat.div_le_self _ _)
lemma mod {f g : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => f n%g n) :=
  hf.of_le (fun _ => Nat.mod_le _ _)

lemma eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma natSize {f : ℕ → ℕ} (hf : PolyBound f) : PolyBound (fun n => (f n).size) :=
  hf.of_le (fun _ => Nat.size_le.mpr (Nat.lt_two_pow_self))
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
lemma comp {h : ℕ→ℕ} (hh : PolyBound h) (hf : PolyAt len f) :
    PolyAt len (fun a=>h (f a)) := by
  obtain ⟨p,hp⟩:=hh; obtain ⟨q,hq⟩:=hf
  refine ⟨p.comp q,fun a=>?_⟩
  simpa only [Polynomial.eval_comp] using
    (hp (f a)).trans (PolyBound.eval_mono p (hq a))
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionGeneralStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {K : α→ℕ} {F : α→ℕ→β}
lemma stages (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>F x 0))
    (hs : Emits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,F x.1 x.2.val))) eb
      (fun x=>F x.1 (x.2.val+1)))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>(eb (F x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>F x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K F
  let c:=fun x:Σa,Fin (K a+1)=>x.2.val<K x.1
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode eb))).precompose
    (fun x:Σa,Fin (K a+1)=>(x.1,(x.2.val,F x.1 x.2.val)))
  have htest:=hx.snd.fst.unaryNat.natLt (hK.comp hx.fst).unaryNat
  have hy : Emits (fun x:{a:Σa,Fin (K a+1) // c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    have h:=hs.precompose (fun x:{a:Σa,Fin (K a+1) // c a}=>(⟨x.val.1,⟨x.val.2.val,x.property⟩⟩ : Σa,Fin (K a)))
    exact h.congr (by intro x;rw [Nat.min_eq_left (by have:=x.property;dsimp only [c] at this;omega)])
  have hz : Emits (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>ec x.val) eb
      (fun x=>F x.val.1 (min (x.val.2.val+1) (K x.val.1))):=by
    exact (hx.snd.snd.precompose (fun x:{a:Σa,Fin (K a+1) // ¬c a}=>x.val)).congr (by
      intro x
      change F x.val.1 x.val.2.val=F x.val.1 _
      congr 1
      have := x.property
      have := x.val.2.isLt
      dsimp only [c] at *
      omega)
  exact boundedRecursion K F hK h0 (splitOn c htest hy hz) hb
end ExactQuantumFactoring.BitStackProgram.Emits

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
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace NetworkAt
variable {α : Type*} {len a b c : α→ℕ}
lemma of_le {f : ∀x,BooleanNetwork (a x) (b x)} {bound : α→ℕ} (hb : PolyAt len bound)
    (h : ∀x,(f x).net.count≤bound x) : NetworkAt len f := hb.of_le h
lemma pull {β : Type*} {f : ∀x,BooleanNetwork (a x) (b x)} (hf : NetworkAt len f) (g : β→α) :
    NetworkAt (fun y=>len (g y)) (fun y=>f (g y)) := PolyAt.pull hf g
end NetworkAt
end ExactQuantumFactoring

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
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma countPoly {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    NetworkAt (fun x=>(ea x).length) f:=hf.count.unaryPoly
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
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilterEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.divisor_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pending_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.top_count
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
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
lemma FilterState.positiveView_eq {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0 < r.depth) :
    (⟨(r.positiveView h).1+1,(r.positiveView h).2.1,(r.positiveView h).2.2⟩ : FilterState k w)=r:=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>rfl
namespace NetsEmits
lemma foldlBand {α : Type} {ea : α→List Bool} {k : α→ℕ}
    {f : ∀x,List (BooleanNetwork (k x) 1)} (hk : Emits ea unaryCode k) (hf : NetsEmits ea f) :
    NetEmits ea (fun x=>(f x).foldl BooleanNetwork.band (BooleanNetwork.constant true)):=by
  let p:=Emission.foldRightPack (f:=fun a b=>bandPack b a) 4 (by intro a b; dsimp [bandPack,compPack,pairPack,nodePack]; omega)
    (Emission.bandPackP.comp ((Procedure.second packCode packCode).pair (Procedure.first packCode packCode)))
  have hi:=(ofProcedure Emission.constantPackP).comp (hk.pair (const _ _ true))
  have hr:=(ofProcedure (Procedure.listReverse packCode emptyPack)).comp hf
  refine ⟨fun x=>((f x).map erasePack).foldl bandPack (constantPack (k x) true),
    ((ofProcedure p).comp (hr.pair hi)).congr (fun x=>by dsimp only;rw [List.foldr_reverse]),?_⟩
  intro x
  dsimp only
  have hgen : ∀(fs:List (BooleanNetwork (k x) 1)) (a:Pack) (b:BooleanNetwork (k x) 1),a.val.value=erase b→
      ((fs.map erasePack).foldl bandPack a).val.value=erase (fs.foldl BooleanNetwork.band b):=by
    intro fs
    induction fs with
    | nil=>intro a b h;exact h
    | cons c cs ih=>intro a b h;exact ih _ _ (bandPack_value _ _ _ _ h rfl)
  exact hgen _ _ _ (constantPack_value _ true)
end NetsEmits
lemma filterPrefixEmitter {α : Type} {ea : α→List Bool} {k S B C W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hc : ∀x s,s<S x→∀v: BooleanNetwork (k x) (w x (s+1)),v.net.count≤B x→(keep x s v).net.count≤C x)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x))) (hv : ∀x,(v x).net.count≤B x)
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hB : PolyAt (fun x=>(ea x).length) B) (hC : PolyAt (fun x=>(ea x).length) C)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hstep : Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0 < r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let R:=fun x i=>(filterStep (prev x) (keep x))^[i] (⟨S x,v x,[]⟩ : FilterState (k x) (w x))
  have h0 : Emits ea filterCode (fun x=>(R x 0).code):=
    hS.pair (hV.canonical.pair (const _ _ []))
  have hs : Emits (fun x:Σa,Fin (S a)=>prodCode ea (prodCode unaryCode filterCode) (x.1,(x.2.val,(R x.1 x.2.val).code)))
      filterCode (fun x=>(R x.1 (x.2.val+1)).code):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode filterCode))).precompose
      (fun x:Σa,Fin (S a)=>(x.1,(x.2.val,(R x.1 x.2.val).code)))
    let g : (Σa,Fin (S a))→Σa,{r:FilterState (k a) (w a) // 0 < r.depth}:=fun x=>⟨x.1,R x.1 x.2.val,by
      dsimp only [R];rw [filterRun_depth];dsimp only;exact Nat.sub_pos_of_lt x.2.isLt⟩
    have hh:=hstep.comp ((hx.fst.pair hx.snd.snd).recode (g:=g) (fun _=>rfl))
    exact hh.congr (fun x=>by dsimp only [g,R];rw [Function.iterate_succ_apply'])
  have hb : PolyAt (fun x:Σa,Fin (S a+1)=>(ea x.1).length) (fun x=>(filterCode (R x.1 x.2.val).code).length):=by
    have hs:=hS.unaryPoly
    have hh:=hk.unaryPoly
    let P:= (PolyAt.const _ 104).mul ((((hh.add hB).add hW).add (PolyAt.const _ 1)).pow 2)
    let Q:= (PolyAt.const _ 104).mul ((((hh.add hC).add (PolyAt.const _ 1)).add (PolyAt.const _ 1)).pow 2)
    apply (((PolyAt.const _ 2).mul hs).add (((PolyAt.const _ 2).mul P).add
      ((hs.mul (((PolyAt.const _ 2).mul Q).add (PolyAt.const _ 2))).add (PolyAt.const _ 5)))).pull
        (fun x:Σa,Fin (S a+1)=>x.1) |>.of_le
    intro x
    obtain ⟨hd,hr,hl,hls⟩:=filterRun_bounds (prev x.1) (keep x.1) (hp x.1) (S x.1) (B x.1) (C x.1) (hc x.1) (v x.1) (hv x.1) x.2.val
    have ht:=hw x.1 (R x.1 x.2.val).depth hd
    have hraw:=packCode_bound (erasePack (R x.1 x.2.val).raw)
    have hraw' : (packCode (erasePack (R x.1 x.2.val).raw)).length≤104*(k x.1+B x.1+W x.1+1)^2:=
      hraw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [erasePack,R] at *;omega) 2))
    have hlist:=listCode_length_bound packCode ((R x.1 x.2.val).pending.map erasePack) (104*(k x.1+C x.1+1+1)^2) (by
      intro a ha;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
      exact (packCode_bound _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
        have hh:=hls b hb;dsimp only [erasePack];omega) 2)))
    simp only [filterCode,FilterState.code,prodCode,pairBits_length,unaryCode,List.length_replicate,List.length_map] at hlist ⊢
    dsimp only [R] at *
    have hi:=x.2.isLt
    nlinarith
  have hf:=BitStackProgram.Emits.stages (F:=fun x i=>(R x i).code) hS h0 hs hb
  exact (NetsEmits.foldlBand hk hf.snd.snd).congr (fun x=>filterRun_result (prev x) (keep x) (S x) (v x))
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingStepEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterStepEmitter {α : Type} {ea : α→List Bool} {k : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hc : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    Emits (fun x:Σa,{r:FilterState (k a) (w a) // 0 < r.depth}=>prodCode ea filterCode (x.1,x.2.val.code))
      filterCode (fun x=>(filterStep (prev x.1) (keep x.1) x.2.val).code):=by
  let ix:=Σa,Σs,BooleanNetwork (k a) (w a (s+1)) × List (BooleanNetwork (k a) 1)
  let enc:ix→List Bool:=fun x=>prodCode ea filterCode (x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack))
  have hx:=(BitStackProgram.Emits.id (prodCode ea filterCode)).precompose
    (fun x:ix=>(x.1,(x.2.1+1,erasePack x.2.2.1,x.2.2.2.map erasePack)))
  have hd: Emits enc unaryCode (fun x=>x.2.1):=
    ((hx.snd.fst.unaryNat.natSub (const _ _ 1)).boundedUnary hx.snd.fst (fun _=>Nat.sub_le _ _)).congr (fun _=>by dsimp only;omega)
  have hp':=hp.compInput (hx.fst.pair hd)
  have hr:=NetEmits.ofCanonical hx.snd.snd.fst
  have hraw:=(hr.comp hp').canonical
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1,x.2.2.1⟩
  have hk:=hc.canonical.comp ((hx.fst.pair (hd.pair hx.snd.snd.fst)).recode (g:=g) (fun _=>rfl))
  have hs:=hd.pair (hraw.pair (hk.listCons hx.snd.snd.snd))
  let view:(Σa,{r:FilterState (k a) (w a) // 0 < r.depth})→ix:=fun x=>⟨x.1,x.2.val.positiveView x.2.property⟩
  have h:=hs.precompose view
  have he : (fun x=>enc (view x))=(fun x:Σa,{r:FilterState (k a) (w a) // 0 < r.depth}=>prodCode ea filterCode (x.1,x.2.val.code)):=by
    funext x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>prodCode ea filterCode (x.1,r.code)) hv
  change Emits (fun x=>enc (view x)) filterCode _ at h
  rw [he] at h
  exact h.congr (by
    intro x
    have hv:=x.2.val.positiveView_eq x.2.property
    exact congrArg (fun r=>(filterStep (prev x.1) (keep x.1) r).code) hv)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingPrefixAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterPrefixEmits {α : Type} {ea : α→List Bool} {k S W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x)))
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hep : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hec : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let ix:=Σa,Σs:Fin (S a),{r:BooleanNetwork (k a) (w a (s.val+1)) // r.net.count≤(v a).net.count}
  let enc:ix→List Bool:=fun x=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1.val,erasePack x.2.2.val))
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:ix=>(x.1,(x.2.1.val,erasePack x.2.2.val)))
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1.val,x.2.2.val⟩
  have he:=hec.compInput (hx.recode (g:=g) (fun _=>rfl))
  have hb : PolyAt (fun x:ix=>(ea x.1).length) (fun x=>(enc x).length):=by
    have hbound:=(PolyAt.const _ 104).mul ((((hk.unaryPoly.add hV.countPoly).add hW).add (PolyAt.const _ 1)).pow 2)
    apply ((((PolyAt.const _ 2).mul (PolyAt.self _)).add
      (((PolyAt.const _ 2).mul hS.unaryPoly).add hbound)).add (PolyAt.const _ 2)).pull (fun x:ix=>x.1) |>.of_le
    intro x
    have hs:=x.2.1.isLt
    have hc:=x.2.2.property
    have hw':=hw x.1 (x.2.1.val+1) (by omega)
    have hp':=(packCode_bound (erasePack x.2.2.val)).trans
      (Nat.mul_le_mul_left 104 (Nat.pow_le_pow_left (show k x.1+x.2.2.val.net.count+w x.1 (x.2.1.val+1)+1≤
        k x.1+(v x.1).net.count+W x.1+1 by omega) 2))
    simp only [enc,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega
  obtain ⟨p,hp'⟩:=he.countPoly.rebase hb
  exact filterPrefixEmitter (C:=fun x=>p.eval (ea x).length) prev keep hp
    (fun x s hs r hr=>hp' ⟨x,⟨s,hs⟩,r,hr⟩) hw v (fun _=>le_rfl) hS hk hV
    hV.countPoly ⟨p,fun _=>le_rfl⟩ hW (filterStepEmitter prev keep hep hec)
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
lemma steps (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.steps (n x)):=(const _ _ 2).unaryMul (hn.unaryPow 2)
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
lemma slots (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.slots (n x)):=
  (((hn.unaryPow 5).unarySucc).unaryMul ((const _ _ 2).unaryMul hn)).unaryMul ((const _ _ 2).unaryMul (hn.unaryPow 2))
lemma padding (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.padding (n x)):=
  ((hn.unaryPow 10).unaryNat.natSub (slots hn).unaryNat).boundedUnary (hn.unaryPow 10) (fun _=>Nat.sub_le _ _)
lemma padFlag (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.padFlag (n x)):=by
  apply allOfFn (hn.tensorWidth (padding hn)) (padding hn)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (PhysicalTree.padding (n a))=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (zeroWord (hN.tensorWidth (padding hN)) hN (NetEmits.tensorSelect hN (padding hN) (fun x=>x.2) hx.fst.unaryNat)).bnot
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BitArithmetic
namespace PreparationPolynomial
variable {α : Sort*} {len s w a b c : α→ℕ}
lemma cyclicMulBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicMulBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicMulBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul (hw.add (hs.mul ((((((ha.add hb).add ((PolyAt.const len 2).mul hc)).add
    (((((PolyAt.const len 1224).mul hw).mul hw).add ((PolyAt.const len 143).mul hw)).add (PolyAt.const len 12))).add
    ((PolyAt.const len 216).mul (hwp.pow 2))).add ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15))))
lemma cyclicAddBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicAddBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicAddBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul ((((((ha.add hb).add hc).add ((PolyAt.const len 216).mul (hwp.pow 2))).add
    ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15)))
lemma cyclicStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicStepBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hm:=cyclicMulBound_poly hs hw h0 h0 h0
  exact ((cyclicMulBound_poly hs hw hm h0 h0).add hm).add ((PolyAt.const len 7).mul (hs.mul hw))
lemma cyclicTestBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicTestBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hsw:=(hs.mul hw).mul hw
  have hstep:=hw.mul (cyclicStepBound_poly hs hw)
  exact (((((cyclicAddBound_poly hs hw hsw hsw h0).add hsw).add hstep).add
    (cyclicAddBound_poly hs hw (((PolyAt.const len 2).mul hsw).add hstep) hsw h0)).add
      ((PolyAt.const len 96).mul (hs.mul hw))).add (PolyAt.const len 21)
lemma rootWidth_poly : PolyBound rootWidth := by unfold rootWidth;repeat' (with_reducible_and_instances first | assumption | exact PolyBound.id | exact PolyBound.const _ | apply PolyBound.mul | apply PolyBound.add | apply PolyBound.pow | apply PolyBound.max | apply PolyBound.sub | apply PolyBound.div | apply PolyBound.mod | apply PolyBound.natSize)
lemma perfectCheckBound_poly : PolyBound perfectCheckBound := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hb:=((((PolyBound.const 90).mul hr).mul hr).add ((PolyBound.const 14).mul hr)).add (PolyBound.const 6)
  exact ((((PolyBound.const 147).mul hr).add (PolyBound.const 31)).add
    (hn.mul ((((PolyBound.const 230).mul hr).add (PolyBound.const 21)).add (hn.mul hb)))).add (hn.mul hb)
lemma aksBranchBound_poly : PolyBound (fun n=>aksBranchBound n (n^8) (rootWidth n)) := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hc : PolyBound (fun n=>cyclicTestBound (n^8) (rootWidth n)) :=
    cyclicTestBound_poly ((PolyAt.self (id : ℕ→ℕ)).pow 8) hr
  have hbase:=(((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 154).mul hr)).add
    (PolyBound.const 27)).add (PolyBound.const 1)
  have hstep:=(((((PolyBound.const 3672).mul hr).mul hr).add ((PolyBound.const 436).mul hr)).add (PolyBound.const 36))
  have hord:=((hn.pow 2).mul ((((PolyBound.const 100).mul hr).add (PolyBound.const 23)).add (hr.mul hstep))).add (PolyBound.const 1)
  have hdiv:=(((PolyBound.const 8).mul (hn.pow 8)).mul
    (((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 203).mul hr)).add (PolyBound.const 38))).add (PolyBound.const 1)
  have hcon:=(((PolyBound.const 8).mul (hn.pow 8)).mul (hc.add (PolyBound.const 1))).add (PolyBound.const 1)
  exact (((hbase.add hord).add hdiv).add hcon).add (PolyBound.const 3)
lemma primalityBound_poly : PolyBound primalityBound := by
  have hn:=PolyBound.id
  exact (((hn.add (PolyBound.const 1)).mul (perfectCheckBound_poly.add (PolyBound.const 4))).add
    (PolyBound.const 1)).add (PolyBound.const 1) |>.add
      ((((hn.pow 8).add (PolyBound.const 1)).mul (aksBranchBound_poly.add (PolyBound.const 4))).add (PolyBound.const 1)) |>.add (PolyBound.const 1)
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedPrefixPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace SplitMachine
lemma previousNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.previousNet s).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
end SplitMachine
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedQuarterPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma factorVerifierBound_at {α : Type*} {len n c : α→ℕ}
    (hn : PolyAt len n) (hc : PolyAt len c) :
    PolyAt len (fun x=>factorVerifierBound (n x) (c x)) := by
  have hr:=PolyAt.comp rootWidth_poly hn
  have hp:=PolyAt.comp primalityBound_poly hn
  have hprod:= (hn.mul ((((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 105).mul hn)).add
    (PolyAt.const len 21)).add hr).add (((PolyAt.const len 90).mul hr).mul hr)).add
    ((PolyAt.const len 14).mul hr)).add (PolyAt.const len 6))).add hr
  have hfirst:= (hn.mul (((((((PolyAt.const len 2).mul hc).add ((PolyAt.const len 146).mul hn)).add
    (PolyAt.const len 35)).add hr).add hp).add (PolyAt.const len 1))).add (PolyAt.const len 1)
  have hsecond:= ((hn.mul hn).mul ((((PolyAt.const len 4).mul hc).add
    ((PolyAt.const len 242).mul hn)).add (PolyAt.const len 58))).add (PolyAt.const len 1)
  exact ((((hfirst.add hsecond).add (PolyAt.const len 1)).add
    ((((hprod.add hc).add hr).add ((PolyAt.const len 96).mul hr)).add (PolyAt.const len 21))).add
      (PolyAt.const len 1))
lemma physicalResultBound : PolyBound PhysicalNode.resultBound := by
  exact (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
    (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
end PreparationPolynomial
namespace NodeMachine
lemma rowBound_at {α : Type*} {len n c : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (hq : NetworkAt len (fun x=>(M x).query)) :
    PolyAt len (fun x=>(M x).rowBound) := by
  have hr:=PolyAt.comp PreparationPolynomial.physicalResultBound hn
  exact (((PolyAt.add hq ((PolyAt.const len 97).mul hn)).add (PolyAt.const len 25)).add
    (PreparationPolynomial.factorVerifierBound_at hn (PolyAt.add hq hr)))
lemma verifiedNet_at {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
    (hn : PolyAt len n) (ht : PolyAt len t) (hq : NetworkAt len (fun x=>(M x).query)) :
    NetworkAt len (fun x=>(M x).verifiedNet (t x)) :=
  NetworkAt.of_le ((ht.mul ((rowBound_at hn hq).add (PolyAt.const len 1))).add (PolyAt.const len 1))
    (fun x=>(M x).verifiedNet_count (t x))
end NodeMachine
end ExactQuantumFactoring

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
lemma rowFields (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.machine (n x.1)).rowFields (t x.1) x.2):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact (lastNode (hn.comp hx.snd) (ht.comp hx.snd)).comp (fields hn)
lemma rowVerified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).rowVerifiedNet (t x)):=
  (zeroWord (machineWidth hn ht.unarySucc) hn (rowQuery hn ht)).bor
    (factorVerifier (machineWidth hn ht.unarySucc) hn (rowQuery hn ht) (rowFields hn ht))
lemma verified (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea
    (fun x=>(PhysicalTree.machine (n x)).verifiedNet (t x)):=by
  apply boundedStages ht (f:=fun x j=>(PhysicalTree.machine (n x)).verifiedNet j)
  · exact constant (configWidth hn) (const _ _ true)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((PhysicalTree.machine (n x.1)).verifiedNet x.2.val))))
    exact ((previous (hn.comp hx.fst) hx.snd.fst).comp (ofCanonical hx.snd.snd)).band (rowVerified (hn.comp hx.fst) hx.snd.fst)
  · exact ((machineWidth hn ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [NodeMachine.width_eq,NodeMachine.width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · exact PolyAt.const _ 1
  · exact NodeMachine.verifiedNet_at (hn.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
      ((ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
      ((query hn).countPoly.pull (fun x:Σa,Fin (t a+1)=>x.1))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedNodeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma previous (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).previousNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (firstSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
lemma lastSplit (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) :
    NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).lastSplitNet (t x)):=
  (firstSelect (((width hn hs ht).unaryAdd (PhysicalSplitEmission.width hn)).unaryAdd (initWork hn hs))
    (configWidth hn hs) (updateWork hn hs)).comp (targetSelect (width hn hs ht) (PhysicalSplitEmission.width hn) (initWork hn hs))
end ExactQuantumFactoring.PhysicalNodeEmission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma nodePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalNode.machine n (2*n)).width s)) :
    filterPrefix (fun s=>(PhysicalNode.machine n (2*n)).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedSplitFilter hn t (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s))) s v=
      (PhysicalTree.machine n).nodePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.nodePrefixFilter];rw [ih]
lemma nodePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalNode.machine (n x) (2*n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).nodePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have h2:=(const _ _ 2).unaryMul hn
  have hW:=PhysicalNodeEmission.width hn h2 hs
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalNode.machine (n x.1) (2*n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact PhysicalNodeEmission.previous (hn.comp hx.fst) (h2.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedSplitFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalNode.machine (n x.1) (2*n x.1)).lastSplitNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalNode.machine (n a) (2*n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedSplitFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (PhysicalNodeEmission.lastSplit (hn.comp hx.fst) (h2.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalNode.machine (n x) (2*n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedSplitFilter (hn0 x) (t x) (v.comp ((PhysicalNode.machine (n x) (2*n x)).lastSplitNet j)))
    (fun x j=>SplitMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalNode.machine (n x) (2*n x)).width (s x)) (fun x j hj=>by
      rw [SplitMachine.width_eq,SplitMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr hW.unaryPoly hep hec
  exact h.congr (fun x=>nodePrefix_eq (hn0 x) (s x) (raw x))
lemma retainedNodeFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) (NodeKernel.width (n x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (raw x)):=
  nodePrefixFilter hn ht ((const _ _ 2).unaryMul hn) hn0 hr
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTreeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n t s : α→ℕ}
lemma treePrefix_eq {n t : ℕ} (hn : 0<n) (s : ℕ) (v : BooleanNetwork ((PhysicalTree.machine n).width t) ((PhysicalTree.machine n).width s)) :
    filterPrefix (fun s=>(PhysicalTree.machine n).previousNet s)
      (fun s v=>(PhysicalTree.machine n).retainedNodeFilter hn t (v.comp ((PhysicalTree.machine n).lastNodeNet s))) s v=
      (PhysicalTree.machine n).treePrefixFilter hn t s v:=by
  induction s with
  | zero=>rfl
  | succ s ih=>dsimp only [filterPrefix,NodeMachine.treePrefixFilter];rw [ih]
lemma treePrefixFilter {raw : ∀x,BooleanNetwork ((PhysicalTree.machine (n x)).width (t x)) ((PhysicalTree.machine (n x)).width (s x))}
    (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hs : Emits ea unaryCode s) (hn0 : ∀x,0<n x) (hr : NetEmits ea raw) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).treePrefixFilter (hn0 x) (t x) (s x) (raw x)):=by
  have hep : NetEmits (prodCode ea unaryCode) (fun x=>(PhysicalTree.machine (n x.1)).previousNet x.2):=by
    have hx:=BitStackProgram.Emits.id (prodCode ea unaryCode)
    exact previous (hn.comp hx.fst) hx.snd
  have hec : NetEmits (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2)))
      (fun x=>(PhysicalTree.machine (n x.1)).retainedNodeFilter (hn0 x.1) (t x.1)
        (x.2.2.comp ((PhysicalTree.machine (n x.1)).lastNodeNet x.2.1))):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Σj,BooleanNetwork ((PhysicalTree.machine (n a)).width (t a)) ((PhysicalTree.machine (n a)).width (j+1))=>(x.1,(x.2.1,erasePack x.2.2)))
    exact retainedNodeFilter (hn.comp hx.fst) (ht.comp hx.fst) (fun x=>hn0 x.1)
      ((ofCanonical hx.snd.snd).comp (lastNode (hn.comp hx.fst) hx.snd.fst))
  have h:=filterPrefixEmits (fun x j=>(PhysicalTree.machine (n x)).previousNet j)
    (fun x j v=>(PhysicalTree.machine (n x)).retainedNodeFilter (hn0 x) (t x) (v.comp ((PhysicalTree.machine (n x)).lastNodeNet j)))
    (fun x j=>NodeMachine.previousNet_count _ j)
    (W:=fun x=>(PhysicalTree.machine (n x)).width (s x)) (fun x j hj=>by
      rw [NodeMachine.width_eq,NodeMachine.width_eq];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
    raw hs (machineWidth hn ht) hr (machineWidth hn hs).unaryPoly hep hec
  exact h.congr (fun x=>treePrefix_eq (hn0 x) (s x) (raw x))
lemma accepted (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>(PhysicalTree.machine (n x)).acceptedNet (hn0 x) (t x)):=
  (verified hn ht).band (treePrefixFilter hn ht ht hn0 (identity (machineWidth hn ht)))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FinalUniformity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma paddedFlag_oai (hn : Emits ea unaryCode n) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>PhysicalTree.paddedFlag (n x) (hn0 x)):=
  ((paddedHistory hn).comp (accepted hn (steps hn) hn0)).band ((paddedPad hn).comp (padFlag hn))
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

theorem solution : type_of% @OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag_oai := @OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag_oai

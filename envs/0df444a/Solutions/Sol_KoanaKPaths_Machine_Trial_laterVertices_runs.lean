-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.laterVertices_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:25.798508+00:00
-- url     : https://prove2.me/submissions/2209a7ea-2a27-4027-bab5-d674c9622d8e

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Native_invariant_loop
import Theorems.Thm_KoanaKPaths_Machine_Trial_laterVertex_runs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





end KoanaKPaths.Machine.Native

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup







attribute [local simp] DB Out Cache Count Back Tmp






































lemma frames_append (as bs : List (List ℤ)) : frames (as++bs)=frames as++frames bs := by
  simp [frames,List.flatMap_append]





end KoanaKPaths.Machine.ArrayLookup

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Machine





lemma frameRows_succ {n : ℕ} (F : Fin n→List (List ℤ)) (i : ℕ) (hi : i< n) :
    ArrayLookup.frames (((List.ofFn F).take (i+1)).flatten.reverse)=
      ArrayLookup.frames (F ⟨i,hi⟩).reverse ++
        ArrayLookup.frames (((List.ofFn F).take i).flatten.reverse) := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using hi)]
  simp only [List.flatten_append,List.flatten_singleton,List.reverse_append,ArrayLookup.frames_append,List.getElem_ofFn]

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main






lemma Core.upd {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∉coreRegisters) (xs : List Item) : Core (s.upd j xs) ω arcs p := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] PredecessorCounter PreviousCounter LayerIndex VerticesCounter VerticesTemplate Vertex GraphArray.Current StateIndex LabelCounter LabelTmp
  Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back
  SignLookup.Tmp BitCounter.Count BitCounter.Tmp



lemma laterVertices_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (layer : Fin (k-1))
    (vt it : List Item) (hCore : Core s ω arcs (layer.val+1))
    (hv : s.G Vertex=.int 0::vt) (hCount : s.G VerticesCounter=List.replicate n .mark)
    (hI : s.G LayerIndex=.int (layer.val : ℤ)::it)
    (hCounter : s.G LabelCounter=[]) (hPC : s.G PredecessorCounter=[]) (hBC : s.G PreviousCounter=[]) :
    IRuns I Wedge.prog laterVertices s
      (firstVerticesState s (fun v a => denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (layer.val+2) v a) n vt)
      ((laterVertexCost n k arcs.length+31)*n+30) := by
  let F : Fin n→Fin k→List ℤ := fun v a => denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (layer.val+2) v a
  let Inv : ℕ→IState NS→Prop := fun i st => st=firstVerticesState s F i vt
  have hcounter : ∀ i≤ n, ∀ st, Inv i st → st.G VerticesCounter=List.replicate (n-i) .mark ++ [] := by
    intro i hi st hInv
    rw [hInv]
    simp [firstVerticesState]
  have hstep : ∀ i< n, ∀ st, Inv i st → ∃ st',
      IRuns I Wedge.prog (.seq (.op (.unmark VerticesCounter)) laterVertex) st st'
        (laterVertexCost n k arcs.length+1) ∧ Inv (i+1) st' := by
    intro i hi st hInv
    rw [hInv]
    let cur := firstVerticesState s F i vt
    let popped := cur.upd VerticesCounter (List.replicate (n-(i+1)) .mark)
    let vi : Fin n := ⟨i,hi⟩
    let next := (popped.upd Vertex (.int ((i+1 : ℕ) : ℤ)::vt)).upd GraphArray.Current
      (ArrayLookup.frames (List.ofFn (F vi)).reverse ++ popped.G GraphArray.Current)
    have hlen : n-i=(n-(i+1))+1 := by omega
    have h0 : IExec I Wedge.prog (.op (.unmark VerticesCounter)) cur popped 1 :=
      .op (.unmark (by simp [cur,firstVerticesState,hlen,List.replicate_succ]))
    have h1 : IRuns I Wedge.prog laterVertex popped next (laterVertexCost n k arcs.length) := by
      have hc : Core popped ω arcs (layer.val+1) :=
        (((hCore.upd VerticesCounter (by decide) _).upd Vertex (by decide) _).upd GraphArray.Current (by decide) _).upd VerticesCounter (by decide) _
      exact laterVertex_runs I popped ω arcs layer vi vt it hc
        (by simp [popped,cur,firstVerticesState,vi]) (by simp [popped,cur,firstVerticesState,hI])
        (by simp [popped,cur,firstVerticesState,hCounter])
        (by simp [popped,cur,firstVerticesState,hPC]) (by simp [popped,cur,firstVerticesState,hBC])
    have hpost : next=firstVerticesState s F (i+1) vt := by
      apply itemState_ext
      · intro r
        by_cases hC : r=VerticesCounter
        · subst r; simp [next,popped,cur,firstVerticesState]
        by_cases hV : r=Vertex
        · subst r; simp [next,popped,cur,firstVerticesState]
        by_cases hO : r=GraphArray.Current
        · subst r
          simp [next,popped,cur,firstVerticesState,frameRows_succ (fun v => List.ofFn (F v)) i hi,List.append_assoc,vi]
        simp [next,popped,cur,firstVerticesState,IState.upd,Function.update_apply,hC,hV,hO]
      · rfl
      · rfl
    refine ⟨next,?_,hpost⟩
    exact Native.mono (Native.seq (Native.of_exec h0) h1) (by omega)
  have hinit : Inv 0 s := by
    unfold Inv firstVerticesState
    simp only [Nat.sub_zero,Nat.cast_zero,List.take_zero,List.flatten_nil,List.reverse_nil,
      ArrayLookup.frames,List.flatMap_nil,List.nil_append]
    rw [← hCount,← hv]
    simp
  obtain ⟨st',hrun,hend⟩ := Native.invariant_loop I Wedge.prog VerticesCounter
    (.seq (.op (.unmark VerticesCounter)) laterVertex) Inv n (laterVertexCost n k arcs.length+1) [] (by simp [cls])
    hcounter hstep s hinit
  rw [hend] at hrun
  simpa only [laterVertices,F,Nat.add_assoc,show (1+30 : ℕ)=31 from rfl] using hrun

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (layer :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (vt it : List.{0} NLogN.Item)
  (hCore :
    @KoanaKPaths.Machine.Trial.Core n k s ω arcs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Fin.val
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          layer)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) vt))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.VerticesCounter)
      (@List.replicate.{0} NLogN.Item n NLogN.Item.mark))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              layer)))
        it))
  (hCounter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.nil.{0} NLogN.Item))
  (hPC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PredecessorCounter)
      (@List.nil.{0} NLogN.Item))
  (hBC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.laterVertices s
    (@KoanaKPaths.Machine.Trial.firstVerticesState n k s
      (fun (v : Fin n) (a : Fin k) =>
        @KoanaKPaths.Main.denseLayer n k k arcs
          (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
              (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
              (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
              (KoanaKPaths.Main.trialEquiv n k) ω))
          (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
              (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
              (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
              (KoanaKPaths.Main.trialEquiv n k) ω))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              layer)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          v a)
      n vt)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (KoanaKPaths.Machine.Trial.laterVertexCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs))
          (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        n)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.laterVertices_runs

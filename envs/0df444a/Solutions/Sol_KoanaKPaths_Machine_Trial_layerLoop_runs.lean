-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.layerLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.13042+00:00
-- url     : https://prove2.me/submissions/a729f9a9-9437-41ab-9635-7de822ff74f5

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
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_laterLayer_runs
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

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

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

namespace KoanaKPaths.Machine
open NLogN
variable {S P : ℕ}



lemma liftClosed_exec (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IExec I Fin.elim0 p s s' c) : IExec I prog (liftClosed p) s s' c := by
  induction h with
  | skip s => exact .skip s
  | op h => exact .op h
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT h _ ih => exact .iteT h ih
  | iteF h _ ih => exact .iteF h ih
  | loopT h _ _ ih1 ih2 => exact .loopT h ih1 ih2
  | loopF h => exact .loopF h
  | call => exact Fin.elim0 ‹Fin 0›

lemma liftClosed_runs (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IRuns I Fin.elim0 p s s' c) : IRuns I prog (liftClosed p) s s' c := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht,liftClosed_exec I prog h⟩

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]





































end KoanaKPaths.Machine.Wedge

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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls







lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self








end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main



lemma wordWidth_pos (n k : ℕ) : 1≤ wordWidth n k := by
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





lemma row_word_width (n k r : ℕ) (hr : r≤ k) : zsz (r : ℤ)≤ wordWidth n k := by
  have hz := Controls.zsz_nat_le r
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





end KoanaKPaths.Machine.Trial

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

lemma Core.at {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∈coreRegisters) : s.G j=coreStack ω arcs p j := h j hj

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

lemma coreStack_layer {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (p q : ℕ) (j : Fin NS) (hj : j≠14) : coreStack ω arcs p j=coreStack ω arcs q j := by
  fin_cases j <;> norm_num [coreStack,NS,Wedge.NS] at *
  exact (hj rfl).elim

lemma Core.layer {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (q : ℕ) :
    Core (s.upd 14 (ArrayLookup.frames (matrixArrays
      (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 q)))) ω arcs q := by
  intro j hj
  by_cases he : j=14
  · subst j
    simp [IState.upd,coreStack,NS,Wedge.NS]
  · simpa [IState.upd,he,coreStack_layer ω arcs p q j he] using h j hj

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

attribute [local simp] LayersCounter LayerIndex VerticesCounter LabelCounter PredecessorCounter PreviousCounter Matrix.Prev ArrayLookup.DB





lemma layerLoop_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (it : List Item)
    (hk : 1≤ k) (hCore : Core s ω arcs 1)
    (hI : s.G LayerIndex=.int 0::it) (hCount : s.G LayersCounter=List.replicate (k-1) .mark)
    (hOuter : s.G VerticesCounter=[]) (hCounter : s.G LabelCounter=[])
    (hPC : s.G PredecessorCounter=[]) (hBC : s.G PreviousCounter=[]) :
    IRuns I Wedge.prog layerLoop s
      (layerLoopState s ω arcs (k-1) it)
      ((laterLayerCost n k arcs.length+13000*(wordWidth n k+1)^2+31)*(k-1)+30) := by
  let C := laterLayerCost n k arcs.length+13000*(wordWidth n k+1)^2
  let Inv : ℕ→IState NS→Prop := fun i st => st=layerLoopState s ω arcs i it
  have hcounter : ∀ i≤ k-1, ∀ st, Inv i st → st.G LayersCounter=List.replicate (k-1-i) .mark ++ [] := by
    intro i hi st hs; rw [hs]; simp [layerLoopState]
  have hstep : ∀ i< k-1, ∀ st, Inv i st → ∃ st',
      IRuns I Wedge.prog (.seq (.op (.unmark LayersCounter)) (.seq laterLayer (liftClosed (Square.increment LayerIndex))))
        st st' (C+1) ∧ Inv (i+1) st' := by
    intro i hi st hs; rw [hs]
    let cur := layerLoopState s ω arcs i it
    let popped := cur.upd LayersCounter (List.replicate (k-1-(i+1)) .mark)
    let ii : Fin (k-1) := ⟨i,hi⟩
    let next := popped.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
      (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 (i+2))))
    let final := next.upd LayerIndex (.int ((i+1 : ℕ) : ℤ)::it)
    have hlen : k-1-i=(k-1-(i+1))+1 := by omega
    have h0 : IExec I Wedge.prog (.op (.unmark LayersCounter)) cur popped 1 :=
      .op (.unmark (by simp [cur,layerLoopState,hlen,List.replicate_succ]))
    have hCP : Core popped ω arcs (i+1) :=
      (((hCore.upd LayersCounter (by decide) _).upd LayerIndex (by decide) _).layer (i+1)).upd LayersCounter (by decide) _
    have h1 : IRuns I Wedge.prog laterLayer popped next (laterLayerCost n k arcs.length) :=
      laterLayer_runs I popped ω arcs ii it hCP
        (by simp [popped,cur,layerLoopState,ii]) (by simp [popped,cur,layerLoopState,hOuter])
        (by simp [popped,cur,layerLoopState,hCounter]) (by simp [popped,cur,layerLoopState,hPC])
        (by simp [popped,cur,layerLoopState,hBC])
    have h2 : IRuns I Wedge.prog (liftClosed (Square.increment LayerIndex)) next final
        (13000*(wordWidth n k+1)^2) :=
      liftClosed_runs I Wedge.prog (Square.increment_runs I LayerIndex (by decide) next i (wordWidth n k) it
        (by simp [next,popped,cur,layerLoopState]) (wordWidth_pos n k) (row_word_width n k i (by omega)))
    have hpost : final=layerLoopState s ω arcs (i+1) it := by
      apply itemState_ext
      · intro r
        by_cases hC : r=LayersCounter
        · subst r; simp [final,next,popped,cur,layerLoopState]
        by_cases hI : r=LayerIndex
        · subst r; simp [final,next,popped,cur,layerLoopState]
        by_cases hP : r=Matrix.Prev
        · subst r; simp [final,next,popped,cur,layerLoopState,Nat.add_assoc]
        simp [final,next,popped,cur,layerLoopState,IState.upd,Function.update_apply,hC,hI,hP]
      · rfl
      · rfl
    exact ⟨final,Native.mono (Native.seq (Native.of_exec h0) (Native.seq h1 h2)) (by omega),hpost⟩
  have hinit : Inv 0 s := by
    unfold Inv layerLoopState
    simp only [Nat.sub_zero,Nat.cast_zero,Nat.zero_add]
    have hp : s.G Matrix.Prev=ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1)) := by
      simpa [coreStack,NS,Wedge.NS] using hCore.at 14 (by decide)
    rw [←hCount,←hI,←hp]
    simp
  obtain ⟨st,hrun,hend⟩ := Native.invariant_loop I Wedge.prog LayersCounter
    (.seq (.op (.unmark LayersCounter)) (.seq laterLayer (liftClosed (Square.increment LayerIndex))))
    Inv (k-1) (C+1) [] (by simp [cls]) hcounter hstep s hinit
  rw [hend] at hrun
  simpa only [layerLoop,C,Nat.add_assoc,show (1+30 : ℕ)=31 from rfl] using hrun

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (it : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) it))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayersCounter)
      (@List.replicate.{0} NLogN.Item
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        NLogN.Item.mark))
  (hOuter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.VerticesCounter)
      (@List.nil.{0} NLogN.Item))
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
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.layerLoop s
    (@KoanaKPaths.Machine.Trial.layerLoopState n k s ω arcs
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      it)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (KoanaKPaths.Machine.Trial.laterLayerCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 13000) (instOfNatNat (nat_lit 13000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (KoanaKPaths.Machine.Trial.wordWidth n k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.layerLoop_runs

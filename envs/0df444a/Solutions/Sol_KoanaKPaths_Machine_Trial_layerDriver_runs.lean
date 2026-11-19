-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.layerDriver_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:20.12038+00:00
-- url     : https://prove2.me/submissions/b32379f6-06a6-4bef-bd6f-3fda59a84379

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_layerLoop_runs
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















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
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}











lemma Expr.root_width (e : Expr v) (values : Fin v→ℕ) :
    zsz (e.eval values : ℤ)≤ e.width values := by
  cases e <;> exact le_max_left _ _



end KoanaKPaths.Machine.Arithmetic

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Square.Eval Square.Value BitCounter.Source BitCounter.Count BitCounter.Tmp



lemma storeExpr_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (dst : Fin Square.NS) (hd : dst≠Eval) (s : IState Square.NS)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (storeExpr reg e dst) s
      (s.upd dst (.int (e.eval values : ℤ)::s.G dst)) (11000*(e.size+1)*(w+1)^2) := by
  let s1 := s.upd Eval (.int (e.eval values : ℤ)::s.G Eval)
  let s2 := (s1.upd Eval (s.G Eval)).upd dst (.int (e.eval values : ℤ)::s.G dst)
  have h1 := e.compile_runs I reg hreg values w hw s hv
  have h2 : IExec I Fin.elim0 (.op (.mv Eval dst)) s1 s2 (2*moveCost (zsz (e.eval values : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt Square.NS 0))
      (IOp.Step.mv (s := s1) (i := Eval) (j := dst) (a := (e.eval values : ℤ)) (L := s.G Eval)
        (Ne.symm hd) (by simp [s1]))
    simpa [s2,s1,hd] using h
  have he : s2=s.upd dst (.int (e.eval values : ℤ)::s.G dst) := by simp [s2,s1]
  have h := Native.seq h1 (Native.of_exec h2)
  rw [he] at h
  change IRuns I Fin.elim0 (storeExpr reg e dst) s _ _ at h
  apply Native.mono h
  have hx := (e.root_width values).trans hw
  unfold moveCost
  nlinarith [Nat.zero_le (e.size*w*w)]



lemma countExpr_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (dst : Fin Square.NS) (hdc : dst≠BitCounter.Count) (hds : dst≠BitCounter.Source)
    (s : IState Square.NS) (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (countExpr reg e dst) s
      (s.upd dst (List.replicate (e.eval values) .mark ++ s.G dst))
      (11000*(e.size+1)*(w+1)^2+1100*(e.eval values+1)) := by
  let n := e.eval values
  let s1 := s.upd BitCounter.Source (.int (n : ℤ)::s.G BitCounter.Source)
  let s2 := (s1.upd BitCounter.Source (s.G BitCounter.Source)).upd BitCounter.Count (List.replicate n .mark)
  let s3 := (s2.upd BitCounter.Count []).upd dst (List.replicate n .mark ++ s.G dst)
  have h1 : IRuns I Fin.elim0 (storeExpr reg e BitCounter.Source) s s1
      (11000*(e.size+1)*(w+1)^2) :=
    storeExpr_runs I reg hreg values e w hw BitCounter.Source (by decide) s hv
  have h2 : IRuns I Fin.elim0 BitCounter.toMarks s1 s2 (1000*(n+1)) := by
    simpa [s2,s1,hc] using BitCounter.toMarks_runs I s1 n (s.G BitCounter.Source)
      (by simp [s1]) (by simp [s1,hc,cls]) (by simp [s1,ht])
  have h3 : IExec I Fin.elim0 (moveMarks BitCounter.Count dst) s2 s3 (32*n+30) := by
    have h := moveMarks_exec I BitCounter.Count dst (Ne.symm hdc) s2 n [] (by simp [cls]) (by simp [s2])
    simpa [s3,s2,s1,hdc,hds] using h
  have he : s3=s.upd dst (List.replicate (e.eval values) .mark ++ s.G dst) := by
    apply itemState_ext
    · intro i
      by_cases hi : i=dst
      · subst i; simp [s3,s2,s1,n]
      by_cases hC : i=BitCounter.Count
      · subst i; simp [s3,s2,s1,hc,Ne.symm hdc]
      by_cases hS : i=BitCounter.Source
      · subst i; simp [s3,s2,s1,Ne.symm hds]
      simp [s3,s2,s1,IState.upd,Function.update_apply,hi,hC,hS]
    · rfl
    · rfl
  have h := Native.seq h1 (Native.seq h2 (Native.of_exec h3))
  rw [he] at h
  change IRuns I Fin.elim0 (countExpr reg e dst) s _ _ at h
  apply Native.mono h
  omega

end KoanaKPaths.Machine.Arithmetic

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
open Arithmetic KoanaKPaths.Main
attribute [local simp] LayersCounter LayerIndex VerticesCounter LabelCounter PredecessorCounter PreviousCounter Matrix.Prev ArrayLookup.DB BitCounter.Count BitCounter.Tmp





lemma layerDriver_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (kmTail : List Item)
    (hk : 1≤ k) (hCore : Core s ω arcs 1)
    (hKM : s.G 66=.int ((k-1 : ℕ) : ℤ)::kmTail) (hCount : s.G LayersCounter=[])
    (hOuter : s.G VerticesCounter=[]) (hCounter : s.G LabelCounter=[])
    (hPC : s.G PredecessorCounter=[]) (hBC : s.G PreviousCounter=[]) :
    IRuns I Wedge.prog layerDriver s
      (s.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k))))
      (layerDriverCost n k arcs.length) := by
  let s0 := s.upd LayerIndex (.int 0::s.G LayerIndex)
  let s1 := s0.upd LayersCounter (List.replicate (k-1) .mark)
  let s2 := layerLoopState s1 ω arcs (k-1) (s.G LayerIndex)
  let s3 := s2.upd LayerIndex (s.G LayerIndex)
  have h0 : IExec I Wedge.prog (.op (.const LayerIndex 0)) s s0 2 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.const (s := s) (i := LayerIndex) 0))
  have h1 : IRuns I Wedge.prog (liftClosed (countExpr (fun _ : Fin 1 => 66) (.input 0) LayersCounter)) s0 s1
      (22000*(wordWidth n k+1)^2+1100*((k-1)+1)) := by
    have h := liftClosed_runs I Wedge.prog (countExpr_runs I (fun _ : Fin 1 => 66) (by intro j; decide)
      (fun _ => k-1) (.input 0) (wordWidth n k) (by simpa [Expr.width,Expr.eval] using row_word_width n k (k-1) (by omega)) LayersCounter
      (by decide) (by decide) s0
      (by simpa [s0,coreStack,NS,Wedge.NS] using hCore.at 40 (by decide))
      (by simpa [s0,coreStack,NS,Wedge.NS] using hCore.at 41 (by decide))
      (by intro j; exact ⟨kmTail,by simpa [s0] using hKM⟩))
    simpa [s1,s0,hCount,Expr.size,Expr.eval] using h
  have hc : Core s1 ω arcs 1 := (hCore.upd LayerIndex (by decide) _).upd LayersCounter (by decide) _
  have h2 : IRuns I Wedge.prog layerLoop s1 s2
      ((laterLayerCost n k arcs.length+13000*(wordWidth n k+1)^2+31)*(k-1)+30) :=
    layerLoop_runs I s1 ω arcs (s.G LayerIndex) hk hc (by simp [s1,s0]) (by simp [s1])
      (by simp [s1,s0,hOuter]) (by simp [s1,s0,hCounter]) (by simp [s1,s0,hPC]) (by simp [s1,s0,hBC])
  have h3 : IExec I Wedge.prog (.op (.drop LayerIndex)) s2 s3 (2*zsz ((k-1 : ℕ) : ℤ)+2) :=
    .op (.drop (by simp [s2,layerLoopState]))
  have hpost : s3=s.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k))) := by
    have hkm : k-1+1=k := by omega
    apply itemState_ext
    · intro r
      by_cases hC : r=LayersCounter
      · subst r; simp [s3,s2,layerLoopState,s1,s0,IState.upd,hCount]
      by_cases hI : r=LayerIndex
      · subst r; simp [s3,s2,layerLoopState,s1,s0,IState.upd]
      by_cases hP : r=Matrix.Prev
      · subst r; simp [s3,s2,layerLoopState,s1,s0,IState.upd,hkm]
      simp [s3,s2,layerLoopState,s1,s0,IState.upd,Function.update_apply,hC,hI,hP]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq h1 (Native.seq h2 (Native.of_exec h3)))
  rw [hpost] at h
  change IRuns I Wedge.prog layerDriver s _ _ at h
  apply Native.mono h
  have hkw := row_word_width n k (k-1) (by omega)
  have hkm : k-1+1=k := by omega
  unfold layerDriverCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (kmTail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hKM :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 66)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 66))))
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        kmTail))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayersCounter)
      (@List.nil.{0} NLogN.Item))
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
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.layerDriver s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.Prev
      (KoanaKPaths.Machine.ArrayLookup.frames
        (@KoanaKPaths.Main.matrixArrays n k
          (@KoanaKPaths.Main.denseLayer n k k arcs
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
            k))))
    (KoanaKPaths.Machine.Trial.layerDriverCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)) := by
  exact @KoanaKPaths.Machine.Trial.layerDriver_runs

-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.positiveRaw_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.091659+00:00
-- url     : https://prove2.me/submissions/87d297e9-6153-4bb2-a0cf-2d738b0d8104

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_Square_predCopy_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_nativeEstimator_runs
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_transferBits_exec
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

lemma skip (s : IState S) : IRuns I iprog .skip s s 1 := of_exec (.skip s)
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











@[simp] lemma set_stk_self (σ : St S) (i : Fin S) (l : List Sym) : (σ.set i l).stk i = l := by
  simp [St.set]
@[simp] lemma set_stk_ne (σ : St S) {i j : Fin S} (h : j ≠ i) (l : List Sym) :
    (σ.set i l).stk j = σ.stk j := by simp [St.set,h]





@[simp] lemma set_same (σ : St S) (i : Fin S) : σ.set i (σ.stk i) = σ := by
  apply St.ext
  · funext j
    simp [St.set]
  · rfl
  · rfl






@[simp] lemma setIp_same (σ : St S) : σ.setIp σ.ip = σ := rfl









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



lemma readCountedMarks_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (cnt dst : Fin S) (hne : cnt ≠ dst) (σ : St S)
    (W : List Bool) (tail : List Sym) (ht : tail.head? ≠ some hdMark)
    (hs : σ.stk cnt = List.replicate W.length hdMark ++ tail)
    (hinput : ∀ j (hj : j < W.length), I.getD (σ.ip+j) codeEnd = codeBit W[j]) :
    Exec I prog (readCountedMarks cnt dst) σ
      (((σ.set cnt tail).set dst (W.reverse.map codeBit ++ σ.stk dst)).setIp (σ.ip+W.length))
      (3*W.length+1) := by
  induction W generalizing σ with
  | nil =>
    have hh : (decide (σ.top cnt=some hdMark)) = false := by simp [St.top,hs,ht]
    have hcnt : σ.set cnt tail = σ := by rw [← show σ.stk cnt = tail from by simpa using hs]; exact set_same _ _
    unfold readCountedMarks
    simp only [List.length_nil,List.replicate_zero,List.nil_append,List.reverse_nil,List.map_nil,
      hcnt,set_same,Nat.add_zero,mul_zero,zero_add,setIp_same]
    exact Exec.loopF hh
  | cons b W ih =>
    let σ1 := (σ.pop cnt).inRd I dst
    have hbit : I.getD σ.ip codeEnd = codeBit b := by
      have hh := hinput 0 (by simp)
      change I.getD (σ.ip+0) codeEnd = codeBit b at hh
      simpa only [Nat.add_zero] using hh
    have hcnt : σ1.stk cnt = List.replicate W.length hdMark ++ tail := by
      simp [σ1,St.inRd,St.pop,hs,hne]
    have hi : ∀ j (hj : j < W.length), I.getD (σ1.ip+j) codeEnd = codeBit W[j] := by
      intro j hj
      have hh := hinput (j+1) (by simpa using Nat.succ_lt_succ hj)
      simpa [σ1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hbody : Exec I prog (.seq (.pop cnt) (.inRd dst)) σ σ1 2 :=
      Exec.seq (Exec.pop _ _) (Exec.inRd _ _)
    have htop : (decide (σ.top cnt=some hdMark)) = true := by simp [St.top,hs,List.replicate_succ]
    have hrun := Exec.loopT htop hbody (ih σ1 hcnt hi)
    have hfinal :
        (((σ1.set cnt tail).set dst (W.reverse.map codeBit ++ σ1.stk dst)).setIp (σ1.ip+W.length)) =
        (((σ.set cnt tail).set dst ((b::W).reverse.map codeBit ++ σ.stk dst)).setIp (σ.ip+(b::W).length)) := by
      apply St.ext
      · funext t
        by_cases hc : t=cnt <;> by_cases hd : t=dst <;>
          simp_all [σ1,St.setIp,St.set,St.inRd,St.pop,List.reverse_cons,List.map_append,List.append_assoc]
      · simp [σ1,St.setIp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · rfl
    rw [hfinal] at hrun
    convert hrun using 1 <;> simp [readCountedMarks] <;> omega




lemma signWord_enc (b : Bool) : signWord b = Item.enc (.int (KoanaKPaths.Main.sgn b)) := by
  cases b <;> simp [signWord,KoanaKPaths.Main.sgn,Item.enc,hdOf,zbits,nbits_eq_bits,codeBit]



lemma pushSigns_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src dst : Fin S) (hne : src ≠ dst) (σ : St S)
    (W : List Bool) (tail : List Sym) (ht : bitOf tail.head? = none)
    (hs : σ.stk src = W.map codeBit ++ tail) :
    Exec I prog (pushSigns src dst) σ
      ((σ.set src tail).set dst (W.reverse.flatMap signWord ++ σ.stk dst)) (5*W.length+1) := by
  induction W generalizing σ with
  | nil =>
    have hh : isBitT (σ.top src) = false := by simp [St.top,hs,isBitT,ht]
    have hsrc : σ.set src tail = σ := by rw [← show σ.stk src=tail from by simpa using hs]; exact set_same _ _
    unfold pushSigns
    simp only [List.reverse_nil,List.flatMap_nil,List.nil_append,List.length_nil,mul_zero,zero_add,hsrc,set_same]
    exact Exec.loopF hh
  | cons b W ih =>
    let σ1 := ((σ.pop src).push dst 1).push dst (if b then hdPos else hdNeg)
    have hbody : Exec I prog
        (.ite src (fun o => decide (o=some 1))
          (.seq (.pop src) (.seq (.push dst 1) (.push dst hdPos)))
          (.seq (.pop src) (.seq (.push dst 1) (.push dst hdNeg)))) σ σ1 4 := by
      cases b
      · exact Exec.iteF (by simp [St.top,hs,codeBit])
          (Exec.seq (Exec.pop _ _) (Exec.seq (Exec.push _ _ _) (Exec.push _ _ _)))
      · exact Exec.iteT (by simp [St.top,hs,codeBit])
          (Exec.seq (Exec.pop _ _) (Exec.seq (Exec.push _ _ _) (Exec.push _ _ _)))
    have hsrc1 : σ1.stk src = W.map codeBit ++ tail := by simp [σ1,St.push,St.pop,hs,hne]
    have hloop : isBitT (σ.top src) = true := by cases b <;> simp [St.top,hs,isBitT,codeBit,bitOf]
    have hrun := Exec.loopT hloop hbody (ih σ1 hsrc1)
    have hfinal : ((σ1.set src tail).set dst (W.reverse.flatMap signWord ++ σ1.stk dst)) =
        ((σ.set src tail).set dst ((b::W).reverse.flatMap signWord ++ σ.stk dst)) := by
      apply St.ext
      · funext t
        by_cases hs : t=src <;> by_cases hd : t=dst <;>
          simp_all [σ1,St.set,St.push,St.pop,List.reverse_cons,List.flatMap_append,signWord,List.append_assoc]
      · rfl
      · rfl
    rw [hfinal] at hrun
    convert hrun using 1 <;> simp [pushSigns] <;> omega

@[simp] lemma enc_work_stk (s : IState S) (i : Fin S) : (encI s).stk (ι i) = encL (s.G i) := by
  simp [encI,ι,i.isLt]
@[simp] lemma enc_sq_stk (s : IState S) : (encI s).stk (NLogN.sq S) = [] := by simp [encI,NLogN.sq]
@[simp] lemma iota_eq {i j : Fin S} : ι i = ι j ↔ i=j := by
  constructor
  · intro h; exact Fin.ext (congrArg (fun x : Fin (S+4) => x.val) h)
  · exact congrArg ι
@[simp] lemma iota_ne_sq (i : Fin S) : ι i ≠ NLogN.sq S := by
  intro h
  have he := congrArg (fun x : Fin (S+4) => x.val) h
  simp only [ι,Fin.val_castAdd,NLogN.sq] at he
  omega
@[simp] lemma sq_ne_iota (i : Fin S) : NLogN.sq S ≠ ι i := Ne.symm (iota_ne_sq i)

@[simp] lemma encL_append (L M : List Item) : encL (L++M) = encL L++encL M := by
  simp [encL,List.flatMap_append]
@[simp] lemma encL_replicate_mark (m : ℕ) : encL (List.replicate m Item.mark) = List.replicate m hdMark := by
  induction m <;> simp_all [encL,Item.enc,List.replicate_succ]
lemma encL_signs (W : List Bool) :
    encL (W.map (fun b => Item.int (KoanaKPaths.Main.sgn b))) = W.flatMap signWord := by
  simp only [encL,List.flatMap_map]
  apply congrArg (fun f : Bool → List Sym => W.flatMap f)
  funext b
  exact (signWord_enc b).symm



lemma bulkSigns_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P) (counter coins : Fin S) (hne : counter ≠ coins)
    (s : IState S) (W : List Bool) (hc : s.G counter = List.replicate W.length .mark)
    (hi : ∀ j (hj : j < W.length), I.getD (s.ip+j) codeEnd = codeBit W[j]) :
    Exec I prog (bulkSigns counter coins) (encI s)
      (encI { (s.upd counter []).upd coins ((W.map (fun b => Item.int (KoanaKPaths.Main.sgn b)))++s.G coins)
        with ip := s.ip+W.length }) (8*W.length+2) := by
  let σB := ((((encI s).set (ι counter) []).set (NLogN.sq S)
    (W.reverse.map codeBit ++ (encI s).stk (NLogN.sq S))).setIp ((encI s).ip+W.length))
  have hread : Exec I prog (readCountedMarks (ι counter) (NLogN.sq S)) (encI s) σB (3*W.length+1) := by
    apply readCountedMarks_exec I prog _ _ (iota_ne_sq counter) (encI s) W [] (by decide)
    · simp [hc]
    · exact hi
  have hs : σB.stk (NLogN.sq S) = W.reverse.map codeBit ++ [] := by simp [σB]
  let σF := (σB.set (NLogN.sq S) []).set (ι coins) ((W.reverse.reverse).flatMap signWord ++ σB.stk (ι coins))
  have hpush : Exec I prog (pushSigns (NLogN.sq S) (ι coins)) σB σF (5*W.length+1) := by
    simpa only [List.length_reverse] using pushSigns_exec I prog _ _ (sq_ne_iota coins) σB W.reverse [] rfl hs
  have hrun := Exec.seq hread hpush
  have he : σF = encI { (s.upd counter []).upd coins
      ((W.map (fun b => Item.int (KoanaKPaths.Main.sgn b)))++s.G coins) with ip := s.ip+W.length } := by
    apply St.ext
    · funext x
      by_cases hx : x.val < S
      · let j : Fin S := ⟨x.val,hx⟩
        have hj : x=ι j := Fin.ext rfl
        rw [hj]
        by_cases hjc : j=counter <;> by_cases hjn : j=coins <;>
          simp_all [σF,σB,IState.upd,encL_signs,List.reverse_reverse]
      · have hxc : x ≠ ι counter := by intro h; have hv := congrArg (fun x : Fin (S+4) => x.val) h; simp only [ι,Fin.val_castAdd] at hv; omega
        have hxn : x ≠ ι coins := by intro h; have hv := congrArg (fun x : Fin (S+4) => x.val) h; simp only [ι,Fin.val_castAdd] at hv; omega
        by_cases hxs : x=NLogN.sq S
        · subst x
          simp [σF,σB]
        · have henc : (encI s).stk x = [] := by simp [encI,hx]
          simp [σF,σB,hxc,hxn,hxs,encI,hx]
    · rfl
    · rfl
  rw [he] at hrun
  change Exec I prog (bulkSigns counter coins) (encI s) _ ((3*W.length+1)+(5*W.length+1)) at hrun
  have hcost : (3*W.length+1)+(5*W.length+1) = 8*W.length+2 := by omega
  simpa only [hcost] using hrun

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
namespace KoanaKPaths.Machine.Arithmetic
variable {v : ℕ}









lemma countPlans_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Square.Eval)
    (values : Fin v→ℕ) (plans : List (CountPlan v)) (w : ℕ)
    (hw : ∀ p∈plans, p.1.width values≤ w)
    (hsc : ∀ p∈plans, p.2≠BitCounter.Count)
    (hss : ∀ p∈plans, p.2≠BitCounter.Source)
    (hst : ∀ p∈plans, p.2≠BitCounter.Tmp)
    (hinput : ∀ p∈plans, ∀ i, reg i≠p.2)
    (s : IState Square.NS) (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (countPlans reg plans) s (applyCounts values s plans) (countPlansCost values w plans) := by
  induction plans generalizing s with
  | nil => exact Native.skip s
  | cons p plans ih =>
    rcases p with ⟨e,d⟩
    let s1 := s.upd d (List.replicate (e.eval values) .mark ++ s.G d)
    have h1 := countExpr_runs I reg hreg values e w (hw (e,d) (by simp)) d
      (hsc (e,d) (by simp)) (hss (e,d) (by simp)) s hc ht hv
    have h2 := ih
      (fun p hp => hw p (by simp [hp]))
      (fun p hp => hsc p (by simp [hp]))
      (fun p hp => hss p (by simp [hp]))
      (fun p hp => hst p (by simp [hp]))
      (fun p hp => hinput p (by simp [hp])) s1
      (by simp [s1,Ne.symm (hsc (e,d) (by simp)),hc])
      (by simp [s1,Ne.symm (hst (e,d) (by simp)),ht]) (by
        intro i
        obtain ⟨tail,htail⟩ := hv i
        exact ⟨tail,by simp [s1,hinput (e,d) (by simp) i,htail]⟩)
    exact Native.seq h1 h2



end KoanaKPaths.Machine.Arithmetic

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls




attribute [local simp] PowerCount PowerRuler PowerOut



lemma powerLoop_exec (I : List Sym) (s : IState NS) (L p : ℕ) (ht rt : List Item)
    (hf : s.G PowerCount=List.replicate L .mark) (hh : s.G PowerOut=.int ((4 : ℤ)^p)::ht)
    (hr : s.G PowerRuler=.int 4::rt) :
    IExec I Fin.elim0 powerLoop s
      ((s.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^(p+L))::ht)) ((shlCost 2+31)*L+30) := by
  induction L generalizing s p with
  | zero =>
    have hcl : decide (s.cl PowerCount=Cls.mark)=false := by simp [IState.cl,hf,cls]
    have he : (s.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^(p+0))::ht)=s := by
      have hf' : s.G PowerCount=[] := by simpa using hf
      simp only [Nat.add_zero]
      rw [← hf',← hh]
      simp
    rw [he]
    exact .loopF hcl
  | succ L ih =>
    let s1 := s.upd PowerCount (List.replicate L .mark)
    let s2 := s1.upd PowerOut (.int ((4 : ℤ)^(p+1))::ht)
    have h1 : IExec I Fin.elim0 (.op (.unmark PowerCount)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hf))
    have h2 : IExec I Fin.elim0 (.op (.shl PowerOut PowerRuler)) s1 s2 (shlCost 2) := by
      have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.shl (s := s1) (i := PowerOut) (j := PowerRuler) (a := (4 : ℤ)^p) (m := 2)
          (Li := ht) (Lj := rt) (by decide) (by simp [s1,hh]) (by simpa [s1] using hr))
      simpa [s2,pow_succ] using h
    have htail := ih s2 (p+1) (by simp [s2,s1]) (by simp [s2]) (by simp [s2,s1,hr])
    have hcl : decide (s.cl PowerCount=Cls.mark)=true := by simp [IState.cl,hf,List.replicate_succ,cls]
    have h := IExec.loopT hcl (IExec.seq h1 h2) htail
    have he : (s2.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^(p+1+L))::ht)=
      (s.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^(p+(L+1)))::ht) := by
      apply itemState_ext
      · intro i
        by_cases hF : i=PowerCount
        · subst i; simp [s2,s1]
        by_cases hH : i=PowerOut
        · subst i; simp [s2,s1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        simp [s2,s1,IState.upd,Function.update_apply,hF,hH]
      · rfl
      · rfl
    rw [he] at h
    change IExec I Fin.elim0 powerLoop s _ _ at h
    convert h using 1 <;> ring



lemma powerFour_exec (I : List Sym) (s : IState NS) (a : ℕ)
    (hc : s.G PowerCount=List.replicate a .mark) :
    IExec I Fin.elim0 powerFour s
      ((s.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^a)::s.G PowerOut))
      ((shlCost 2+31)*a+46) := by
  let s0 := s.upd PowerRuler (.int 4::s.G PowerRuler)
  let s1 := s0.upd PowerOut (.int 1::s.G PowerOut)
  let s2 := (s1.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^a)::s.G PowerOut)
  let s3 := s2.upd PowerRuler (s.G PowerRuler)
  have hz4 : zsz (4 : ℤ)=3 := by simpa [Wedge.zsz_eq_size] using (Nat.size_pow (n := 2))
  have h0 : IExec I Fin.elim0 (.op (.const PowerRuler 4)) s s0 5 := by
    simpa only [hz4] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s) (i := PowerRuler) 4))
  have h1 : IExec I Fin.elim0 (.op (.const PowerOut 1)) s0 s1 3 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s0) (i := PowerOut) 1))
  have h2 : IExec I Fin.elim0 powerLoop s1 s2 ((shlCost 2+31)*a+30) := by
    simpa [s2] using powerLoop_exec I s1 a 0 (s.G PowerOut) (s.G PowerRuler)
      (by simp [s1,s0,hc]) (by simp [s1]) (by simp [s1,s0])
  have h3 : IExec I Fin.elim0 (.op (.drop PowerRuler)) s2 s3 8 := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.drop (s := s2) (i := PowerRuler) (a := 4) (L := s.G PowerRuler) (by simp [s2,s1,s0]))
    simpa only [hz4] using h
  have he : s3=(s.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^a)::s.G PowerOut) := by
    apply itemState_ext
    · intro i
      by_cases hC : i=PowerCount
      · subst i; simp [s3,s2,s1,s0]
      by_cases hO : i=PowerOut
      · subst i; simp [s3,s2,s1,s0]
      by_cases hR : i=PowerRuler
      · subst i; simp [s3,s2,s1,s0]
      simp [s3,s2,s1,s0,IState.upd,Function.update_apply,hC,hO,hR]
    · rfl
    · rfl
  have h := IExec.seq h0 (IExec.seq h1 (IExec.seq h2 h3))
  rw [he] at h
  change IExec I Fin.elim0 powerFour s _ _ at h
  convert h using 1 <;> omega

lemma powerFour_cost (a : ℕ) : (shlCost 2+31)*a+46≤500*(a+1) := by
  norm_num [shlCost,moveCost,zipCost]
  omega

end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic























lemma inputRegs_ne_eval (i : Fin 7) : inputRegs i≠Square.Eval := by
  fin_cases i <;> decide

lemma exprM_eval (n k a b m : ℕ) : exprM.eval (inputValues n k a b m)=KoanaKPaths.Main.groupTrials k a := by
  simp [exprM,exprK,exprPower,Expr.eval,inputValues,KoanaKPaths.Main.groupTrials,pow_succ] <;> ring

lemma exprQ_eval (n k a b m : ℕ) : exprQ.eval (inputValues n k a b m)=2*b+1 := rfl
lemma exprTrial_eval (n k a b m : ℕ) : exprTrial.eval (inputValues n k a b m)=KoanaKPaths.Main.trialBits n k := rfl
lemma exprNK_eval (n k a b m : ℕ) : exprNK.eval (inputValues n k a b m)=n*k := rfl
lemma exprWidth_eval (n k a b m : ℕ) : exprWidth.eval (inputValues n k a b m)=KoanaKPaths.Main.medianWidth n k a := by
  simp [exprWidth,exprN,exprK,exprA,Expr.eval,inputValues,KoanaKPaths.Main.medianWidth] <;> ring
lemma exprSample_eval (n k a b m : ℕ) : exprSample.eval (inputValues n k a b m)=KoanaKPaths.Main.sampleBits n k a b := by
  simp only [exprSample,Expr.eval,exprM_eval,exprQ_eval,exprTrial_eval]
  rfl
lemma exprThreshold_eval (n k a b m : ℕ) : exprThreshold.eval (inputValues n k a b m)=b+1 := rfl

lemma plans_safe :
    (∀ p∈plans, p.2≠BitCounter.Count) ∧ (∀ p∈plans, p.2≠BitCounter.Source) ∧
    (∀ p∈plans, p.2≠BitCounter.Tmp) ∧ (∀ p∈plans, ∀ i, inputRegs i≠p.2) := by
  constructor
  · simp [plans,BitCounter.Count]
  constructor
  · simp [plans,BitCounter.Source]
  constructor
  · simp [plans,BitCounter.Tmp]
  · intro p hp i
    simp only [plans,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases i <;> decide

lemma plans_sizes (p : CountPlan 7) (hp : p∈plans) : p.1.size≤ 100 := by
  simp only [plans,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    decide

lemma plans_atoms (n k a b m U : ℕ)
    (hinputs : ∀ i, zsz (inputValues n k a b m i : ℤ)≤ U) (hU : 11≤ U)
    (p : CountPlan 7) (hp : p∈plans) : p.1.atomWidth (inputValues n k a b m)≤ U := by
  have h1024 : Nat.size 1024=11 := by decide
  have h100 : Nat.size 100=7 := by decide
  have h2 : Nat.size 2=2 := by decide
  have hN := hinputs 0
  have hK := hinputs 1
  have hA := hinputs 2
  have hB := hinputs 3
  have hArc := hinputs 4
  have hP := hinputs 5
  have hKm := hinputs 6
  simp only [Wedge.zsz_eq_size] at hN hK hA hB hArc hP hKm
  simp only [plans,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [exprN,exprK,exprA,exprB,exprArcCount,exprPower,exprKMinus,exprM,exprQ,exprTrial,
      exprNK,exprWidth,exprSample,exprThreshold,Expr.atomWidth,max_le_iff,Wedge.zsz_eq_size] <;>
    norm_num at * <;> omega

lemma plans_width (n k a b m U : ℕ)
    (hinputs : ∀ i, zsz (inputValues n k a b m i : ℤ)≤ U) (hU : 11≤ U)
    (p : CountPlan 7) (hp : p∈plans) : p.1.width (inputValues n k a b m)≤100*(U+1) := by
  have h := p.1.width_le (inputValues n k a b m) U (plans_atoms n k a b m U hinputs hU p hp)
  exact h.trans (Nat.mul_le_mul_right _ (plans_sizes p hp))

lemma program_runs (I : List Sym) (s : IState NS) (n k a b m U : ℕ)
    (hv : ∀ i, ∃ tail, s.G (inputRegs i)=.int (inputValues n k a b m i : ℤ)::tail)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hinputs : ∀ i, zsz (inputValues n k a b m i : ℤ)≤ U) (hU : 11≤ U) :
    IRuns I Fin.elim0 program s (applyCounts (inputValues n k a b m) s plans)
      (countPlansCost (inputValues n k a b m) (100*(U+1)) plans) := by
  exact countPlans_runs I inputRegs inputRegs_ne_eval (inputValues n k a b m) plans
    (100*(U+1)) (plans_width n k a b m U hinputs hU) plans_safe.1 plans_safe.2.1
      plans_safe.2.2.1 plans_safe.2.2.2 s hc ht hv

end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls







lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

lemma control_inputs_width (n k a b m : ℕ) (i : Fin 7) :
    zsz (inputValues n k a b m i : ℤ)≤ controlWidth n k a b m := by
  have hn := zsz_nat_le n
  have hk := zsz_nat_le k
  have ha := zsz_nat_le a
  have hm := zsz_nat_le m
  have hkm := zsz_nat_le (k-1)
  have hb : zsz (b : ℤ)=b.size := by simp [Wedge.zsz_eq_size]
  have hp : zsz ((4^a : ℕ) : ℤ)=2*a+1 := by
    rw [Wedge.zsz_eq_size,Int.natAbs_natCast,show (4 : ℕ)=2^2 from rfl,← pow_mul]
    exact Nat.size_pow
  fin_cases i
  · change zsz (n : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz (k : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz (a : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz (b : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz (m : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz ((4^a : ℕ) : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega
  · change zsz ((k-1 : ℕ) : ℤ)≤ controlWidth n k a b m
    unfold controlWidth
    omega


lemma controlWidth_ge (n k a b m : ℕ) : 11≤controlWidth n k a b m := by unfold controlWidth; omega



end KoanaKPaths.Machine.Controls

end

section

open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}

lemma native_closed_runs (I : List Sym) (prog : Fin P→Stmt (S+4) P) (iprog : Fin P→IStmt S P)
    (hprog : ∀ j, prog j=compile (iprog j)) {p : IStmt S 0} {s s' : IState S} {C : ℕ}
    (h : IRuns I Fin.elim0 p s s' C) :
    Runs I prog (compile (liftClosed p)) (encI s) (encI s') C := by
  obtain ⟨t,ht,h⟩ := h
  obtain ⟨u,hu,he⟩ := (NLogN.compile_correct hprog (liftClosed_exec I iprog h)).1
  exact ⟨u,hu.trans ht,he⟩

end KoanaKPaths.Machine

end

section

namespace KoanaKPaths.Machine.Raw
open NLogN
variable {S P : ℕ} {I : List Sym} {prog : Fin P→Stmt S P}
variable {p q : Stmt S P} {s s1 s2 : St S} {c d : ℕ}
lemma of_exec (h : Exec I prog p s s1 c) : Runs I prog p s s1 c := ⟨c,le_rfl,h⟩
lemma mono (h : Runs I prog p s s1 c) (hc : c≤d) : Runs I prog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma seq (h1 : Runs I prog p s s1 c) (h2 : Runs I prog q s1 s2 d) :
    Runs I prog (.seq p q) s s2 (c+d) := by
  obtain ⟨t,ht,h1⟩ := h1
  obtain ⟨u,hu,h2⟩ := h2
  exact ⟨t+u,Nat.add_le_add ht hu,.seq h1 h2⟩
end KoanaKPaths.Machine.Raw

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main









lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic



attribute [local simp] FieldK FieldA KMinus PowerCount PowerOut BitCounter.Count BitCounter.Tmp Square.Eval Square.Value



lemma prepareBinary_runs (I : List Sym) (s : IState NS) (k a : ℕ) (kt atail : List Item)
    (hk : s.G FieldK=.int (k : ℤ)::kt) (ha : s.G FieldA=.int (a : ℤ)::atail)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[]) (hp : s.G PowerCount=[]) :
    IRuns I Fin.elim0 prepareBinary s
      ((s.upd PowerOut (.int ((4^a : ℕ) : ℤ)::s.G PowerOut)).upd KMinus
        (.int ((k-1 : ℕ) : ℤ)::s.G KMinus))
      (22000*(zsz (a : ℤ)+1)^2+1600*(a+1)+12000*(zsz (k : ℤ)+2)^2) := by
  let s0 := s.upd PowerCount (List.replicate a .mark)
  let s1 := (s0.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^a)::s.G PowerOut)
  let s2 := s1.upd KMinus (.int ((k-1 : ℕ) : ℤ)::s.G KMinus)
  have h0 : IRuns I Fin.elim0
      (countExpr (fun _ : Fin 1 => FieldA) (.input 0) PowerCount) s s0
      (22000*(zsz (a : ℤ)+1)^2+1100*(a+1)) := by
    have h := countExpr_runs I (fun _ : Fin 1 => FieldA) (by intro i; decide)
      (fun _ => a) (.input 0) (zsz (a : ℤ)) (by simp [Expr.width,Expr.eval])
      PowerCount (by decide) (by decide) s hc ht (by intro i; exact ⟨atail,ha⟩)
    simpa [s0,hp,Expr.size,Expr.eval] using h
  have h1 : IRuns I Fin.elim0 powerFour s0 s1 (500*(a+1)) := by
    have h := powerFour_exec I s0 a (by simp [s0])
    have he : (s0.upd PowerCount []).upd PowerOut (.int ((4 : ℤ)^a)::s0.G PowerOut)=s1 := by simp [s1,s0]
    rw [he] at h
    exact Native.mono (Native.of_exec h) (powerFour_cost a)
  have h2 : IRuns I Fin.elim0 (Square.predCopy FieldK KMinus) s1 s2 (12000*(zsz (k : ℤ)+2)^2) := by
    have h := Square.predCopy_runs I FieldK KMinus (by decide) (by decide) s1 k (zsz (k : ℤ)+1)
      kt (by simp [s1,s0,hk]) (by omega) (by omega)
    simpa [s2,s1,s0,Nat.add_assoc] using h
  have he : s2=(s.upd PowerOut (.int ((4^a : ℕ) : ℤ)::s.G PowerOut)).upd KMinus
      (.int ((k-1 : ℕ) : ℤ)::s.G KMinus) := by
    apply itemState_ext
    · intro i
      by_cases hP : i=PowerOut
      · subst i; simp [s2,s1,s0]
      by_cases hK : i=KMinus
      · subst i; simp [s2,s1,s0]
      by_cases hC : i=PowerCount
      · subst i; simp [s2,s1,s0,hp]
      simp [s2,s1,s0,IState.upd,Function.update_apply,hP,hK,hC]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq h1 h2)
  rw [he] at h
  change IRuns I Fin.elim0 prepareBinary s _ _ at h
  apply Native.mono h
  omega

end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic
attribute [local simp] FieldK FieldA KMinus PowerOut PowerCount BitCounter.Count BitCounter.Tmp







lemma setup_runs (I : List Sym) (s : IState NS) (n k a b m : ℕ)
    (nt kt atail bt mt : List Item)
    (hn : s.G 53=.int (n : ℤ)::nt) (hk : s.G 54=.int (k : ℤ)::kt)
    (ha : s.G 55=.int (a : ℤ)::atail) (hb : s.G 56=.int (b : ℤ)::bt)
    (hm : s.G 57=.int (m : ℤ)::mt)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[]) (hp : s.G PowerCount=[]) :
    IRuns I Fin.elim0 setup s (setupState s n k a b m) (setupCost n k a b m) := by
  let s0 := (s.upd PowerOut (.int ((4^a : ℕ) : ℤ)::s.G PowerOut)).upd KMinus
    (.int ((k-1 : ℕ) : ℤ)::s.G KMinus)
  have h0 := prepareBinary_runs I s k a kt atail hk ha hc ht hp
  have hv : ∀ i, ∃ tail, s0.G (inputRegs i)=.int (inputValues n k a b m i : ℤ)::tail := by
    intro i
    fin_cases i
    · exact ⟨nt,by simpa [s0,inputRegs,inputValues] using hn⟩
    · exact ⟨kt,by simpa [s0,inputRegs,inputValues] using hk⟩
    · exact ⟨atail,by simpa [s0,inputRegs,inputValues] using ha⟩
    · exact ⟨bt,by simpa [s0,inputRegs,inputValues] using hb⟩
    · exact ⟨mt,by simpa [s0,inputRegs,inputValues] using hm⟩
    · exact ⟨s.G PowerOut,by simp [s0,inputRegs,inputValues]⟩
    · exact ⟨s.G KMinus,by simp [s0,inputRegs,inputValues]⟩
  have h1 := program_runs I s0 n k a b m (controlWidth n k a b m) hv
    (by simp [s0,hc]) (by simp [s0,ht]) (control_inputs_width n k a b m) (controlWidth_ge n k a b m)
  exact Native.seq h0 h1

lemma setupState_samples (s : IState NS) (n k a b m : ℕ) :
    (setupState s n k a b m).G 51=List.replicate (KoanaKPaths.Main.sampleBits n k a b) .mark ++ s.G 51 := by
  simp [setupState,applyCounts,plans,exprSample_eval]



end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Input.VertexField Input.PathField Input.AccuracyField Input.ConfidenceField Input.ArcCountField



lemma prepared_ready (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    EstimatorReady (preparedState n arcs k a b) k a b arcs := by
  constructor
  · intro j hj
    fin_cases j <;> norm_num [readyRegisters,coreRegisters,NS,Wedge.NS,Fin.ext_iff] at hj
    all_goals
      simp [readyStack,preparedState,Controls.setupState,Arithmetic.applyCounts,
        Controls.plans,Controls.exprM_eval,Controls.exprQ_eval,Controls.exprTrial_eval,Controls.exprNK_eval,
        Controls.exprWidth_eval,Controls.exprSample_eval,Controls.exprThreshold_eval,
        Controls.exprK,Controls.exprN,Controls.exprArcCount,Arithmetic.Expr.eval,Controls.inputValues,
        Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,NS,Wedge.NS,
        Controls.PowerOut,Controls.KMinus,Input.DB]
    all_goals first
      | exact Controls.exprTrial_eval n k a b arcs.length
      | exact Controls.exprNK_eval n k a b arcs.length
      | exact Controls.exprM_eval n k a b arcs.length
      | exact Controls.exprQ_eval n k a b arcs.length
      | exact Controls.exprThreshold_eval n k a b arcs.length
      | exact Controls.exprWidth_eval n k a b arcs.length
  · intro j hj
    fin_cases j <;> norm_num [estimatorRegisters,NS,Wedge.NS,Fin.ext_iff] at hj
    all_goals
      simp [estimatorStack,preparedState,Controls.setupState,Arithmetic.applyCounts,
        Controls.plans,Controls.exprM_eval,Controls.exprQ_eval,Controls.exprTrial_eval,Controls.exprNK_eval,
        Controls.exprWidth_eval,Controls.exprSample_eval,Controls.exprThreshold_eval,
        Controls.exprK,Controls.exprN,Controls.exprArcCount,Arithmetic.Expr.eval,Controls.inputValues,
        Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,NS,Wedge.NS,
        Controls.PowerOut,Controls.KMinus,Input.DB]
    all_goals first
      | exact Controls.exprTrial_eval n k a b arcs.length
      | exact Controls.exprNK_eval n k a b arcs.length
      | exact Controls.exprM_eval n k a b arcs.length
      | exact Controls.exprQ_eval n k a b arcs.length
      | exact Controls.exprThreshold_eval n k a b arcs.length
      | exact Controls.exprWidth_eval n k a b arcs.length

lemma prepared_ip (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (preparedState n arcs k a b).ip=(graphInputControls n arcs k a b).length := rfl
lemma prepared_out (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (preparedState n arcs k a b).out=[] := rfl
lemma prepared_coins (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (preparedState n arcs k a b).G Coins=[] := by
  simp [preparedState,Controls.setupState,Arithmetic.applyCounts,Controls.plans,Coins,
    Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,Controls.PowerOut,Controls.KMinus,Input.DB]
lemma prepared_samples (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (preparedState n arcs k a b).G 51=List.replicate (sampleBits n k a b) .mark := by
  simpa [preparedState,Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,Input.DB] using
    Controls.setupState_samples (Input.parsedState n arcs k a b) n k a b arcs.length

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

lemma setup_native_runs (I : List Sym) (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    IRuns I Fin.elim0 Controls.setup (Input.parsedState n arcs k a b)
      (preparedState n arcs k a b) (Controls.setupCost n k a b arcs.length) := by
  apply Controls.setup_runs I _ n k a b arcs.length [] [] [] [] []
  all_goals simp [Input.parsedState,storeFields,Input.headerFields,Input.initial,IState.upd,Input.DB,
    BitCounter.Count,BitCounter.Tmp,Controls.PowerCount,Input.VertexField,Input.PathField,Input.AccuracyField,Input.ConfidenceField,Input.ArcCountField]

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
lemma EstimatorReady.upd {n : ℕ} {s : IState NS} {k a b : ℕ} {arcs : List (Fin n × Fin n)}
    (h : EstimatorReady s k a b arcs) (j : Fin NS)
    (hj : j∉readyRegisters) (hj' : j∉estimatorRegisters) (xs : List Item) :
    EstimatorReady (s.upd j xs) k a b arcs := by
  refine ⟨h.1.upd j hj xs,?_⟩
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj' hr
  simpa [IState.upd,hne] using h.2 r hr
lemma EstimatorReady.ip {n : ℕ} {s : IState NS} {k a b : ℕ} {arcs : List (Fin n × Fin n)}
    (h : EstimatorReady s k a b arcs) (ip : ℕ) : EstimatorReady {s with ip := ip} k a b arcs := h
end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}
lemma native_runs (I : List Sym) (prog : Fin P→Stmt (S+4) P) (iprog : Fin P→IStmt S P)
    (hprog : ∀ j, prog j=compile (iprog j)) {p : IStmt S P} {s s' : IState S} {C : ℕ}
    (h : IRuns I iprog p s s' C) : Runs I prog (compile p) (encI s) (encI s') C := by
  obtain ⟨t,ht,h⟩ := h
  obtain ⟨u,hu,he⟩ := (NLogN.compile_correct hprog h).1
  exact ⟨u,hu.trans ht,he⟩
end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}



lemma skipInput_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P) (s : IState S) :
    Exec I prog skipInput (encI s) (encI {s with ip := s.ip+1}) 2 := by
  have h := Exec.seq (Exec.inRd (I := I) (prog := prog) (encI s) (NLogN.sq S))
    (Exec.pop (I := I) (prog := prog) ((encI s).inRd I (NLogN.sq S)) (NLogN.sq S))
  have he : ((encI s).inRd I (NLogN.sq S)).pop (NLogN.sq S)=encI {s with ip := s.ip+1} := by
    apply St.ext
    · funext r
      by_cases hr : r=NLogN.sq S
      · subst r
        simp [St.inRd,St.pop,encI,St.set,NLogN.sq]
      · simp [St.inRd,St.pop,encI,St.set,hr]
    · rfl
    · rfl
  rw [he] at h
  exact h

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine
lemma logicalInput_tape_get (input tape : List Bool) (j : ℕ) (hj : j< tape.length) :
    (logicalInput input tape).getD (input.length+1+j) codeEnd=codeBit (tape.getD j false) := by
  unfold logicalInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_map]
  have he : input.length+1+j-input.length=j+1 := by omega
  rw [he]
  change (tape.map codeBit).getD j codeEnd=codeBit (tape.getD j false)
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ hj]
  simp
end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}







lemma countWriteBits_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src dst : Fin S) (hne : src ≠ dst) (σ : St S)
    (A : List Bool) (tail : List Sym) (ht : bitOf tail.head? = none)
    (hs : σ.stk src = A.map codeBit ++ tail) :
    Exec I prog (countWriteBits src dst) σ
      (((σ.set src tail).set dst (A.reverse.map codeBit ++ σ.stk dst)).setOut
        (σ.out ++ List.replicate A.length true)) (5*A.length+1) := by
  induction A generalizing σ with
  | nil =>
    have hh : isBitT (σ.top src) = false := by simp [St.top,hs,isBitT,ht]
    have hsrc : σ.set src tail = σ := by rw [← show σ.stk src=tail from by simpa using hs]; exact set_same _ _
    simp only [List.reverse_nil,List.map_nil,List.nil_append,List.length_nil,List.replicate_zero,
      List.append_nil,mul_zero,zero_add,hsrc,set_same,St.setOut_self]
    exact Exec.loopF hh
  | cons b A ih =>
    let σ1 := ((σ.pop src).push dst (codeBit b)).outB true
    have hbody : Exec I prog
        (.seq (.ite src (fun o => decide (o=some 0))
          (.seq (.pop src) (.push dst 0)) (.seq (.pop src) (.push dst 1))) (.out true)) σ σ1 4 := by
      cases b
      · apply Exec.seq (c₁ := 3) (c₂ := 1)
        · apply Exec.iteT
          · simp [St.top,hs,codeBit]
          · exact Exec.seq (Exec.pop _ _) (Exec.push _ _ _)
        · exact Exec.out _ _
      · apply Exec.seq (c₁ := 3) (c₂ := 1)
        · apply Exec.iteF
          · simp [St.top,hs,codeBit]
          · exact Exec.seq (Exec.pop _ _) (Exec.push _ _ _)
        · exact Exec.out _ _
    have hsrc1 : σ1.stk src = A.map codeBit ++ tail := by simp [σ1,St.outB,St.push,St.pop,hs,hne]
    have hh : isBitT (σ.top src) = true := by cases b <;> simp [St.top,hs,isBitT,codeBit,bitOf]
    have hrun := Exec.loopT hh hbody (ih σ1 hsrc1)
    have he : (((σ1.set src tail).set dst (A.reverse.map codeBit ++ σ1.stk dst)).setOut
        (σ1.out ++ List.replicate A.length true)) =
      (((σ.set src tail).set dst ((b::A).reverse.map codeBit ++ σ.stk dst)).setOut
        (σ.out ++ List.replicate (b::A).length true)) := by
      apply St.ext
      · funext t
        by_cases h1 : t=src <;> by_cases h2 : t=dst <;>
          simp_all [σ1,St.setOut,St.outB,St.set,St.push,St.pop,List.reverse_cons,List.map_append,List.append_assoc]
      · rfl
      · simp [σ1,St.outB,List.replicate_succ,List.append_assoc]
    rw [he] at hrun
    convert hrun using 1 <;> simp [countWriteBits] <;> omega

lemma writeBits_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src : Fin S) (σ : St S) (A : List Bool) (tail : List Sym)
    (ht : bitOf tail.head? = none) (hs : σ.stk src = A.map codeBit ++ tail) :
    Exec I prog (writeBits src) σ ((σ.set src tail).setOut (σ.out ++ A)) (4*A.length+1) := by
  induction A generalizing σ with
  | nil =>
    have hh : isBitT (σ.top src) = false := by simp [St.top,hs,isBitT,ht]
    have hsrc : σ.set src tail = σ := by rw [← show σ.stk src=tail from by simpa using hs]; exact set_same _ _
    simp only [List.length_nil,List.map_nil,List.nil_append,List.append_nil,hsrc,St.setOut_self,mul_zero,zero_add]
    exact Exec.loopF hh
  | cons b A ih =>
    let σ1 := (σ.outB b).pop src
    have hbody : Exec I prog
        (.seq (.ite src (fun o => decide (o=some 0)) (.out false) (.out true)) (.pop src)) σ σ1 3 := by
      cases b
      · apply Exec.seq (c₁ := 2) (c₂ := 1)
        · apply Exec.iteT
          · simp [St.top,hs,codeBit]
          · exact Exec.out _ _
        · exact Exec.pop _ _
      · apply Exec.seq (c₁ := 2) (c₂ := 1)
        · apply Exec.iteF
          · simp [St.top,hs,codeBit]
          · exact Exec.out _ _
        · exact Exec.pop _ _
    have hsrc1 : σ1.stk src = A.map codeBit ++ tail := by simp [σ1,St.outB,St.pop,hs]
    have hh : isBitT (σ.top src) = true := by cases b <;> simp [St.top,hs,isBitT,codeBit,bitOf]
    have hrun := Exec.loopT hh hbody (ih σ1 hsrc1)
    have he : (σ1.set src tail).setOut (σ1.out ++ A) =
        (σ.set src tail).setOut (σ.out ++ b::A) := by
      apply St.ext
      · funext t
        by_cases h : t=src <;> simp_all [σ1,St.setOut,St.outB,St.set,St.pop]
      · rfl
      · simp [σ1,St.outB,List.append_assoc]
    rw [he] at hrun
    convert hrun using 1 <;> simp [writeBits] <;> omega


lemma writeNat_word_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src tmp : Fin S) (hne : src ≠ tmp) (σ : St S) (W : List Bool) (tail : List Sym)
    (ht : bitOf tail.head? = none) (hx : bitOf (σ.stk tmp).head? = none)
    (hs : σ.stk src = hdPos :: (W.map codeBit ++ tail)) :
    Exec I prog (writeNat src tmp) σ
      ((σ.set src tail).setOut (σ.out ++ List.replicate W.length true ++ [false] ++ W))
      (13*W.length+5) := by
  let σ0 := σ.pop src
  let σ1 := (((σ0.set src tail).set tmp (W.reverse.map codeBit ++ σ0.stk tmp)).setOut
    (σ0.out ++ List.replicate W.length true))
  let σ2 := σ1.outB false
  let σ3 := (σ2.set tmp (σ.stk tmp)).set src (W.map codeBit ++ tail)
  have h0 : σ0.stk src = W.map codeBit ++ tail := by simp [σ0,St.pop,hs]
  have hx0 : σ0.stk tmp = σ.stk tmp := by simp [σ0,St.pop,Ne.symm hne]
  have hc := countWriteBits_exec I prog src tmp hne σ0 W tail ht h0
  have hr : Exec I prog (transferBits tmp src) σ2 σ3 (4*W.length+1) := by
    have hh : σ2.stk tmp = W.reverse.map codeBit ++ σ.stk tmp := by simp [σ2,σ1,hx0,St.outB]
    have hm := transferBits_exec I prog tmp src (Ne.symm hne) σ2 W.reverse (σ.stk tmp) hx hh
    have he : (σ2.set tmp (σ.stk tmp)).set src (W.reverse.reverse.map codeBit ++ σ2.stk src) = σ3 := by
      simp [σ3,σ2,σ1,hne,St.outB]
    simpa only [List.length_reverse,he] using hm
  have hw : Exec I prog (writeBits src) σ3 ((σ3.set src tail).setOut (σ3.out ++ W))
      (4*W.length+1) := writeBits_exec I prog src σ3 W tail ht (by simp [σ3])
  have he : (σ3.set src tail).setOut (σ3.out ++ W) =
      (σ.set src tail).setOut (σ.out ++ List.replicate W.length true ++ [false] ++ W) := by
    apply St.ext
    · funext t
      by_cases h1 : t=src <;> by_cases h2 : t=tmp <;>
        simp_all [σ3,σ2,σ1,σ0,St.set,St.setOut,St.outB,St.pop]
    · rfl
    · rfl
  rw [he] at hw
  have hrun := Exec.seq (Exec.pop σ src) (Exec.seq hc (Exec.seq (Exec.out σ1 false) (Exec.seq hr hw)))
  change Exec I prog (writeNat src tmp) σ _ _ at hrun
  convert hrun using 1
  omega

lemma writeNat_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src tmp : Fin S) (hne : src ≠ tmp) (σ : St S) (n : ℕ) (tail : List Sym)
    (ht : bitOf tail.head? = none) (hx : bitOf (σ.stk tmp).head? = none)
    (hs : σ.stk src = Item.enc (.int (n : ℤ)) ++ tail) :
    Exec I prog (writeNat src tmp) σ
      ((σ.set src tail).setOut (σ.out ++ HypergraphUnreliability.FPRAS.natCode n))
      (13*(Nat.bits n).length+5) := by
  have henc : Item.enc (.int (n : ℤ)) = hdPos::(Nat.bits n).map codeBit := by
    simp [Item.enc,hdOf,zbits,nbits_eq_bits]
  have h := writeNat_word_exec I prog src tmp hne σ (Nat.bits n) tail ht hx (by simpa [henc] using hs)
  simpa only [HypergraphUnreliability.FPRAS.natCode,List.append_assoc] using h

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
open HypergraphUnreliability.FPRAS
variable {P : ℕ}



lemma writeFraction_exec (I : List Sym) (prog : Fin P→Stmt (128+4) P) (s : IState 128) (f : Frac)
    (hn : s.G 126=[.int (f.num : ℤ)]) (hd : s.G 127=[.int (f.den : ℤ)]) :
    ∃ σ, Exec I prog writeFraction (encI s) σ
      (13*(Nat.bits f.num).length+13*(Nat.bits f.den).length+10) ∧ σ.out=s.out++fracCode f := by
  let σ0 := encI s
  let σ1 := (σ0.set (ι (126 : Fin 128)) []).setOut (s.out++natCode f.num)
  let σ2 := (σ1.set (ι (127 : Fin 128)) []).setOut (s.out++natCode f.num++natCode f.den)
  have h0 : Exec I prog (writeNat (ι (126 : Fin 128)) (NLogN.sq 128)) σ0 σ1
      (13*(Nat.bits f.num).length+5) := by
    have h := writeNat_exec I prog (ι (126 : Fin 128)) (NLogN.sq 128) (iota_ne_sq _) σ0 f.num []
      (by decide) (by simp [σ0,encI,bitOf,NLogN.sq]) (by simp [σ0,hn,encL])
    exact h
  have h1 : Exec I prog (writeNat (ι (127 : Fin 128)) (NLogN.sq 128)) σ1 σ2
      (13*(Nat.bits f.den).length+5) := by
    have h := writeNat_exec I prog (ι (127 : Fin 128)) (NLogN.sq 128) (iota_ne_sq _) σ1 f.den []
      (by decide) (by simp [σ1,σ0,St.setOut,St.set,encI,bitOf,NLogN.sq,ι])
      (by simp [σ1,σ0,St.setOut,St.set,encI,hd,encL,ι])
    simpa [σ2,σ1,σ0] using h
  refine ⟨σ2,?_,?_⟩
  · have h := Exec.seq h0 h1
    change Exec I prog writeFraction (encI s) σ2 _ at h
    convert h using 1 <;> omega
  · simp [σ2,fracCode,List.append_assoc]

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS
attribute [local simp] Coins


lemma rawProg_correct (j : Fin 1) : rawProg j=compile (Wedge.prog j) := rfl







lemma positiveRaw_runs (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool)
    (hk : 1≤ k) (hTape : sampleBits n k a b≤ tape.length) :
    ∃ σ, Runs (logicalInput (graphInputControls n arcs k a b) tape) rawProg positiveRaw
      (encI (Input.parsedState n arcs k a b)) σ (positiveCost n arcs k a b tape) ∧
      σ.out=fracCode (estimateFraction (walkTensor n arcs k) a b (tapeSamples n k a b tape)) := by
  let I := logicalInput (graphInputControls n arcs k a b) tape
  let S := sampleBits n k a b
  let ω : Fin S→Bool := fun j => tape.getD j.val false
  let W := List.ofFn ω
  let s1 := preparedState n arcs k a b
  let s2 : IState NS := {s1 with ip := s1.ip+1}
  let s3 : IState NS := { (s2.upd 51 []).upd Coins (W.map (fun b => Item.int (sgn b))) with ip := s2.ip+W.length }
  let f := estimateFraction (walkTensor n arcs k) a b (tapeSamples n k a b tape)
  have h0 : Runs I rawProg (compile (liftClosed Controls.setup)) (encI (Input.parsedState n arcs k a b))
      (encI s1) (Controls.setupCost n k a b arcs.length) :=
    native_closed_runs I rawProg Wedge.prog rawProg_correct (setup_native_runs I n arcs k a b)
  have h1 : Exec I rawProg skipInput (encI s1) (encI s2) 2 := skipInput_exec I rawProg s1
  have h2 : Exec I rawProg (bulkSigns 51 Coins) (encI s2) (encI s3) (8*S+2) := by
    have h := bulkSigns_exec I rawProg (51 : Fin NS) Coins (by decide) s2 W
      (by simpa [s2,s1,W,S] using prepared_samples n arcs k a b)
      (by
        intro j hj
        have hjS : j< S := by simpa [W] using hj
        have ht : j< tape.length := hjS.trans_le hTape
        have hh := logicalInput_tape_get (graphInputControls n arcs k a b) tape j ht
        simpa [s2,s1,prepared_ip,W,ω,List.getElem_ofFn] using hh)
    have hcoin : s2.G Coins=[] := prepared_coins n arcs k a b
    simpa [s3,W,List.length_ofFn,hcoin,S] using h
  have hReady : EstimatorReady s3 k a b arcs :=
    ((((prepared_ready n arcs k a b).ip _).upd 51 (by decide) (by decide) _).upd Coins (by decide) (by decide) _).ip _
  have hCoins : s3.G Coins=(List.ofFn (fun j => sgn (ω j))).map Item.int ++ [] := by
    simp [s3,W,List.map_ofFn,Function.comp_def]
  obtain ⟨s4,h3,hn,hd,hip,hout⟩ := nativeEstimator_runs I s3 arcs ω [] hk hReady hCoins
  have h3raw : Runs I rawProg (compile nativeEstimator) (encI s3) (encI s4) (estimatorCost n k a b arcs.length) :=
    native_runs I rawProg Wedge.prog rawProg_correct h3
  obtain ⟨σ,h4,ho⟩ := writeFraction_exec I rawProg s4 f hn hd
  refine ⟨σ,?_,?_⟩
  · have h := Raw.seq h0 (Raw.seq (Raw.of_exec h1) (Raw.seq (Raw.of_exec h2)
      (Raw.seq h3raw (Raw.of_exec h4))))
    change Runs I rawProg positiveRaw (encI (Input.parsedState n arcs k a b)) σ _ at h
    apply Raw.mono h
    unfold positiveCost writtenCost
    dsimp only [f,S]
    omega
  · rw [ho,hout]
    simp [s3,s2,s1,prepared_out,f]

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hTape : @LE.le.{0} Nat instLENat (KoanaKPaths.Main.sampleBits n k a b) (@List.length.{0} Bool tape)),
  @Exists.{1}
    (NLogN.St
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun
      (σ :
        NLogN.St
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) =>
    And
      (@NLogN.Runs
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (KoanaKPaths.Machine.logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape)
        KoanaKPaths.Machine.Trial.rawProg KoanaKPaths.Machine.Trial.positiveRaw
        (@NLogN.encI KoanaKPaths.Machine.Trial.NS (KoanaKPaths.Machine.Input.parsedState n arcs k a b)) σ
        (KoanaKPaths.Machine.Trial.positiveCost n arcs k a b tape))
      (@Eq.{1} (List.{0} Bool)
        (@NLogN.St.out
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Trial.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          σ)
        (HypergraphUnreliability.FPRAS.fracCode
          (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
            (KoanaKPaths.Main.tapeSamples n k a b tape)))) := by
  exact @KoanaKPaths.Machine.Trial.positiveRaw_runs

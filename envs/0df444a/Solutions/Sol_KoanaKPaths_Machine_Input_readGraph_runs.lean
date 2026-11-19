-- Prove2me | solution 1 for KoanaKPaths.Machine.Input.readGraph_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.634113+00:00
-- url     : https://prove2.me/submissions/9fcf8f9b-e03d-475b-918f-c6509791c1d1

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_Input_readArcs_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_transferBits_exec
import Theorems.Thm_NLogN_compile_correct
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

lemma readCountedBits_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (cnt dst : Fin S) (hne : cnt ≠ dst) (σ : St S)
    (W : List Bool) (tail : List Sym) (ht : tail.head? ≠ some 1)
    (hs : σ.stk cnt = List.replicate W.length 1 ++ tail)
    (hinput : ∀ j (hj : j < W.length), I.getD (σ.ip+j) codeEnd = codeBit W[j]) :
    Exec I prog (readCountedBits cnt dst) σ
      (((σ.set cnt tail).set dst (W.reverse.map codeBit ++ σ.stk dst)).setIp (σ.ip+W.length))
      (3*W.length+1) := by
  induction W generalizing σ with
  | nil =>
    have hh : (decide (σ.top cnt=some 1)) = false := by simp [St.top,hs,ht]
    have hcnt : σ.set cnt tail = σ := by rw [← show σ.stk cnt = tail from by simpa using hs]; exact set_same _ _
    unfold readCountedBits
    simp only [List.length_nil,List.replicate_zero,List.nil_append,List.reverse_nil,List.map_nil,
      hcnt,set_same,Nat.add_zero,mul_zero,zero_add,setIp_same]
    exact Exec.loopF hh
  | cons b W ih =>
    let σ1 := (σ.pop cnt).inRd I dst
    have hbit : I.getD σ.ip codeEnd = codeBit b := by
      have hh := hinput 0 (by simp)
      change I.getD (σ.ip+0) codeEnd = codeBit b at hh
      simpa only [Nat.add_zero] using hh
    have hcnt : σ1.stk cnt = List.replicate W.length 1 ++ tail := by
      simp [σ1,St.inRd,St.pop,hs,hne]
    have hi : ∀ j (hj : j < W.length), I.getD (σ1.ip+j) codeEnd = codeBit W[j] := by
      intro j hj
      have hh := hinput (j+1) (by simpa using Nat.succ_lt_succ hj)
      simpa [σ1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hbody : Exec I prog (.seq (.pop cnt) (.inRd dst)) σ σ1 2 :=
      Exec.seq (Exec.pop _ _) (Exec.inRd _ _)
    have htop : (decide (σ.top cnt=some 1)) = true := by simp [St.top,hs,List.replicate_succ]
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
    convert hrun using 1 <;> simp [readCountedBits] <;> omega

lemma replicate_cons_same {α : Type} (m : ℕ) (x : α) (L : List α) :
    List.replicate m x ++ x::L = x::(List.replicate m x ++ L) := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons x) ih

lemma unaryLoop_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (tmp cnt : Fin S) (hne : tmp ≠ cnt) (σ : St S)
    (m : ℕ) (tail : List Sym)
    (hs : σ.stk tmp = (if m=0 then 0 else 1) :: tail)
    (hinput : ∀ j, j < m → I.getD (σ.ip+j) codeEnd = if j+1 < m then 1 else 0) :
    Exec I prog (.loop tmp (fun o => decide (o=some 1)) (unaryBody tmp cnt)) σ
      (((σ.set tmp (0::tail)).set cnt (List.replicate m 1 ++ σ.stk cnt)).setIp (σ.ip+m))
      (4*m+1) := by
  induction m generalizing σ with
  | zero =>
    have hh : decide (σ.top tmp=some 1) = false := by simp [St.top,hs]
    have htmp : σ.set tmp (0::tail) = σ := by rw [← show σ.stk tmp=0::tail from by simpa using hs]; exact set_same _ _
    simp only [List.replicate_zero,List.nil_append,htmp,set_same,Nat.add_zero,mul_zero,zero_add,setIp_same]
    exact Exec.loopF hh
  | succ m ih =>
    let σ1 := ((σ.pop tmp).push cnt 1).inRd I tmp
    have hbit : I.getD σ.ip codeEnd = if m=0 then 0 else 1 := by
      have h := hinput 0 (by omega)
      by_cases hm : m=0
      · simpa [hm] using h
      · have hp : 0 < m := Nat.pos_of_ne_zero hm
        simpa [hm,show 1 < m+1 by omega] using h
    have htmp1 : σ1.stk tmp = (if m=0 then 0 else 1)::tail := by
      simp [σ1,St.inRd,St.push,St.pop,hs,hne]
      simpa only [List.getD_eq_getElem?_getD] using hbit
    have hfuture : ∀ j, j < m → I.getD (σ1.ip+j) codeEnd = if j+1 < m then 1 else 0 := by
      intro j hj
      have hh := hinput (j+1) (by omega)
      have he : (j+1+1 < m+1) ↔ j+1 < m := by omega
      simpa [σ1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,he] using hh
    have hbody : Exec I prog (unaryBody tmp cnt) σ σ1 3 :=
      Exec.seq (Exec.pop _ _) (Exec.seq (Exec.push _ _ _) (Exec.inRd _ _))
    have hh : decide (σ.top tmp=some 1) = true := by simp [St.top,hs]
    have hrun := Exec.loopT hh hbody (ih σ1 htmp1 hfuture)
    have hfinal :
        (((σ1.set tmp (0::tail)).set cnt (List.replicate m 1 ++ σ1.stk cnt)).setIp (σ1.ip+m)) =
        (((σ.set tmp (0::tail)).set cnt (List.replicate (m+1) 1 ++ σ.stk cnt)).setIp (σ.ip+(m+1))) := by
      apply St.ext
      · funext t
        by_cases ht : t=tmp <;> by_cases hc : t=cnt <;>
          simp_all [σ1,St.setIp,St.set,St.inRd,St.push,St.pop,List.replicate_succ,replicate_cons_same,List.append_assoc]
      · simp [σ1,St.setIp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · rfl
    rw [hfinal] at hrun
    convert hrun using 1 <;> omega

lemma readUnary_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (tmp cnt : Fin S) (hne : tmp ≠ cnt) (σ : St S) (m : ℕ)
    (hinput : ∀ j, j ≤ m → I.getD (σ.ip+j) codeEnd = if j < m then 1 else 0) :
    Exec I prog (readUnary tmp cnt) σ
      ((σ.set cnt (List.replicate m 1 ++ σ.stk cnt)).setIp (σ.ip+m+1)) (4*m+3) := by
  let σ0 := σ.inRd I tmp
  let σF := (((σ0.set tmp (0::σ.stk tmp)).set cnt (List.replicate m 1 ++ σ0.stk cnt)).setIp (σ0.ip+m))
  have hbit : I.getD σ.ip codeEnd = if m=0 then 0 else 1 := by
    have hh := hinput 0 (by omega)
    by_cases hm : m=0
    · simpa [hm] using hh
    · have hp : 0 < m := Nat.pos_of_ne_zero hm
      simpa [hm,hp] using hh
  have htmp : σ0.stk tmp = (if m=0 then 0 else 1)::σ.stk tmp := by
    simp only [σ0,St.inRd,Function.update_self,hbit]
  have hfuture : ∀ j, j < m → I.getD (σ0.ip+j) codeEnd = if j+1 < m then 1 else 0 := by
    intro j hj
    have hh := hinput (j+1) (by omega)
    simpa [σ0,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have hloop : Exec I prog (.loop tmp (fun o => decide (o=some 1)) (unaryBody tmp cnt)) σ0 σF (4*m+1) :=
    unaryLoop_exec I prog tmp cnt hne σ0 m (σ.stk tmp) htmp hfuture
  have hrun := Exec.seq (Exec.inRd σ tmp) (Exec.seq hloop (Exec.pop σF tmp))
  have hfinal : σF.pop tmp =
      (σ.set cnt (List.replicate m 1 ++ σ.stk cnt)).setIp (σ.ip+m+1) := by
    apply St.ext
    · funext t
      by_cases ht : t=tmp <;> by_cases hc : t=cnt <;>
        simp_all [σF,σ0,St.setIp,St.set,St.inRd,St.pop]
    · simp [σF,σ0,St.setIp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · rfl
  rw [hfinal] at hrun
  change Exec I prog (readUnary tmp cnt) σ _ (1+((4*m+1)+1)) at hrun
  have hcost : 1+((4*m+1)+1) = 4*m+3 := by omega
  simpa only [hcost] using hrun

lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

lemma parseNat_word_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (tmp cnt rev dst : Fin S)
    (hnd : tmp≠cnt ∧ tmp≠rev ∧ tmp≠dst ∧ cnt≠rev ∧ cnt≠dst ∧ rev≠dst)
    (σ : St S) (W : List Bool) (hcnt : σ.stk cnt = []) (hrev : σ.stk rev = [])
    (hu : ∀ j, j ≤ W.length → I.getD (σ.ip+j) codeEnd = if j < W.length then 1 else 0)
    (hb : ∀ j (hj : j < W.length), I.getD (σ.ip+W.length+1+j) codeEnd = codeBit W[j]) :
    Exec I prog (parseNat tmp cnt rev dst) σ
      ((σ.set dst (hdPos :: W.map codeBit ++ σ.stk dst)).setIp (σ.ip+2*W.length+1))
      (11*W.length+6) := by
  let m := W.length
  let σU := (σ.set cnt (List.replicate m 1)).setIp (σ.ip+m+1)
  have hU : Exec I prog (readUnary tmp cnt) σ σU (4*m+3) := by
    simpa only [hcnt,List.append_nil] using readUnary_exec I prog tmp cnt hnd.1 σ m hu
  have hUs : σU.stk cnt = List.replicate W.length 1 ++ [] := by simp [σU,m]
  have hUb : ∀ j (hj : j < W.length), I.getD (σU.ip+j) codeEnd = codeBit W[j] := by
    intro j hj
    exact hb j hj
  let σB := (((σU.set cnt []).set rev (W.reverse.map codeBit ++ σU.stk rev)).setIp (σU.ip+W.length))
  have hB : Exec I prog (readCountedBits cnt rev) σU σB (3*m+1) :=
    readCountedBits_exec I prog cnt rev hnd.2.2.2.1 σU W [] (by decide) hUs hUb
  have hBs : σB.stk rev = W.reverse.map codeBit ++ [] := by
    simp [σB,σU,St.setIp,St.set,hnd.2.2.2.1.symm,hrev]
  let σM := (σB.set rev []).set dst ((W.reverse.reverse).map codeBit ++ σB.stk dst)
  have hM : Exec I prog (transferBits rev dst) σB σM (4*m+1) := by
    simpa only [List.length_reverse] using
      transferBits_exec I prog rev dst hnd.2.2.2.2.2 σB W.reverse [] rfl hBs
  have hrun := Exec.seq hU (Exec.seq hB (Exec.seq hM (Exec.push σM dst hdPos)))
  have hfinal : σM.push dst hdPos =
      (σ.set dst (hdPos :: W.map codeBit ++ σ.stk dst)).setIp (σ.ip+2*W.length+1) := by
    apply St.ext
    · funext t
      rcases hnd with ⟨htc,htr,htd,hcr,hcd,hrd⟩
      by_cases ht : t=tmp <;> by_cases hc : t=cnt <;> by_cases hr : t=rev <;> by_cases hd : t=dst <;>
        simp_all [σM,σB,σU,St.setIp,St.set,St.push,List.reverse_reverse]
    · simp [σM,σB,σU,m,St.setIp]
      omega
    · rfl
  rw [hfinal] at hrun
  change Exec I prog (parseNat tmp cnt rev dst) σ _
    ((4*m+3)+((3*m+1)+((4*m+1)+1))) at hrun
  have hcost : (4*m+3)+((3*m+1)+((4*m+1)+1)) = 11*W.length+6 := by dsimp [m]; omega
  simpa only [hcost] using hrun



lemma natCode_map (n : ℕ) :
    (HypergraphUnreliability.FPRAS.natCode n).map codeBit = wordCode (Nat.bits n) := by
  simp [HypergraphUnreliability.FPRAS.natCode,wordCode,codeBit]

lemma wordCode_length (W : List Bool) : (wordCode W).length = 2*W.length+1 := by
  simp [wordCode]
  omega

lemma wordCode_unary (W : List Bool) (j : ℕ) (hj : j ≤ W.length) :
    (wordCode W).getD j codeEnd = if j < W.length then 1 else 0 := by
  unfold wordCode
  by_cases h : j < W.length
  · rw [List.getD_append _ _ _ _ (by simpa using h),List.getD_replicate 1 h,if_pos h]
  · have he : j=W.length := by omega
    subst j
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

lemma wordCode_payload (W : List Bool) (j : ℕ) (hj : j < W.length) :
    (wordCode W).getD (W.length+1+j) codeEnd = codeBit W[j] := by
  unfold wordCode
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate]
  rw [show W.length+1+j-W.length = j+1 by omega,List.getD_cons_succ]
  simp [List.getD_eq_getElem?_getD,hj]

lemma input_slice (I pre code post : List Sym) (hI : I=pre++code++post)
    (j : ℕ) (hj : j < code.length) :
    I.getD (pre.length+j) codeEnd = code.getD j codeEnd := by
  rw [hI,List.append_assoc,List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ hj]

lemma parseNat_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (tmp cnt rev dst : Fin S)
    (hnd : tmp≠cnt ∧ tmp≠rev ∧ tmp≠dst ∧ cnt≠rev ∧ cnt≠dst ∧ rev≠dst)
    (σ : St S) (n : ℕ) (pre post : List Sym)
    (hcnt : σ.stk cnt = []) (hrev : σ.stk rev = [])
    (hI : I=pre++(HypergraphUnreliability.FPRAS.natCode n).map codeBit++post) (hip : σ.ip=pre.length) :
    Exec I prog (parseNat tmp cnt rev dst) σ
      ((σ.set dst (Item.enc (.int (n : ℤ)) ++ σ.stk dst)).setIp
        (σ.ip+(HypergraphUnreliability.FPRAS.natCode n).length))
      (11*(Nat.bits n).length+6) := by
  have hcode : I=pre++wordCode (Nat.bits n)++post := by simpa only [natCode_map] using hI
  have hu : ∀ j, j ≤ (Nat.bits n).length → I.getD (σ.ip+j) codeEnd =
      if j < (Nat.bits n).length then 1 else 0 := by
    intro j hj
    rw [hip,input_slice I pre _ post hcode j (by rw [wordCode_length]; omega)]
    exact wordCode_unary _ _ hj
  have hb : ∀ j (hj : j < (Nat.bits n).length), I.getD (σ.ip+(Nat.bits n).length+1+j) codeEnd =
      codeBit (Nat.bits n)[j] := by
    intro j hj
    have he : σ.ip+(Nat.bits n).length+1+j = pre.length+((Nat.bits n).length+1+j) := by rw [hip]; omega
    rw [he,input_slice I pre _ post hcode _ (by rw [wordCode_length]; omega)]
    exact wordCode_payload _ _ hj
  have h := parseNat_word_exec I prog tmp cnt rev dst hnd σ (Nat.bits n) hcnt hrev hu hb
  have he : Item.enc (.int (n : ℤ)) = hdPos :: (Nat.bits n).map codeBit := by
    simp [Item.enc,hdOf,zbits,nbits_eq_bits]
  have hl : (HypergraphUnreliability.FPRAS.natCode n).length = 2*(Nat.bits n).length+1 := by
    simp [HypergraphUnreliability.FPRAS.natCode]
    omega
  simpa only [he,List.cons_append,hl,Nat.add_assoc] using h

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
namespace KoanaKPaths.Machine
variable {S P : ℕ}














@[simp] lemma enc_work_stk (s : IState S) (i : Fin S) : (encI s).stk (ι i) = encL (s.G i) := by
  simp [encI,ι,i.isLt]

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









end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}



lemma iota_ne_s1 (i : Fin S) : ι i≠NLogN.s1 S := by
  intro h
  have he := congrArg (fun x : Fin (S+4) => x.val) h
  simp only [ι,Fin.val_castAdd,NLogN.s1] at he
  omega
lemma iota_ne_s2 (i : Fin S) : ι i≠NLogN.s2 S := by
  intro h
  have he := congrArg (fun x : Fin (S+4) => x.val) h
  simp only [ι,Fin.val_castAdd,NLogN.s2] at he
  omega

@[simp] lemma enc_extra_stk (s : IState S) (x : Fin (S+4)) (hx : S≤x.val) : (encI s).stk x=[] := by
  simp [encI,show ¬x.val<S by omega]

lemma parseItem_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P) (dst : Fin S)
    (s : IState S) (n : ℕ) (pre post : List Sym)
    (hI : I=pre++(HypergraphUnreliability.FPRAS.natCode n).map codeBit++post) (hip : s.ip=pre.length) :
    Exec I prog (parseItem dst) (encI s)
      (encI {s.upd dst (.int (n : ℤ)::s.G dst) with
        ip := s.ip+(HypergraphUnreliability.FPRAS.natCode n).length}) (11*n.bits.length+6) := by
  have hnd : NLogN.sq S≠NLogN.s1 S ∧ NLogN.sq S≠NLogN.s2 S ∧ NLogN.sq S≠ι dst ∧
      NLogN.s1 S≠NLogN.s2 S ∧ NLogN.s1 S≠ι dst ∧ NLogN.s2 S≠ι dst := by
    refine ⟨?_,?_,sq_ne_iota dst,?_,Ne.symm (iota_ne_s1 dst),Ne.symm (iota_ne_s2 dst)⟩ <;>
      intro h <;> have he := congrArg (fun x : Fin (S+4) => x.val) h <;>
      simp only [NLogN.sq,NLogN.s1,NLogN.s2] at he <;> omega
  have h := parseNat_exec I prog (NLogN.sq S) (NLogN.s1 S) (NLogN.s2 S) (ι dst) hnd (encI s) n pre post
    (by apply enc_extra_stk; simp [NLogN.s1]) (by apply enc_extra_stk; simp [NLogN.s2]) hI hip
  have he : ((encI s).set (ι dst) (Item.enc (.int (n : ℤ)) ++ (encI s).stk (ι dst))).setIp
      ((encI s).ip+(HypergraphUnreliability.FPRAS.natCode n).length) =
      encI {s.upd dst (.int (n : ℤ)::s.G dst) with
        ip := s.ip+(HypergraphUnreliability.FPRAS.natCode n).length} := by
    apply St.ext
    · funext x
      by_cases hx : x.val<S
      · let j : Fin S := ⟨x.val,hx⟩
        have hj : x=ι j := Fin.ext rfl
        rw [hj]
        by_cases hd : j=dst <;> simp_all [IState.upd,encL,List.flatMap_cons]
      · have hxd : x≠ι dst := by
          intro h
          have hv := congrArg (fun x : Fin (S+4) => x.val) h
          simp only [ι,Fin.val_castAdd] at hv
          omega
        simp [set_stk_ne _ hxd,encI,hx]
    · rfl
    · rfl
  simpa only [parseItem,he] using h

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
namespace KoanaKPaths.Machine
variable {S P : ℕ}









lemma parseFields_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P)
    (fields : List (Fin S × ℕ)) (s : IState S) (pre post : List Sym)
    (hI : I=pre++fieldSymbols fields++post) (hip : s.ip=pre.length) :
    Exec I prog (parseFields (fields.map Prod.fst)) (encI s) (encI (storeFields s fields)) (fieldCost fields) := by
  induction fields generalizing s pre with
  | nil =>
    simpa [parseFields,storeFields,fieldCost] using (Exec.skip (I := I) (prog := prog) (encI s))
  | cons field fields ih =>
    rcases field with ⟨d,n⟩
    let s1 : IState S := {s.upd d (.int (n : ℤ)::s.G d) with
      ip := s.ip+(HypergraphUnreliability.FPRAS.natCode n).length}
    let pre1 := pre++(HypergraphUnreliability.FPRAS.natCode n).map codeBit
    have hfirst : Exec I prog (parseItem d) (encI s) (encI s1) (11*n.bits.length+6) :=
      parseItem_exec I prog d s n pre (fieldSymbols fields++post)
        (by simpa [fieldSymbols,List.append_assoc] using hI) hip
    have hrest := ih s1 pre1 (by simpa [pre1,fieldSymbols,List.append_assoc] using hI)
      (by simp [s1,pre1,hip])
    have hrun := Exec.seq hfirst hrest
    change Exec I prog (parseFields ((d,n)::fields |>.map Prod.fst)) (encI s)
      (encI (storeFields s ((d,n)::fields))) _ at hrun
    convert hrun using 1
    simp [fieldCost]
    omega

lemma encI_init (S : ℕ) : encI (⟨fun _ => [],0,[]⟩ : IState S)=St.init (S+4) := by
  apply St.ext
  · funext i
    simp [encI,encL,St.init]
  · rfl
  · rfl


lemma storeFields_ip (s : IState S) (fields : List (Fin S × ℕ)) :
    (storeFields s fields).ip=s.ip+(fieldSymbols fields).length := by
  induction fields generalizing s with
  | nil => simp [storeFields,fieldSymbols]
  | cons p fields ih =>
    rcases p with ⟨d,n⟩
    simp only [storeFields,ih,fieldSymbols,List.flatMap_cons,List.length_append,List.length_map]
    omega

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input





attribute [local simp] VertexField PathField AccuracyField ConfidenceField ArcCountField Counter
attribute [local simp] BitCounter.Source BitCounter.Count BitCounter.Tmp







lemma prepareArcCount_runs (I : List Sym) (s : IState NS) (m : ℕ) (tail : List Item)
    (hm : s.G ArcCountField=.int (m : ℤ)::tail)
    (hc : s.G Counter=[]) (hn : s.G BitCounter.Count=[]) (hx : s.G BitCounter.Tmp=[]) :
    IRuns I Fin.elim0 prepareArcCount s (s.upd Counter (List.replicate m .mark)) (2000*(m+1)) := by
  let s1 := s.upd BitCounter.Source (.int (m : ℤ)::s.G BitCounter.Source)
  let s2 := (s1.upd BitCounter.Source (s.G BitCounter.Source)).upd BitCounter.Count
    (List.replicate m .mark ++ s1.G BitCounter.Count)
  let s3 := (s2.upd BitCounter.Count []).upd Counter (List.replicate m .mark ++ s2.G Counter)
  have h1 : IExec I Fin.elim0 (.op (.dup ArcCountField BitCounter.Source)) s s1
      (dupCost (zsz (m : ℤ))+17) := .op (.dup (by decide) hm)
  have h2 : IRuns I Fin.elim0 BitCounter.toMarks s1 s2 (1000*(m+1)) :=
    BitCounter.toMarks_runs I s1 m (s.G BitCounter.Source) (by simp [s1])
      (by simp [s1,hn,cls]) (by simp [s1,hx])
  have h3 : IExec I Fin.elim0 (moveMarks BitCounter.Count Counter) s2 s3 (32*m+30) :=
    moveMarks_exec I BitCounter.Count Counter (by decide) s2 m [] (by simp [cls])
      (by simp [s2,s1,hn])
  have he : s3=s.upd Counter (List.replicate m .mark) := by
    cases s with
    | mk G ip o =>
      have hc' : G Counter=[] := hc
      have hn' : G BitCounter.Count=[] := hn
      simp only [Counter,BitCounter.Count] at hc' hn'
      simp only [s3,s2,s1,IState.upd]
      congr 1
      funext i
      by_cases hC : i=Counter
      · subst i; simp [Function.update_apply,hc']
      by_cases hN : i=BitCounter.Count
      · subst i; simp [Function.update_apply,hn']
      by_cases hS : i=BitCounter.Source
      · subst i; simp [Function.update_apply]
      simp [Function.update_apply,hC,hN,hS]
  have hrun := Native.seq (Native.of_exec h1) (Native.seq h2 (Native.of_exec h3))
  change IRuns I Fin.elim0 prepareArcCount s _ _ at hrun
  rw [he] at hrun
  apply Native.mono hrun
  have hw : zsz (m : ℤ)≤ m := by
    have hh : m.size≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
    simpa [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len] using hh
  simp only [dupCost,zipCost,moveCost]
  nlinarith

lemma readHeader_exec {P : ℕ} (I : List Sym) (prog : Fin P→Stmt (NS+4) P)
    (n k a b m : ℕ) (s : IState NS) (pre post : List Sym)
    (hI : I=pre++fieldSymbols (headerFields n k a b m)++post) (hip : s.ip=pre.length) :
    Exec I prog readHeader (encI s) (encI (storeFields s (headerFields n k a b m)))
      (fieldCost (headerFields n k a b m)) := by
  simpa only [readHeader,headerFields,List.map_cons,List.map_nil,Prod.fst] using
    parseFields_exec I prog (headerFields n k a b m) s pre post hI hip

end KoanaKPaths.Machine.Input

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

lemma seq (h1 : Runs I prog p s s1 c) (h2 : Runs I prog q s1 s2 d) :
    Runs I prog (.seq p q) s s2 (c+d) := by
  obtain ⟨t,ht,h1⟩ := h1
  obtain ⟨u,hu,h2⟩ := h2
  exact ⟨t+u,Nat.add_le_add ht hu,.seq h1 h2⟩
end KoanaKPaths.Machine.Raw

end

section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input
attribute [local simp] VertexField PathField AccuracyField ConfidenceField ArcCountField Counter DB
attribute [local simp] BitCounter.Count BitCounter.Tmp
variable {P : ℕ}



lemma arcSymbols_values {n : ℕ} (arcs : List (Fin n × Fin n)) :
    arcSymbols (arcValues arcs)=(arcs.flatMap (fun p => HypergraphUnreliability.FPRAS.natCode p.1.val ++
      HypergraphUnreliability.FPRAS.natCode p.2.val)).map codeBit := by
  induction arcs with
  | nil => rfl
  | cons p arcs ih =>
    have h := congrArg (fun L => (HypergraphUnreliability.FPRAS.natCode p.1.val).map codeBit ++
      (HypergraphUnreliability.FPRAS.natCode p.2.val).map codeBit ++ L) ih
    simpa [arcValues,arcSymbols,List.map_append,List.append_assoc] using h

lemma graphInput_symbols (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) :
    logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape =
      fieldSymbols (headerFields n k a b arcs.length) ++ arcSymbols (arcValues arcs) ++ codeSep::tape.map codeBit := by
  simp [logicalInput,KoanaKPaths.Main.graphInputControls,HypergraphUnreliability.FPRAS.listCode,
    fieldSymbols,headerFields,arcSymbols_values,List.map_append,List.append_assoc]

lemma graphInput_length (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (KoanaKPaths.Main.graphInputControls n arcs k a b).length =
      (fieldSymbols (headerFields n k a b arcs.length)).length+(arcSymbols (arcValues arcs)).length := by
  have h := congrArg List.length (graphInput_symbols n arcs k a b [])
  simp only [logicalInput,List.length_append,List.length_map,List.length_cons,List.length_nil] at h
  omega









lemma readGraph_runs (prog : Fin P→Stmt (NS+4) P) (iprog : Fin P→IStmt NS P)
    (hprog : ∀ j, prog j=compile (iprog j)) (n : ℕ) (arcs : List (Fin n × Fin n))
    (k a b : ℕ) (tape : List Bool) :
    Runs (logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape) prog readGraph
      (St.init (NS+4)) (encI (parsedState n arcs k a b)) (graphReadCost n arcs k a b) := by
  let I := logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape
  let fields := headerFields n k a b arcs.length
  let h := storeFields initial fields
  let ar := arcValues arcs
  let s1 := h.upd Counter (List.replicate arcs.length .mark)
  have hsym : I=fieldSymbols fields++arcSymbols ar++codeSep::tape.map codeBit :=
    graphInput_symbols n arcs k a b tape
  have hhead : Exec I prog readHeader (encI initial) (encI h) (fieldCost fields) :=
    readHeader_exec I prog n k a b arcs.length initial []
      (arcSymbols ar++codeSep::tape.map codeBit) (by simpa only [List.nil_append,List.append_assoc] using hsym) rfl
  have hArcCount : h.G ArcCountField=.int (arcs.length : ℤ)::[] := by
    simp [h,fields,storeFields,headerFields,initial,IState.upd]
  have hCounter : h.G Counter=[] := by simp [h,fields,storeFields,headerFields,initial,IState.upd]
  have hNativeCount : h.G BitCounter.Count=[] := by simp [h,fields,storeFields,headerFields,initial,IState.upd]
  have hNativeTmp : h.G BitCounter.Tmp=[] := by simp [h,fields,storeFields,headerFields,initial,IState.upd]
  have hDB : h.G DB=[] := by simp [h,fields,storeFields,headerFields,initial,IState.upd]
  have hcount : Runs I prog (compile (liftClosed prepareArcCount)) (encI h) (encI s1)
      (2000*(arcs.length+1)) :=
    native_closed_runs I prog iprog hprog (prepareArcCount_runs I h arcs.length [] hArcCount hCounter hNativeCount hNativeTmp)
  have hread := readArcs_exec I prog ar s1 (fieldSymbols fields) (codeSep::tape.map codeBit)
    (by simp [s1,ar,arcValues]) hsym
    (by simpa only [s1,IState.upd_ip,h,initial,Nat.zero_add] using storeFields_ip initial fields)
  have he : {(s1.upd Counter []).upd DB (arcItems ar ++ s1.G DB) with ip := s1.ip+(arcSymbols ar).length} =
      parsedState n arcs k a b := by
    apply itemState_ext
    · intro i
      by_cases hC : i=Counter
      · subst i; simp [parsedState,s1,hCounter] <;> exact hCounter
      by_cases hD : i=DB
      · subst i; simp [parsedState,s1,hDB,ar,h,fields]
      simp [parsedState,s1,IState.upd,hC,hD,h,fields]
    · simp only [s1,IState.upd_ip]
      have hip := storeFields_ip initial fields
      change h.ip+(arcSymbols ar).length=(KoanaKPaths.Main.graphInputControls n arcs k a b).length
      rw [graphInput_length]
      simpa only [h,fields,ar,initial,Nat.zero_add] using congrArg (fun j => j+(arcSymbols ar).length) hip
    · rfl
  rw [he] at hread
  have hrun := Raw.seq (Raw.of_exec hhead) (Raw.seq hcount (Raw.of_exec hread))
  change Runs I prog readGraph (encI initial) _ _ at hrun
  simpa only [initial,encI_init,I,ar,graphReadCost,fields,Nat.add_assoc] using hrun

end KoanaKPaths.Machine.Input

end

theorem solution :
∀ {P : Nat}
  (prog :
    Fin P →
      NLogN.Stmt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        P)
  (iprog : Fin P → NLogN.IStmt KoanaKPaths.Machine.Input.NS P)
  (hprog :
    ∀ (j : Fin P),
      @Eq.{1}
        (NLogN.Stmt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          P)
        (prog j) (@NLogN.compile KoanaKPaths.Machine.Input.NS P (iprog j)))
  (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool),
  @NLogN.Runs
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    P (KoanaKPaths.Machine.logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape) prog
    (@KoanaKPaths.Machine.Input.readGraph P)
    (NLogN.St.init
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (@NLogN.encI KoanaKPaths.Machine.Input.NS (KoanaKPaths.Machine.Input.parsedState n arcs k a b))
    (KoanaKPaths.Machine.Input.graphReadCost n arcs k a b) := by
  exact @KoanaKPaths.Machine.Input.readGraph_runs

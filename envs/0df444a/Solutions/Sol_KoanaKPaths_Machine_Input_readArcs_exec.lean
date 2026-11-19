-- Prove2me | solution 1 for KoanaKPaths.Machine.Input.readArcs_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:25.857526+00:00
-- url     : https://prove2.me/submissions/12fd5e37-36cb-41ba-a0bb-525e3f9b90d9

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Machine_transferBits_exec
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
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


@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















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

lemma encI_upd (s : IState S) (i : Fin S) (L : List Item) :
    encI (s.upd i L)=(encI s).set (ι i) (encL L) := by
  apply St.ext
  · funext x
    by_cases hx : x.val<S
    · let j : Fin S := ⟨x.val,hx⟩
      have hj : x=ι j := Fin.ext rfl
      rw [hj]
      by_cases he : j=i <;> simp_all [IState.upd]
    · have hxi : x≠ι i := by
        intro h
        have he := congrArg (fun x : Fin (S+4) => x.val) h
        simp only [ι,Fin.val_castAdd] at he
        omega
      simp [encI,hx,set_stk_ne _ hxi]
  · rfl
  · rfl

lemma raw_mark_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P) (s : IState S) (i : Fin S) :
    Exec I prog (.push (ι i) hdMark) (encI s) (encI (s.upd i (.mark::s.G i))) 1 := by
  rw [encI_upd]
  simpa [St.push,St.set,encL,Item.enc] using (Exec.push (I := I) (prog := prog) (encI s) (ι i) hdMark)

lemma raw_unmark_exec (I : List Sym) (prog : Fin P→Stmt (S+4) P) (s : IState S)
    (i : Fin S) (tail : List Item) (hs : s.G i=.mark::tail) :
    Exec I prog (.pop (ι i)) (encI s) (encI (s.upd i tail)) 1 := by
  rw [encI_upd]
  simpa [St.pop,St.set,hs,encL,Item.enc] using (Exec.pop (I := I) (prog := prog) (encI s) (ι i))


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
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input



attribute [local simp] Counter DB
variable {P : ℕ}









lemma readArcs_exec (I : List Sym) (prog : Fin P→Stmt (NS+4) P) (arcs : List (ℕ×ℕ))
    (s : IState NS) (pre post : List Sym)
    (hc : s.G Counter=List.replicate arcs.length .mark)
    (hI : I=pre++arcSymbols arcs++post) (hip : s.ip=pre.length) :
    Exec I prog readArcs (encI s)
      (encI {(s.upd Counter []).upd DB (arcItems arcs ++ s.G DB) with ip := s.ip+(arcSymbols arcs).length})
      (arcCost arcs) := by
  induction arcs generalizing s pre with
  | nil =>
    have hcond : decide ((encI s).top (ι Counter)=some hdMark)=false := by
      simp [St.top,hc,encL]
    have he : {(s.upd Counter []).upd DB (arcItems [] ++ s.G DB) with ip := s.ip+(arcSymbols []).length}=s := by
      apply itemState_ext
      · intro i
        by_cases hi : i=Counter <;> by_cases hd : i=DB <;> simp_all [IState.upd,arcItems,Function.update_apply]
      · simp [arcSymbols]
      · rfl
    rw [he]
    exact Exec.loopF hcond
  | cons p arcs ih =>
    rcases p with ⟨u,v⟩
    let s1 := s.upd Counter (List.replicate arcs.length .mark)
    let s2 := s1.upd DB (.mark::s1.G DB)
    let s3 : IState NS := {s2.upd DB (.int (u : ℤ)::s2.G DB) with
      ip := s2.ip+(HypergraphUnreliability.FPRAS.natCode u).length}
    let s4 : IState NS := {s3.upd DB (.int (v : ℤ)::s3.G DB) with
      ip := s3.ip+(HypergraphUnreliability.FPRAS.natCode v).length}
    let pre1 := pre++(HypergraphUnreliability.FPRAS.natCode u).map codeBit
    let pre2 := pre1++(HypergraphUnreliability.FPRAS.natCode v).map codeBit
    have h1 : Exec I prog (.pop (ι Counter)) (encI s) (encI s1) 1 :=
      raw_unmark_exec I prog s Counter _ (by simpa [List.replicate_succ] using hc)
    have h2 : Exec I prog (.push (ι DB) hdMark) (encI s1) (encI s2) 1 := raw_mark_exec I prog s1 DB
    have h3 : Exec I prog (parseItem DB) (encI s2) (encI s3) (11*u.bits.length+6) :=
      parseItem_exec I prog DB s2 u pre
        ((HypergraphUnreliability.FPRAS.natCode v).map codeBit++arcSymbols arcs++post)
        (by simpa [arcSymbols,List.append_assoc] using hI) (by simpa [s2,s1] using hip)
    have h4 : Exec I prog (parseItem DB) (encI s3) (encI s4) (11*v.bits.length+6) :=
      parseItem_exec I prog DB s3 v pre1 (arcSymbols arcs++post)
        (by simpa [arcSymbols,pre1,List.append_assoc] using hI) (by simp [s3,s2,s1,pre1,hip])
    have htail := ih s4 pre2 (by simp [s4,s3,s2,s1])
      (by simpa [arcSymbols,pre2,pre1,List.append_assoc] using hI)
      (by simp [s4,s3,s2,s1,pre2,pre1,hip,Nat.add_assoc])
    have hcond : decide ((encI s).top (ι Counter)=some hdMark)=true := by
      simp [St.top,hc,List.replicate_succ,encL,Item.enc]
    have hrun := Exec.loopT hcond (Exec.seq h1 (Exec.seq h2 (Exec.seq h3 h4))) htail
    have he : {(s4.upd Counter []).upd DB (arcItems arcs ++ s4.G DB) with
        ip := s4.ip+(arcSymbols arcs).length} =
      {(s.upd Counter []).upd DB (arcItems ((u,v)::arcs) ++ s.G DB) with
        ip := s.ip+(arcSymbols ((u,v)::arcs)).length} := by
      apply itemState_ext
      · intro i
        by_cases hC : i=Counter
        · subst i; simp [IState.upd]
        by_cases hD : i=DB
        · subst i; simp [s4,s3,s2,s1,IState.upd,arcItems,List.append_assoc]
        simp [s4,s3,s2,s1,IState.upd,hC,hD]
      · simp [s4,s3,s2,s1,arcSymbols,List.length_append,List.length_map,Nat.add_assoc]
      · rfl
    rw [he] at hrun
    change Exec I prog readArcs (encI s) _ _ at hrun
    convert hrun using 1 <;> simp only [arcCost] <;> omega

end KoanaKPaths.Machine.Input

end

theorem solution :
∀ {P : Nat} (I : List.{0} NLogN.Sym)
  (prog :
    Fin P →
      NLogN.Stmt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        P)
  (arcs : List.{0} (Prod.{0, 0} Nat Nat)) (s : NLogN.IState KoanaKPaths.Machine.Input.NS)
  (pre post : List.{0} NLogN.Sym)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.Counter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Prod.{0, 0} Nat Nat) arcs) NLogN.Item.mark))
  (hI :
    @Eq.{1} (List.{0} NLogN.Sym) I
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym)) pre
          (KoanaKPaths.Machine.Input.arcSymbols arcs))
        post))
  (hip : @Eq.{1} Nat (@NLogN.IState.ip KoanaKPaths.Machine.Input.NS s) (@List.length.{0} NLogN.Sym pre)),
  @NLogN.Exec
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) KoanaKPaths.Machine.Input.NS
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    P I prog (@KoanaKPaths.Machine.Input.readArcs P) (@NLogN.encI KoanaKPaths.Machine.Input.NS s)
    (@NLogN.encI KoanaKPaths.Machine.Input.NS
      (have __src : NLogN.IState KoanaKPaths.Machine.Input.NS :=
        @NLogN.IState.upd KoanaKPaths.Machine.Input.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.Counter
            (@List.nil.{0} NLogN.Item))
          KoanaKPaths.Machine.Input.DB
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (KoanaKPaths.Machine.Input.arcItems arcs)
            (@NLogN.IState.G KoanaKPaths.Machine.Input.NS s KoanaKPaths.Machine.Input.DB));
      @NLogN.IState.mk KoanaKPaths.Machine.Input.NS (@NLogN.IState.G KoanaKPaths.Machine.Input.NS __src)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@NLogN.IState.ip KoanaKPaths.Machine.Input.NS s)
          (@List.length.{0} NLogN.Sym (KoanaKPaths.Machine.Input.arcSymbols arcs)))
        (@NLogN.IState.out KoanaKPaths.Machine.Input.NS __src)))
    (KoanaKPaths.Machine.Input.arcCost arcs) := by
  exact @KoanaKPaths.Machine.Input.readArcs_exec

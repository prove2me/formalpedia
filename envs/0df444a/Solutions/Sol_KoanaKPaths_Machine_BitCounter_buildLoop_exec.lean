-- Prove2me | solution 1 for KoanaKPaths.Machine.BitCounter.buildLoop_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:26:49.600213+00:00
-- url     : https://prove2.me/submissions/b8dc1677-2d96-4cbb-8fae-fe8b57a5e8cd

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_duplicateMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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





























lemma replicate_cons_same {α : Type} (m : ℕ) (x : α) (L : List α) :
    List.replicate m x ++ x::L = x::(List.replicate m x ++ L) := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons x) ih





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









lemma doubleMarks_exec (I : List Sym) (src tmp : Fin S) (hne : src ≠ tmp)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (doubleMarks src tmp) s
      (s.upd src (List.replicate (2*m) .mark ++ tail)) (97*m+60) := by
  let s1 := (s.upd src tail).upd tmp (List.replicate (2*m) .mark ++ s.G tmp)
  have hdup := duplicateMoveMarks_exec I src tmp hne s m tail ht hs
  have hsrc : s1.G tmp = List.replicate (2*m) .mark ++ [] := by simp [s1,hx]
  have hmov := moveMarks_exec I tmp src (Ne.symm hne) s1 (2*m) [] (by decide) hsrc
  have hrun := IExec.seq hdup hmov
  have he : (s1.upd tmp []).upd src (List.replicate (2*m) .mark ++ s1.G src) =
      s.upd src (List.replicate (2*m) .mark ++ tail) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ht : t=src <;> by_cases hu : t=tmp <;> simp_all [Function.update_apply]
  rw [he] at hrun
  change IExec I Fin.elim0 (doubleMarks src tmp) s _ ((33*m+30)+(32*(2*m)+30)) at hrun
  have hc : (33*m+30)+(32*(2*m)+30) = 97*m+60 := by omega
  simpa only [hc] using hrun










end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.BitCounter







attribute [local simp] Source Ruler Rem Bits Count Tmp









lemma zsz_bitInt (b : Bool) : zsz (bitInt b)=b.toNat := by
  cases b <;> simp [bitInt,zsz,zbits,nbits_eq_bits]

lemma buildLoop_exec (I : List Sym) (s : IState NS) (m : ℕ) (bs : List Bool)
    (bt ct : List Item) (ht : cls ct.head? ≠ Cls.mark)
    (hb : s.G Bits=bs.map (fun b => Item.int (bitInt b)) ++ .mark::bt)
    (hc : s.G Count=List.replicate m .mark ++ ct) (hx : s.G Tmp=[]) :
    IExec I Fin.elim0 buildLoop s
      ((s.upd Bits (.mark::bt)).upd Count (List.replicate (bitValue m bs) .mark ++ ct)) (buildCost m bs) := by
  induction bs generalizing s m with
  | nil =>
    have hcond : decide (s.cl Bits=Cls.zero ∨ s.cl Bits=Cls.pos)=false := by
      simp [IState.cl,hb,cls]
    have hbs : s.upd Bits (.mark::bt)=s := by rw [← show s.G Bits=.mark::bt from by simpa using hb]; exact upd_same _ _
    have hcs : s.upd Count (List.replicate m .mark ++ ct)=s := by rw [← hc]; exact upd_same _ _
    simp only [bitValue,buildCost,hbs,hcs]
    exact IExec.loopF hcond
  | cons b bs ih =>
    let s1 := s.upd Count (List.replicate (2*m) .mark ++ ct)
    let s2 := s.upd Count (List.replicate (2*m+b.toNat) .mark ++ ct)
    let s3 := s2.upd Bits (bs.map (fun b => Item.int (bitInt b)) ++ .mark::bt)
    have h1 : IExec I Fin.elim0 (doubleMarks Count Tmp) s s1 (97*m+60) :=
      doubleMarks_exec I Count Tmp (by decide) s m ct ht hc hx
    have h2 : IExec I Fin.elim0
        (.ite Bits (fun c => decide (c=Cls.pos)) (.op (.mark Count)) .skip) s1 s2 26 := by
      cases b
      · have he : s2=s1 := by simp [s2,s1]
        rw [he]
        exact IExec.iteF (by simp [s1,IState.cl,hb,bitInt,cls]) (.skip s1)
      · have hh : IExec I Fin.elim0 (.op (.mark Count)) s1 s2 1 := by
          simpa only [s1,s2,upd_G_self,upd_upd,Bool.toNat_true,List.replicate_succ,
            replicate_cons_same,List.cons_append] using
            (IExec.op (IOp.Step.mark (s := s1) (i := Count)) : IExec I Fin.elim0 _ _ _ 1)
        exact IExec.iteT (by simp [s1,IState.cl,hb,bitInt,cls]) hh
    have h3 : IExec I Fin.elim0 (.op (.drop Bits)) s2 s3 (2*b.toNat+2) := by
      simpa only [zsz_bitInt] using
        (IExec.op (IOp.Step.drop (I := I) (s := s2) (i := Bits)
          (show s2.G Bits=.int (bitInt b)::(bs.map (fun b => Item.int (bitInt b)) ++ .mark::bt) by
            simp [s2,hb])) : IExec I Fin.elim0 _ _ _ _)
    have hcond : decide (s.cl Bits=Cls.zero ∨ s.cl Bits=Cls.pos)=true := by
      cases b <;> simp [IState.cl,hb,bitInt,cls]
    have htail := ih s3 (2*m+b.toNat) (by simp [s3]) (by simp [s3,s2]) (by simp [s3,s2,hx])
    have hrun := IExec.loopT hcond (IExec.seq h1 (IExec.seq h2 h3)) htail
    have he : (s3.upd Bits (.mark::bt)).upd Count
        (List.replicate (bitValue (2*m+b.toNat) bs) .mark ++ ct) =
      (s.upd Bits (.mark::bt)).upd Count (List.replicate (bitValue m (b::bs)) .mark ++ ct) := by
      cases s
      simp only [s3,s2,IState.upd,bitValue]
      congr 1
      funext i
      by_cases hB : i=Bits <;> by_cases hC : i=Count <;> simp_all
    rw [he] at hrun
    change IExec I Fin.elim0 buildLoop s _ _ at hrun
    convert hrun using 1 <;> simp only [buildCost] <;> omega




















end KoanaKPaths.Machine.BitCounter

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (m : Nat) (bs : List.{0} Bool)
  (bt ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Bool NLogN.Item (fun (b : Bool) => NLogN.Item.int (KoanaKPaths.Machine.BitCounter.bitInt b))
          bs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark bt)))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) ct))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.BitCounter.buildLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Bits
        (@List.cons.{0} NLogN.Item NLogN.Item.mark bt))
      KoanaKPaths.Machine.BitCounter.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (KoanaKPaths.Machine.BitCounter.bitValue m bs) NLogN.Item.mark) ct))
    (KoanaKPaths.Machine.BitCounter.buildCost m bs) := by
  exact @KoanaKPaths.Machine.BitCounter.buildLoop_exec

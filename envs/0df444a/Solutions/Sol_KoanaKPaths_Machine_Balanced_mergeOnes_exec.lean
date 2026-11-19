-- Prove2me | solution 1 for KoanaKPaths.Machine.Balanced.mergeOnes_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.025929+00:00
-- url     : https://prove2.me/submissions/8957474a-c0f1-4cd1-abf7-aaded843a1e6

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
import Mathlib.Data.Nat.Size
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

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Balanced






attribute [local simp] Partials Bits Carry Restore Sum





lemma mergeOnes_exec (I : List Sym) (s : IState NS) (x : ℤ) (ys : List ℤ)
    (bt pt ct : List Item) (hbt : cls bt.head? ≠ Cls.pos)
    (hb : s.G Bits=List.replicate ys.length (.int 1) ++ bt)
    (hp : s.G Partials=ys.map Item.int ++ pt) (hc : s.G Carry=.int x::ct) :
    IExec I Fin.elim0 mergeOnes s
      ((((s.upd Bits bt).upd Partials pt).upd Carry (.int (x+ys.sum)::ct)).upd Restore
        (List.replicate ys.length .mark ++ s.G Restore)) (mergeCost x ys) := by
  induction ys generalizing s x with
  | nil =>
    have hcond : decide (s.cl Bits=Cls.pos)=false := by simp [IState.cl,hb,hbt]
    have he : ((((s.upd Bits bt).upd Partials pt).upd Carry (.int (x+([] : List ℤ).sum)::ct)).upd Restore
        (List.replicate ([] : List ℤ).length .mark ++ s.G Restore))=s := by
      apply itemState_ext
      · intro i
        by_cases hB : i=Bits <;> by_cases hP : i=Partials <;> by_cases hC : i=Carry <;> by_cases hR : i=Restore <;>
          simp_all [IState.upd,Function.update_apply]
      · rfl
      · rfl
    rw [he]
    exact IExec.loopF hcond
  | cons y ys ih =>
    let s1 := s.upd Bits (List.replicate ys.length (.int 1) ++ bt)
    let s2 := s1.upd Restore (.mark::s1.G Restore)
    let sa := (s2.upd Carry ct).upd Partials (ys.map Item.int ++ pt)
    let s3 := sa.upd Carry (.int (x+y)::sa.G Carry)
    have h1 : IExec I Fin.elim0 (.op (.drop Bits)) s s1 4 := by
      have hh := IExec.op (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.drop (I := I) (s := s) (i := Bits) (a := 1)
          (by simpa [List.replicate_succ] using hb))
      simpa [Wedge.zsz_eq_size] using hh
    have h2 : IExec I Fin.elim0 (.op (.mark Restore)) s1 s2 1 := .op (.mark)
    have h3 : IExec I Fin.elim0 (.op (.add Carry Partials Carry)) s2 s3 (addIntCost (zsz x+zsz y)) := by
      exact .op (.add (by decide) (by simp [s2,s1,hc]) (by simp [s2,s1,hp]))
    have htail := ih s3 (x+y) (by simp [s3,sa,s2,s1]) (by simp [s3,sa]) (by simp [s3,sa])
    have hcond : decide (s.cl Bits=Cls.pos)=true := by simp [IState.cl,hb,List.replicate_succ,cls]
    have hrun := IExec.loopT hcond (IExec.seq h1 (IExec.seq h2 h3)) htail
    have he : ((((s3.upd Bits bt).upd Partials pt).upd Carry (.int (x+y+ys.sum)::ct)).upd Restore
        (List.replicate ys.length .mark ++ s3.G Restore)) =
      ((((s.upd Bits bt).upd Partials pt).upd Carry (.int (x+(y::ys).sum)::ct)).upd Restore
        (List.replicate (y::ys).length .mark ++ s.G Restore)) := by
      apply itemState_ext
      · intro i
        by_cases hB : i=Bits
        · subst i; simp [s3,sa,s2,s1]
        by_cases hP : i=Partials
        · subst i; simp [s3,sa,s2,s1]
        by_cases hC : i=Carry
        · subst i; simp [s3,sa,s2,s1,List.sum_cons,add_assoc]
        by_cases hR : i=Restore
        · subst i; simp [s3,sa,s2,s1,List.replicate_succ,replicate_cons_same]
        simp [s3,sa,s2,s1,IState.upd,Function.update_apply,hB,hP,hC,hR]
      · rfl
      · rfl
    have hct : sa.G Carry=ct := by simp [sa]
    rw [he] at hrun
    change IExec I Fin.elim0 mergeOnes s _ _ at hrun
    convert hrun using 1
    simp only [mergeCost]
    omega











end KoanaKPaths.Machine.Balanced

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int) (ys : List.{0} Int)
  (bt pt ct : List.{0} NLogN.Item) (hbt : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item bt)) NLogN.Cls.pos)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
          (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        bt))
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) pt))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Carry)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) ct)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.mergeOnes s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits bt)
          KoanaKPaths.Machine.Balanced.Partials pt)
        KoanaKPaths.Machine.Balanced.Carry
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
              (@List.sum.{0} Int Int.instAdd
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) ys)))
          ct))
      KoanaKPaths.Machine.Balanced.Restore
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Restore)))
    (KoanaKPaths.Machine.Balanced.mergeCost x ys) := by
  exact @KoanaKPaths.Machine.Balanced.mergeOnes_exec

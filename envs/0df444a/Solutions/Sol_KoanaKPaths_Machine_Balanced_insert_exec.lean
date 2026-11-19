-- Prove2me | solution 1 for KoanaKPaths.Machine.Balanced.insert_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.537286+00:00
-- url     : https://prove2.me/submissions/ebba37c2-0926-486a-91cd-736cce1873c5

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
import Theorems.Thm_KoanaKPaths_Machine_Balanced_mergeOnes_exec
import Theorems.Thm_KoanaKPaths_Machine_repeatInts_exec
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















lemma insert_exec (I : List Sym) (s : IState NS) (x : ℤ) (ys : List ℤ)
    (zero : Bool) (bt pt ct : List Item)
    (hb : s.G Bits=List.replicate ys.length (.int 1) ++ stopBits zero bt)
    (hp : s.G Partials=ys.map Item.int ++ pt) (hc : s.G Carry=.int x::ct)
    (hr : s.G Restore=[]) :
    IExec I Fin.elim0 insert s
      (((s.upd Bits (List.replicate ys.length (.int 0) ++
          .int 1::nextBits zero bt)).upd Partials (.int (x+ys.sum)::pt)).upd Carry ct)
      (insertCost x ys zero) := by
  let s1 := (((s.upd Bits (stopBits zero bt)).upd Partials pt).upd Carry
    (.int (x+ys.sum)::ct)).upd Restore (List.replicate ys.length .mark)
  let s2 := s1.upd Bits (nextBits zero bt)
  let s3 := s2.upd Bits (.int 1::s2.G Bits)
  let s4 := (s3.upd Restore []).upd Bits (List.replicate ys.length (.int 0) ++ s3.G Bits)
  let sa := s4.upd Carry ct
  let s5 := sa.upd Partials (.int (x+ys.sum)::sa.G Partials)
  have h1 : IExec I Fin.elim0 mergeOnes s s1 (mergeCost x ys) := by
    simpa only [hr,List.append_nil] using
      mergeOnes_exec I s x ys (stopBits zero bt) pt ct
        (by cases zero <;> simp [stopBits,cls]) hb hp hc
  have h2 : IExec I Fin.elim0
      (.ite Bits (fun c => decide (c=Cls.zero)) (.op (.drop Bits)) .skip)
      s1 s2 (if zero then 27 else 26) := by
    cases zero
    · have he : s2=s1 := by
        have hg : s1.G Bits=nextBits false bt := by simp [s1,stopBits,nextBits]
        dsimp [s2]; rw [← hg]; exact upd_same _ _
      rw [he]
      exact .iteF (by simp [IState.cl,s1,stopBits,cls]) (.skip s1)
    · have hh : IExec I Fin.elim0 (.op (.drop Bits)) s1 s2 2 := by
        have h := IExec.op (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
          (IOp.Step.drop (I := I) (s := s1) (i := Bits) (a := 0) (L := bt)
            (by simp [s1,stopBits]))
        simpa [s2,nextBits,Wedge.zsz_eq_size] using h
      exact .iteT (by simp [IState.cl,s1,stopBits,cls]) hh
  have h3 : IExec I Fin.elim0 (.op (.const Bits 1)) s2 s3 3 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.const (s := s2) (i := Bits) 1))
  have h4 : IExec I Fin.elim0 (repeatInts Restore Bits 0) s3 s4 (33*ys.length+30) := by
    simpa [s4,Wedge.zsz_eq_size] using
      repeatInts_exec I Restore Bits (by decide) 0 s3 ys.length [] (by simp [cls])
        (by simp [s3,s2,s1])
  have h5 : IExec I Fin.elim0 (.op (.mv Carry Partials)) s4 s5
      (2*moveCost (zsz (x+ys.sum))+19) := by
    exact .op (.mv (by decide) (by simp [s4,s3,s2,s1]))
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 h5)))
  have he : s5=(((s.upd Bits (List.replicate ys.length (.int 0) ++
      .int 1::nextBits zero bt)).upd Partials (.int (x+ys.sum)::pt)).upd Carry ct) := by
    apply itemState_ext
    · intro i
      by_cases hB : i=Bits
      · subst i; simp [s5,sa,s4,s3,s2,s1]
      by_cases hP : i=Partials
      · subst i; simp [s5,sa,s4,s3,s2,s1]
      by_cases hC : i=Carry
      · subst i; simp [s5,sa,s4,s3,s2,s1]
      by_cases hR : i=Restore
      · subst i; simp [s5,sa,s4,s3,s2,s1,hr]
      simp [s5,sa,s4,s3,s2,s1,IState.upd,Function.update_apply,hB,hP,hC,hR]
    · rfl
    · rfl
  rw [he] at hrun
  change IExec I Fin.elim0 insert s _ _ at hrun
  convert hrun using 1 <;> simp only [insertCost] <;> omega

end KoanaKPaths.Machine.Balanced

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int) (ys : List.{0} Int)
  (zero : Bool) (bt pt ct : List.{0} NLogN.Item)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
          (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (KoanaKPaths.Machine.Balanced.stopBits zero bt)))
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) pt))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Carry)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) ct))
  (hr :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.insert s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
              (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (KoanaKPaths.Machine.Balanced.nextBits zero bt))))
        KoanaKPaths.Machine.Balanced.Partials
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
              (@List.sum.{0} Int Int.instAdd
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) ys)))
          pt))
      KoanaKPaths.Machine.Balanced.Carry ct)
    (KoanaKPaths.Machine.Balanced.insertCost x ys zero) := by
  exact @KoanaKPaths.Machine.Balanced.insert_exec

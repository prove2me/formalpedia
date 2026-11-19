-- Prove2me | solution 1 for KoanaKPaths.Machine.compareLE_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.488149+00:00
-- url     : https://prove2.me/submissions/a1b55486-5467-4e47-9efe-d726c795312d

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
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma compareLE_exec (I : List Sym) (i j tmp work dst : Fin S)
    (hij : i≠j) (hit : i≠tmp) (hiw : i≠work) (hid : i≠dst)
    (hjt : j≠tmp) (hjw : j≠work) (hjd : j≠dst)
    (htw : tmp≠work) (htd : tmp≠dst) (hwd : work≠dst)
    (s : IState S) (x y : ℤ) (li lj : List Item)
    (hx : s.G i=.int x::li) (hy : s.G j=.int y::lj) :
    IExec I Fin.elim0 (compareLE i j tmp work dst) s
      (s.upd dst (if x≤ y then .mark::s.G dst else s.G dst)) (compareCost x y) := by
  let s1 := s.upd tmp (.int x::s.G tmp)
  let s2 := s1.upd work (.int y::s1.G work)
  let s3 := s2.upd work (.int (-y)::s.G work)
  let sa := (s3.upd tmp (s.G tmp)).upd work (s.G work)
  let s4 := sa.upd tmp (.int (x-y)::sa.G tmp)
  let s5 := s4.upd dst (if x≤ y then .mark::s.G dst else s.G dst)
  let s6 := s5.upd tmp (s.G tmp)
  have h1 : IExec I Fin.elim0 (.op (.dup i tmp)) s s1 (dupCost (zsz x)+17) := .op (.dup hit hx)
  have h2 : IExec I Fin.elim0 (.op (.dup j work)) s1 s2 (dupCost (zsz y)+17) := by
    exact .op (IOp.Step.dup (L := lj) hjw (by simp [s1,hjt,hy]))
  have h3 : IExec I Fin.elim0 (.op (.neg work)) s2 s3 20 := by
    have hh := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt S 0))
      (IOp.Step.neg (s := s2) (i := work) (a := y) (L := s.G work)
        (by simp [s2,s1,Ne.symm htw]))
    simpa [s3] using hh
  have h4 : IExec I Fin.elim0 (.op (.add tmp work tmp)) s3 s4
      (addIntCost (zsz x+zsz (-y))) := by
    have hh := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt S 0))
      (IOp.Step.add (s := s3) (i := tmp) (j := work) (k := tmp) (a := x) (b := -y)
        (Li := s.G tmp) (Lj := s.G work) htw
        (by simp [s3,s2,s1,htw]) (by simp [s3]))
    simpa [s4,sa,sub_eq_add_neg] using hh
  have h5 : IExec I Fin.elim0
      (.ite tmp (fun c => decide (c=Cls.pos)) .skip (.op (.mark dst))) s4 s5 26 := by
    by_cases hxy : x≤ y
    · have hcl : decide (s4.cl tmp=Cls.pos)=false := by
        rcases lt_or_eq_of_le hxy with hh|hh
        · simp [IState.cl,s4,cls,show x-y≠0 by omega,hh]
        · subst y; simp [IState.cl,s4,cls]
      apply IExec.iteF hcl
      have hh : IExec I Fin.elim0 (.op (.mark dst)) s4 (s4.upd dst (.mark::s4.G dst)) 1 := .op (.mark)
      simpa [s5,hxy,s4,sa,s3,s2,s1,Ne.symm htd,Ne.symm hwd] using hh
    · have hcl : decide (s4.cl tmp=Cls.pos)=true := by
        have hh : 0< x-y := by omega
        simp [IState.cl,s4,cls,hh.ne',show ¬x< y by omega,show ¬x-y<0 by omega]
      have he : s5=s4 := by
        have hg : s4.G dst=s.G dst := by simp [s4,sa,s3,s2,s1,Ne.symm htd,Ne.symm hwd]
        dsimp [s5]; rw [if_neg hxy,← hg]; exact upd_same _ _
      rw [he]
      exact .iteT hcl (.skip s4)
  have h6 : IExec I Fin.elim0 (.op (.drop tmp)) s5 s6 (2*zsz (x-y)+2) := by
    exact .op (.drop (by simp [s5,s4,sa,s3,htd,htw]))
  have he : s6=s.upd dst (if x≤ y then .mark::s.G dst else s.G dst) := by
    apply itemState_ext
    · intro r
      by_cases hD : r=dst
      · subst r; simp [s6,s5,s4,sa,s3,s2,s1,Ne.symm htd]
      by_cases hT : r=tmp
      · subst r; simp [s6,s5,s4,sa,s3,s2,s1,htd]
      by_cases hW : r=work
      · subst r; simp [s6,s5,s4,sa,s3,s2,s1,Ne.symm htw,hwd]
      simp [s6,s5,s4,sa,s3,s2,s1,IState.upd,Function.update_apply,hD,hT,hW]
    · rfl
    · rfl
  have hh := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 h6))))
  rw [he] at hh
  change IExec I Fin.elim0 (compareLE i j tmp work dst) s _ _ at hh
  convert hh using 1 <;> simp only [compareCost] <;> omega



end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (i j tmp work dst : Fin S) (hij : @Ne.{1} (Fin S) i j)
  (hit : @Ne.{1} (Fin S) i tmp) (hiw : @Ne.{1} (Fin S) i work) (hid : @Ne.{1} (Fin S) i dst)
  (hjt : @Ne.{1} (Fin S) j tmp) (hjw : @Ne.{1} (Fin S) j work) (hjd : @Ne.{1} (Fin S) j dst)
  (htw : @Ne.{1} (Fin S) tmp work) (htd : @Ne.{1} (Fin S) tmp dst) (hwd : @Ne.{1} (Fin S) work dst) (s : NLogN.IState S)
  (x y : Int) (li lj : List.{0} NLogN.Item)
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s i) (@List.cons.{0} NLogN.Item (NLogN.Item.int x) li))
  (hy : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s j) (@List.cons.{0} NLogN.Item (NLogN.Item.int y) lj)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.compareLE S i j tmp work dst) s
    (@NLogN.IState.upd S s dst
      (@ite.{1} (List.{0} NLogN.Item) (@LE.le.{0} Int Int.instLEInt x y) (Int.decLe x y)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark (@NLogN.IState.G S s dst)) (@NLogN.IState.G S s dst)))
    (KoanaKPaths.Machine.compareCost x y) := by
  exact @KoanaKPaths.Machine.compareLE_exec

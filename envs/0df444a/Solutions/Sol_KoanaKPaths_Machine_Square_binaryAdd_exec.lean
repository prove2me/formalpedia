-- Prove2me | solution 1 for KoanaKPaths.Machine.Square.binaryAdd_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.100971+00:00
-- url     : https://prove2.me/submissions/df7626e7-8186-4450-8262-7dd5f634e73b

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
import Theorems.Thm_NLogN_smul_runs
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
namespace KoanaKPaths.Machine.Square

attribute [local simp] Eval Value Arg X Y W Q R T




lemma binaryAdd_exec (I : List Sym) (s : IState NS) (x y : ℤ) (tail : List Item)
    (hs : s.G Eval=.int y::.int x::tail) :
    IExec I Fin.elim0 binaryAdd s (s.upd Eval (.int (x+y)::tail))
      (2*moveCost (zsz y)+19+addIntCost (zsz x+zsz y)) := by
  let s1 := (s.upd Eval (.int x::tail)).upd Arg (.int y::s.G Arg)
  let sa := (s1.upd Eval tail).upd Arg (s.G Arg)
  let s2 := sa.upd Eval (.int (x+y)::tail)
  have h1 : IExec I Fin.elim0 (.op (.mv Eval Arg)) s s1 (2*moveCost (zsz y)+19) :=
    .op (.mv (by decide) hs)
  have h2 : IExec I Fin.elim0 (.op (.add Eval Arg Eval)) s1 s2 (addIntCost (zsz x+zsz y)) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s1) (i := Eval) (j := Arg) (k := Eval) (a := x) (b := y)
        (Li := tail) (Lj := s.G Arg) (by decide) (by simp [s1]) (by simp [s1]))
    simpa [s2,sa] using h
  have he : s2=s.upd Eval (.int (x+y)::tail) := by
    apply itemState_ext
    · intro i
      by_cases hE : i=Eval
      · subst i; simp [s2,sa,s1]
      by_cases hA : i=Arg
      · subst i; simp [s2,sa,s1]
      simp [s2,sa,s1,IState.upd,Function.update_apply,hE,hA]
    · rfl
    · rfl
  have h := IExec.seq h1 h2
  rw [he] at h
  exact h





end KoanaKPaths.Machine.Square

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (x y : Int) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int y) (@List.cons.{0} NLogN.Item (NLogN.Item.int x) tail))),
  @NLogN.IExec KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Square.binaryAdd s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y))
        tail))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (NLogN.moveCost (NLogN.zsz y)))
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      (NLogN.addIntCost (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (NLogN.zsz x) (NLogN.zsz y)))) := by
  exact @KoanaKPaths.Machine.Square.binaryAdd_exec

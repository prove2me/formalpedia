-- Prove2me | solution 1 for KoanaKPaths.Machine.Balanced.foldPartials_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:37:10.067141+00:00
-- url     : https://prove2.me/submissions/db4e9549-c503-4e66-8045-490f395b59b8

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
namespace KoanaKPaths.Machine.Balanced
attribute [local simp] Partials Bits Carry Restore Sum





lemma foldPartials_exec (I : List Sym) (s : IState NS) (x : ℤ) (cs : List Chunk)
    (pt st : List Item) (ht : cls pt.head?=Cls.mark)
    (hp : s.G Partials=(cs.map Prod.snd).map Item.int ++ pt)
    (hx : s.G Sum=.int x::st) :
    IExec I Fin.elim0 foldPartials s
      ((s.upd Partials pt).upd Sum (.int (x+(cs.map Prod.snd).sum)::st))
      (foldCharge x cs) := by
  induction cs generalizing s x with
  | nil =>
    have hcond : decide (s.cl Partials=Cls.zero ∨ s.cl Partials=Cls.pos ∨ s.cl Partials=Cls.neg)=false := by
      simp [IState.cl,hp,ht]
    have he : (s.upd Partials pt).upd Sum (.int (x+(([] : List Chunk).map Prod.snd).sum)::st)=s := by
      apply itemState_ext
      · intro i
        by_cases hP : i=Partials <;> by_cases hS : i=Sum <;>
          simp_all [IState.upd,Function.update_apply]
      · rfl
      · rfl
    simp only [List.map_nil,List.sum_nil,add_zero] at he
    simp only [List.map_nil,List.sum_nil,add_zero,foldCharge]
    rw [he]
    exact .loopF hcond
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    let sa := (s.upd Sum st).upd Partials ((cs.map Prod.snd).map Item.int ++ pt)
    let s1 := sa.upd Sum (.int (x+y)::sa.G Sum)
    have h1 : IExec I Fin.elim0 (.op (.add Sum Partials Sum)) s s1
        (addIntCost (zsz x+zsz y)) :=
      .op (.add (by decide) hx (by simpa using hp))
    have hcond : decide (s.cl Partials=Cls.zero ∨ s.cl Partials=Cls.pos ∨ s.cl Partials=Cls.neg)=true := by
      simp only [IState.cl,hp,List.map_cons,List.cons_append,List.head?_cons]
      rcases lt_trichotomy y 0 with hn|hz|hpos
      · simp [cls,hn,hn.ne,not_le.mpr hn]
      · subst y; simp [cls]
      · simp [cls,hpos.ne',not_lt.mpr hpos.le]
    have ht := ih s1 (x+y) (by simp [s1,sa]) (by simp [s1,sa])
    have hh := IExec.loopT hcond h1 ht
    have he : (s1.upd Partials pt).upd Sum (.int (x+y+(cs.map Prod.snd).sum)::st)=
        (s.upd Partials pt).upd Sum (.int (x+(((j,y)::cs).map Prod.snd).sum)::st) := by
      apply itemState_ext
      · intro i
        by_cases hP : i=Partials <;> by_cases hS : i=Sum <;>
          simp_all [s1,sa,IState.upd,Function.update_apply,List.sum_cons,add_assoc]
      · rfl
      · rfl
    rw [he] at hh
    change IExec I Fin.elim0 foldPartials s _ _ at hh
    convert hh using 1 <;> simp only [foldCharge] <;> omega

end KoanaKPaths.Machine.Balanced

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int)
  (cs : List.{0} KoanaKPaths.Machine.Balanced.Chunk) (pt st : List.{0} NLogN.Item)
  (ht : @Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item pt)) NLogN.Cls.mark)
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))
        pt))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Sum)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) st)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.foldPartials s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials pt)
      KoanaKPaths.Machine.Balanced.Sum
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
            (@List.sum.{0} Int Int.instAdd
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
              (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))))
        st))
    (KoanaKPaths.Machine.Balanced.foldCharge x cs) := by
  exact @KoanaKPaths.Machine.Balanced.foldPartials_exec

-- Prove2me | solution 1 for KoanaKPaths.Machine.zipAddInts_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:39:40.884824+00:00
-- url     : https://prove2.me/submissions/fc72164b-8ebd-4165-88a3-29abf12240dd

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
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






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]




















lemma zipAddInts_exec (I : List Sym) (src dst out : Fin S)
    (hsd : src ≠ dst) (hso : src ≠ out) (hdo : dst ≠ out)
    (s : IState S) (xs ys : List ℤ) (tail tail' : List Item)
    (ht : ¬ (cls tail.head? = Cls.zero ∨ cls tail.head? = Cls.pos ∨ cls tail.head? = Cls.neg))
    (hlen : xs.length=ys.length)
    (hs : s.G src = xs.map Item.int ++ tail) (hd : s.G dst = ys.map Item.int ++ tail') :
    IExec I Fin.elim0 (zipAddInts src dst out) s
      (((s.upd src tail).upd dst tail').upd out
        ((List.zipWith (·+·) xs ys).reverse.map Item.int ++ s.G out))
      (zipAddIntsCost xs ys) := by
  induction xs generalizing s ys with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst ys
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = false := by
      simpa [IState.cl,hs] using ht
    have hsrc : s.upd src tail = s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    have hdst : s.upd dst tail' = s := by rw [← show s.G dst=tail' from by simpa using hd]; exact upd_same _ _
    simp only [List.zipWith_nil_left,List.reverse_nil,List.map_nil,List.nil_append,hsrc,hdst,
      upd_same,zipAddIntsCost,List.sum_nil,zero_add]
    exact IExec.loopF hh
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      let s1 := ((s.upd src (xs.map Item.int ++ tail)).upd dst (ys.map Item.int ++ tail')).upd out
        (.int (x+y)::s.G out)
      have hbody : IExec I Fin.elim0 (.op (.add src dst out)) s s1
          (addIntCost (zsz x+zsz y)) := by
        have hh : IExec I Fin.elim0 (.op (.add src dst out)) s _ (addIntCost (zsz x+zsz y)) :=
          IExec.op (IOp.Step.add (I := I) (k := out) hsd (by simpa using hs) (by simpa using hd))
        simpa only [upd_G_ne _ (Ne.symm hso),upd_G_ne _ (Ne.symm hdo)] using hh
      have hs1 : s1.G src = xs.map Item.int ++ tail := by simp [s1,hsd,hso]
      have hd1 : s1.G dst = ys.map Item.int ++ tail' := by simp [s1,hdo]
      have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = true := by
        simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
        exact cls_int x
      have hrun := IExec.loopT hh hbody (ih s1 ys (by simpa using hlen) hs1 hd1)
      have he : (((s1.upd src tail).upd dst tail').upd out
          ((List.zipWith (·+·) xs ys).reverse.map Item.int ++ s1.G out)) =
        (((s.upd src tail).upd dst tail').upd out
          ((List.zipWith (·+·) (x::xs) (y::ys)).reverse.map Item.int ++ s.G out)) := by
        cases s
        simp only [s1,IState.upd]
        congr 1
        funext t
        by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=out <;>
          simp_all [List.reverse_cons,List.map_append,List.append_assoc]
      rw [he] at hrun
      change IExec I Fin.elim0 (zipAddInts src dst out) s _ _ at hrun
      convert hrun using 1
      simp [zipAddIntsCost]
      omega















end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst out : Fin S) (hsd : @Ne.{1} (Fin S) src dst)
  (hso : @Ne.{1} (Fin S) src out) (hdo : @Ne.{1} (Fin S) dst out) (s : NLogN.IState S) (xs ys : List.{0} Int)
  (tail tail' : List.{0} NLogN.Item)
  (ht :
    Not
      (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.zero)
        (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.pos)
          (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.neg))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int ys))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s dst)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) tail')),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.zipAddInts S src dst out) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst tail') out
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (@List.zipWith.{0, 0, 0} Int Int Int
              (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2) xs ys)))
        (@NLogN.IState.G S s out)))
    (KoanaKPaths.Machine.zipAddIntsCost xs ys) := by
  exact @KoanaKPaths.Machine.zipAddInts_exec

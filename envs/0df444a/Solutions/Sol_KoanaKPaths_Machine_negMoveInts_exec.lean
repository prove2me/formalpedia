-- Prove2me | solution 1 for KoanaKPaths.Machine.negMoveInts_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:37:10.026718+00:00
-- url     : https://prove2.me/submissions/b6074d04-f3d9-4bfa-b258-f0e08609f593

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
variable {S : ℕ}





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]
































lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]

lemma negMoveInts_exec (I : List Sym) (src dst : Fin S) (hne : src ≠ dst)
    (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head? = Cls.zero ∨ cls tail.head? = Cls.pos ∨ cls tail.head? = Cls.neg))
    (hs : s.G src = xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (negMoveInts src dst) s
      ((s.upd src tail).upd dst (xs.reverse.map (fun z => Item.int (-z)) ++ s.G dst))
      (moveIntsCost xs+20*xs.length) := by
  induction xs generalizing s with
  | nil =>
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = false := by
      simpa [IState.cl,hs] using ht
    have hsrc : s.upd src tail = s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    simp only [List.reverse_nil,List.map_nil,List.nil_append,hsrc,upd_same,moveIntsCost,List.sum_nil,
      List.length_nil,mul_zero,zero_add,Nat.add_zero]
    exact IExec.loopF hh
  | cons z xs ih =>
    let s0 := s.upd src (.int (-z)::(xs.map Item.int ++ tail))
    let s1 := (s.upd src (xs.map Item.int ++ tail)).upd dst (.int (-z)::s.G dst)
    have hn : IExec I Fin.elim0 (.op (.neg src)) s s0 20 := by
      exact IExec.op (IOp.Step.neg (by simpa using hs))
    have hm : IExec I Fin.elim0 (.op (.mv src dst)) s0 s1 (2*moveCost (zsz z)+19) := by
      have hh := IExec.op (iprog := (Fin.elim0 : Fin 0 → IStmt S 0))
        (IOp.Step.mv (I := I) hne (show s0.G src = .int (-z)::(xs.map Item.int ++ tail) by simp [s0]))
      simpa only [s0,upd_G_ne s (Ne.symm hne),upd_upd,zsz_neg] using hh
    have hs1 : s1.G src = xs.map Item.int ++ tail := by simp [s1,hne]
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = true := by
      simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
      exact cls_int z
    have hrun := IExec.loopT hh (IExec.seq hn hm) (ih s1 hs1)
    have he : (s1.upd src tail).upd dst (xs.reverse.map (fun z => Item.int (-z)) ++ s1.G dst) =
      (s.upd src tail).upd dst ((z::xs).reverse.map (fun z => Item.int (-z)) ++ s.G dst) := by
      cases s
      simp only [s1,IState.upd]
      congr 1
      funext t
      by_cases ha : t=src <;> by_cases hb : t=dst <;>
        simp_all [List.reverse_cons,List.map_append,List.append_assoc]
    rw [he] at hrun
    change IExec I Fin.elim0 (negMoveInts src dst) s _ _ at hrun
    convert hrun using 1
    simp [moveIntsCost]
    omega

end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst) (s : NLogN.IState S)
  (xs : List.{0} Int) (tail : List.{0} NLogN.Item)
  (ht :
    Not
      (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.zero)
        (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.pos)
          (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.neg))))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.negMoveInts S src dst) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item (fun (z : Int) => NLogN.Item.int (@Neg.neg.{0} Int Int.instNegInt z))
          (@List.reverse.{0} Int xs))
        (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (KoanaKPaths.Machine.moveIntsCost xs)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) (@List.length.{0} Int xs))) := by
  exact @KoanaKPaths.Machine.negMoveInts_exec

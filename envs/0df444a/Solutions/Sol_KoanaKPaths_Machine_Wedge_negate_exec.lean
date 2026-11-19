-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.negate_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.052187+00:00
-- url     : https://prove2.me/submissions/e9ad459c-9fb4-47fa-bf08-9e73eaec53b9

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
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_negMoveInts_exec
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






































lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]



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
namespace KoanaKPaths.Machine.Wedge






lemma moveIntsCost_neg_reverse (xs : List ℤ) :
    moveIntsCost (xs.reverse.map (fun z => -z))=moveIntsCost xs := by
  simp [moveIntsCost,List.map_map,Function.comp_def,zsz_neg,List.map_reverse]

lemma negate_exec (I : List Sym) (src : Fin NS) (hne : src ≠ Z)
    (s : IState NS) (xs : List ℤ) (tail : List Item)
    (hs : s.G src = xs.map Item.int ++ .mark::tail) :
    IExec I prog (negate src) s
      (s.upd src (xs.map (fun z => Item.int (-z)) ++ .mark::tail))
      (2*moveIntsCost xs+20*xs.length+3) := by
  let s1 := s.upd Z (.mark::s.G Z)
  let s2 := (s1.upd src (.mark::tail)).upd Z
    (xs.reverse.map (fun z => Item.int (-z)) ++ .mark::s.G Z)
  let s3 := (s2.upd Z (.mark::s.G Z)).upd src
    (xs.map (fun z => Item.int (-z)) ++ .mark::tail)
  let s4 := s.upd src (xs.map (fun z => Item.int (-z)) ++ .mark::tail)
  have h1 : IExec I prog (.op (.mark Z)) s s1 1 := .op (.mark)
  have hn := negMoveInts_exec I src Z hne s1 xs (.mark::tail) (by simp [cls])
    (by simp [s1,hne,hs])
  have h2 : IExec I prog (liftClosed (negMoveInts src Z)) s1 s2
      (moveIntsCost xs+20*xs.length) := by
    exact liftClosed_exec I prog hn
  have hm := moveInts_exec I Z src (Ne.symm hne) s2 (xs.reverse.map (fun z => -z))
    (.mark::s.G Z) (by simp [cls]) (by simp [s2,List.map_map,Function.comp_def])
  have he : (s2.upd Z (.mark::s.G Z)).upd src
      ((xs.reverse.map (fun z => -z)).reverse.map Item.int ++ s2.G src) = s3 := by
    simp [s3,s2,hne,List.map_reverse,List.map_map,Function.comp_def]
  rw [he,moveIntsCost_neg_reverse] at hm
  have h3 : IExec I prog (move Z src) s2 s3 (moveIntsCost xs) := liftClosed_exec I prog hm
  have h4 : IExec I prog (.op (.unmark Z)) s3 s4 1 := by
    have hh := IExec.op (iprog := prog)
      (IOp.Step.unmark (I := I) (s := s3) (i := Z) (show s3.G Z = .mark::s.G Z by simp [s3,Ne.symm hne]))
    have he' : s3.upd Z (s.G Z) = s4 := by
      cases s
      simp only [s4,s3,s2,s1,IState.upd]
      congr 1
      funext t
      by_cases ha : t=src <;> by_cases hb : t=Z <;> simp_all
    simpa only [he'] using hh
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.skip s4))))
  change IExec I prog (negate src) s _ _ at hrun
  convert hrun using 1 <;> omega








end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (src : Fin KoanaKPaths.Machine.Wedge.NS)
  (hne : @Ne.{1} (Fin KoanaKPaths.Machine.Wedge.NS) src KoanaKPaths.Machine.Wedge.Z)
  (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (xs : List.{0} Int) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog (KoanaKPaths.Machine.Wedge.negate src) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS s src
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item (fun (z : Int) => NLogN.Item.int (@Neg.neg.{0} Int Int.instNegInt z)) xs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tail)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (KoanaKPaths.Machine.moveIntsCost xs))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) (@List.length.{0} Int xs)))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @KoanaKPaths.Machine.Wedge.negate_exec

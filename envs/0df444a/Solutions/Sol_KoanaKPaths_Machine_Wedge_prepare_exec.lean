-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.prepare_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:20.425132+00:00
-- url     : https://prove2.me/submissions/96660af1-6ace-41f1-9264-12e1d35e002c

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
import Theorems.Thm_KoanaKPaths_Machine_duplicateTakeInts_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_powerMarks_exec
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

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z





lemma prepare_exec (I : List Sym) (s : IState NS) (d : ℕ) (z : ℤ)
    (vs xs ys : List ℤ) (ta td tv : List Item)
    (hx : xs.length=2^d) (hy : ys.length=2^d) (ht : cls td.head? ≠ Cls.mark)
    (ha : s.G A = (xs++ys).map Item.int ++ .mark::ta)
    (hd : s.G D = List.replicate (d+1) .mark ++ td)
    (hv : s.G V = .int z::(vs.map Item.int ++ tv))
    (hHC : s.G HC=[]) (hDC : s.G DC=[]) (hAux : s.G Aux=[]) :
    IExec I prog prepare s (prepared s d z vs xs ys ta td tv) (prepareCost d z xs ys) := by
  let s1 := s.upd D (List.replicate d .mark ++ td)
  have h1 : IExec I prog (.op (.unmark D)) s s1 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s2 := (s1.upd V (vs.map Item.int ++ tv)).upd VS (.int (z)::s1.G VS)
  have h2 : IExec I prog (.op (.mv V VS)) s1 s2 (2*moveCost (zsz z)+19) := by
    exact IExec.op (IOp.Step.mv (by decide) (by simp [s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s3 := s2.upd C0 (.mark::s2.G C0)
  have h3 : IExec I prog (.op (.mark C0)) s2 s3 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s4 := s3.upd H0 (.mark::s3.G H0)
  have h4 : IExec I prog (.op (.mark H0)) s3 s4 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s5 := s4.upd HC (List.replicate (2^d) .mark)
  have h5 : IExec I prog (liftClosed (powerMarks D HC DC Aux)) s4 s5 (1+(65*d+60)+growMarksCost 1 d) := by
    exact liftClosed_exec I prog (powerMarks_exec I D HC DC Aux (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) s4 d td ht
      (by simp [s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]) (by simp [s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy])
      (by simp [s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]) (by simp [s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s6 := (((s5.upd HC []).upd A (ys.map Item.int ++ .mark::ta)).upd C0
    (xs.reverse.map Item.int ++ s5.G C0)).upd H0 (xs.reverse.map Item.int ++ s5.G H0)
  have h6 : IExec I prog (liftClosed (duplicateTakeInts HC A C0 H0)) s5 s6 (duplicateTakeIntsCost xs) := by
    exact liftClosed_exec I prog (duplicateTakeInts_exec I HC A C0 H0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s5 xs (ys.map Item.int ++ .mark::ta) [] (by simp [cls])
      (by simp [s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]) (by simp [s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s7 := s6.upd H1 (.mark::s6.G H1)
  have h7 : IExec I prog (.op (.mark H1)) s6 s7 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s8 := (s7.upd A (.mark::ta)).upd H1 ((ys).reverse.map Item.int ++ s7.G H1)
  have h8 : IExec I prog (move A H1) s7 s8 (moveIntsCost ys) := by
    exact liftClosed_exec I prog (moveInts_exec I A H1 (by decide) s7 (ys) (.mark::ta)
      (by simp [cls]) (by simp [s7,s6,s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s9 := s8.upd A (ta)
  have h9 : IExec I prog (.op (.unmark A)) s8 s9 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s8,s7,s6,s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s10 := s9.upd A (.mark::s9.G A)
  have h10 : IExec I prog (.op (.mark A)) s9 s10 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s11 := (s10.upd H0 (.mark::s.G H0)).upd A ((xs.reverse).reverse.map Item.int ++ s10.G A)
  have h11 : IExec I prog (move H0 A) s10 s11 (moveIntsCost xs.reverse) := by
    exact liftClosed_exec I prog (moveInts_exec I H0 A (by decide) s10 (xs.reverse) (.mark::s.G H0)
      (by simp [cls]) (by simp [s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  let s12 := s11.upd H0 (s.G H0)
  have h12 : IExec I prog (.op (.unmark H0)) s11 s12 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hd,hv,hHC,hDC,hAux,List.map_append,List.append_assoc,List.replicate_succ,hx,hy]))
  have he : s12 = prepared s d z vs xs ys ta td tv := by
    cases s with
    | mk G ip o =>
      simp only [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,prepared,IState.upd]
      congr 1
      funext i
      by_cases hA : i=A
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hD : i=D
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hV : i=V
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hVS : i=VS
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hC : i=C0
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hH0 : i=H0
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hH1 : i=H1
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      by_cases hHCi : i=HC
      · subst i; simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux] <;> assumption
      simp [Function.update_apply,ha,hd,hv,hHC,hDC,hAux,hA,hD,hV,hVS,hC,hH0,hH1,hHCi]
  have hrun := (IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 (IExec.seq h6 (IExec.seq h7 (IExec.seq h8 (IExec.seq h9 (IExec.seq h10 (IExec.seq h11 (IExec.seq h12 (IExec.skip s12)))))))))))))
  change IExec I prog prepare s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> simp [prepareCost] <;> omega

end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (d : Nat) (z : Int) (vs xs ys : List.{0} Int)
  (ta td tv : List.{0} NLogN.Item)
  (hx :
    @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
  (hy :
    @Eq.{1} Nat (@List.length.{0} Int ys)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark)
  (ha :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Int) (List.{0} Int) (List.{0} Int)
            (@instHAppendOfAppend.{0} (List.{0} Int) (@List.instAppend.{0} Int)) xs ys))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark ta)))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.D)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          NLogN.Item.mark)
        td))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.V)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z)
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv)))
  (hHC :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hDC :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (hAux :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Wedge.prepare s
    (KoanaKPaths.Machine.Wedge.prepared s d z vs xs ys ta td tv) (KoanaKPaths.Machine.Wedge.prepareCost d z xs ys) := by
  exact @KoanaKPaths.Machine.Wedge.prepare_exec

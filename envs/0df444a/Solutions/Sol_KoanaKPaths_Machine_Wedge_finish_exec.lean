-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.finish_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:39:40.899308+00:00
-- url     : https://prove2.me/submissions/bd4d616e-3b21-492e-b337-90021db23c24

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
import Theorems.Thm_KoanaKPaths_Machine_Wedge_negate_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_zipAddInts_exec
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













lemma signed_negate_exec (I : List Sym) (s : IState NS) (z : ℤ) (vs : List Item)
    (xs : List ℤ) (tail : List Item)
    (hv : s.G V = .int z::vs) (ha : s.G A = xs.map Item.int ++ .mark::tail) :
    IExec I prog (.ite V (fun c => decide (c=Cls.neg)) (negate A) .skip) s
      (s.upd A ((signedList z xs).map Item.int ++ .mark::tail))
      ((if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25) := by
  by_cases hz : z<0
  · have hh : decide (s.cl V=Cls.neg) = true := by
      have hn : z≠0 := ne_of_lt hz
      simp [IState.cl,hv,cls,hz,hn]
    have hn := negate_exec I A (by decide) s xs tail ha
    simpa only [signedList,if_pos hz,List.map_map,Function.comp_def] using IExec.iteT hh hn
  · have hh : decide (s.cl V=Cls.neg) = false := by
      by_cases he : z=0 <;> simp [IState.cl,hv,cls,hz,he]
    have he : s.upd A ((signedList z xs).map Item.int ++ .mark::tail)=s := by
      rw [signedList,if_neg hz,← ha]
      exact upd_same _ _
    rw [he,if_neg hz]
    exact IExec.iteF hh (.skip s)

lemma signedBlock_eq (z : ℤ) (hz : z=1 ∨ z = -1) (xs ys : List ℤ) :
    List.zipWith (·+·) (signedList z xs) (ys.map (fun y => -y)) =
      List.zipWith (fun x y => z*x-y) xs ys := by
  rcases hz with rfl|rfl <;> simp only [signedList] <;> norm_num
  · induction xs generalizing ys <;> cases ys <;> simp_all [sub_eq_add_neg]
  · induction xs generalizing ys <;> cases ys <;> simp_all [sub_eq_add_neg]

end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z





lemma finish_exec (I : List Sym) (s : IState NS) (z : ℤ) (xs lower upper : List ℤ)
    (ta tr tc tw tvs : List Item) (hz : z=1 ∨ z = -1) (hlen : xs.length=upper.length)
    (ha : s.G A=ta) (hr : s.G R=upper.map Item.int ++ .mark::tr)
    (hc : s.G C0=xs.reverse.map Item.int ++ .mark::tc)
    (hw : s.G W0=lower.reverse.map Item.int ++ .mark::tw)
    (hv : s.G VS=.int z::tvs) :
    IExec I prog finish s (finished s z xs lower upper tr tc tw tvs) (finishCost z xs lower upper) := by
  let signed := signedList z xs
  let negUpper := upper.map (fun x => -x)
  let block := List.zipWith (·+·) signed negUpper
  have hb : block=List.zipWith (fun x y => z*x-y) xs upper := signedBlock_eq z hz xs upper
  have hl : signed.length=negUpper.length := by
    dsimp [signed,signedList,negUpper]
    split <;> simp [hlen]

  let s1 := s.upd A (.mark::s.G A)
  have h1 : IExec I prog (.op (.mark A)) s s1 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s2 := (s1.upd C0 (.mark::tc)).upd A ((xs.reverse).reverse.map Item.int ++ s1.G A)
  have h2 : IExec I prog (move C0 A) s1 s2 (moveIntsCost (xs.reverse)) := by
    exact liftClosed_exec I prog (moveInts_exec I C0 A (by decide) s1 (xs.reverse) (.mark::tc)
      (by simp [cls]) (by simp [s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s3 := s2.upd C0 (tc)
  have h3 : IExec I prog (.op (.unmark C0)) s2 s3 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s4 := (s3.upd VS tvs).upd V (.int z::s3.G V)
  have h4 : IExec I prog (.op (.mv VS V)) s3 s4 (2*moveCost (zsz z)+19) := by
    exact IExec.op (IOp.Step.mv (by decide) (by simp [s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s5 := s4.upd A (signed.map Item.int ++ .mark::ta)
  have h5 : IExec I prog (.ite V (fun c => decide (c=Cls.neg)) (negate A) .skip) s4 s5 ((if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25) := by
    exact signed_negate_exec I s4 z (s4.G V).tail xs ta
      (by simp [s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]) (by simp [s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def])
  let s6 := s5.upd R (upper.map (fun x => Item.int (-x)) ++ .mark::tr)
  have h6 : IExec I prog (negate R) s5 s6 (2*moveIntsCost upper+20*upper.length+3) := by
    exact negate_exec I R (by decide) s5 upper tr (by simp [s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def])
  let s7 := s6.upd U (.mark::s6.G U)
  have h7 : IExec I prog (.op (.mark U)) s6 s7 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s8 := ((s7.upd A (.mark::ta)).upd R (.mark::tr)).upd U
    (block.reverse.map Item.int ++ s7.G U)
  have h8 : IExec I prog (liftClosed (zipAddInts A R U)) s7 s8 (zipAddIntsCost signed negUpper) := by
    exact liftClosed_exec I prog (zipAddInts_exec I A R U (by decide) (by decide) (by decide)
      s7 signed negUpper (.mark::ta) (.mark::tr) (by simp [cls]) hl
      (by simp [s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]) (by simp [s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def,negUpper]))
  let s9 := s8.upd A (ta)
  have h9 : IExec I prog (.op (.unmark A)) s8 s9 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s10 := s9.upd R (tr)
  have h10 : IExec I prog (.op (.unmark R)) s9 s10 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s11 := s10.upd R (.mark::s10.G R)
  have h11 : IExec I prog (.op (.mark R)) s10 s11 (1) := by
    exact IExec.op (IOp.Step.mark)
  let s12 := (s11.upd U (.mark::s.G U)).upd R ((block.reverse).reverse.map Item.int ++ s11.G R)
  have h12 : IExec I prog (move U R) s11 s12 (moveIntsCost (block.reverse)) := by
    exact liftClosed_exec I prog (moveInts_exec I U R (by decide) s11 (block.reverse) (.mark::s.G U)
      (by simp [cls]) (by simp [s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s13 := s12.upd U (s.G U)
  have h13 : IExec I prog (.op (.unmark U)) s12 s13 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s14 := (s13.upd W0 (.mark::tw)).upd R ((lower.reverse).reverse.map Item.int ++ s13.G R)
  have h14 : IExec I prog (move W0 R) s13 s14 (moveIntsCost (lower.reverse)) := by
    exact liftClosed_exec I prog (moveInts_exec I W0 R (by decide) s13 (lower.reverse) (.mark::tw)
      (by simp [cls]) (by simp [s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s15 := s14.upd W0 (tw)
  have h15 : IExec I prog (.op (.unmark W0)) s14 s15 (1) := by
    exact IExec.op (IOp.Step.unmark (by simp [s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,ha,hr,hc,hw,hv,List.map_append,List.append_assoc,List.map_map,Function.comp_def]))
  let s16 := s15.upd D (.mark::s15.G D)
  have h16 : IExec I prog (.op (.mark D)) s15 s16 (1) := by
    exact IExec.op (IOp.Step.mark)
  have he : s16 = finished s z xs lower upper tr tc tw tvs := by
    cases s with
    | mk G ip o =>
      simp only [s16,s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,finished,IState.upd]
      congr 1
      funext i
      by_cases hAi : i=A
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hRi : i=R
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hC0i : i=C0
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hW0i : i=W0
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hVSi : i=VS
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hVi : i=V
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hDi : i=D
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      by_cases hUi : i=U
      · subst i; simp [Function.update_apply,ha,hr,hc,hw,hv,hb,List.map_append,List.append_assoc] <;> first | assumption | exact ha.symm
      simp [Function.update_apply,hAi,hRi,hC0i,hW0i,hVSi,hVi,hDi,hUi]
  have hrun := (IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 (IExec.seq h6 (IExec.seq h7 (IExec.seq h8 (IExec.seq h9 (IExec.seq h10 (IExec.seq h11 (IExec.seq h12 (IExec.seq h13 (IExec.seq h14 (IExec.seq h15 (IExec.seq h16 (IExec.skip s16)))))))))))))))))
  change IExec I prog finish s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> simp [finishCost,signed,negUpper,block] <;> omega

end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (z : Int) (xs lower upper : List.{0} Int)
  (ta tr tc tw tvs : List.{0} NLogN.Item)
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int upper))
  (ha : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A) ta)
  (hr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.R)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int upper) (@List.cons.{0} NLogN.Item NLogN.Item.mark tr)))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.C0)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tc)))
  (hw :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.W0)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int lower))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tw)))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.VS)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) tvs)),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Wedge.finish s
    (KoanaKPaths.Machine.Wedge.finished s z xs lower upper tr tc tw tvs)
    (KoanaKPaths.Machine.Wedge.finishCost z xs lower upper) := by
  exact @KoanaKPaths.Machine.Wedge.finish_exec

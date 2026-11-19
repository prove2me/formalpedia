-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.call_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.43157+00:00
-- url     : https://prove2.me/submissions/e53cef8a-e974-48a3-8eb4-82ddf250abf1

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
import Theorems.Thm_KoanaKPaths_Machine_Wedge_finish_exec
import Theorems.Thm_KoanaKPaths_Machine_Wedge_prepare_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
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
namespace KoanaKPaths.ExteriorCoordinates







lemma wedgeReverse_length (vs A : List ℤ) (h : A.length=2^vs.length) :
    (wedgeReverse vs A).length=2^vs.length := by
  induction vs generalizing A with
  | nil => rfl
  | cons z vs ih =>
    have hp : 2^vs.length ≤ A.length := by rw [h,List.length_cons,pow_succ]; omega
    have ha : (A.take (2^vs.length)).length=2^vs.length := by simp [List.length_take,Nat.min_eq_left hp]
    have hb : (A.drop (2^vs.length)).length=2^vs.length := by simp [List.length_drop,h,pow_succ]; omega
    simp only [wedgeReverse,List.length_append,List.length_zipWith,ih _ ha,ih _ hb,ha,Nat.min_self,
      List.length_cons,pow_succ]
    omega

end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge

lemma base_exec (I : List Sym) (s : IState NS) (z : ℤ) (tail : List Item)
    (ha : s.G A = .int z::.mark::tail) :
    IExec I prog base s
      ((s.upd A tail).upd R (.int 0::.mark::s.G R)) (2*zsz z+7) := by
  let s1 := s.upd A (.mark::tail)
  let s2 := s.upd A tail
  let s3 := s2.upd R (.mark::s.G R)
  let s4 := s2.upd R (.int 0::.mark::s.G R)
  have h1 : IExec I prog (.op (.drop A)) s s1 (2*zsz z+2) := .op (.drop ha)
  have h2 : IExec I prog (.op (.unmark A)) s1 s2 1 := by
    simpa only [s1,upd_upd] using
      (IExec.op (IOp.Step.unmark (I := I) (s := s1) (i := A) (by simp [s1])) : IExec I prog _ _ _ 1)
  have h3 : IExec I prog (.op (.mark R)) s2 s3 1 := by
    simpa only [s2,upd_G_ne s (show R≠A by decide)] using
      (IExec.op (IOp.Step.mark (s := s2) (i := R)) : IExec I prog _ _ _ 1)
  have h4 : IExec I prog (.op (.const R 0)) s3 s4 2 := by
    simpa only [s4,s3,upd_G_self,upd_upd,show zsz 0=0 from by simp [zsz,zbits,nbits_eq_bits],zero_add] using
      (IExec.op (IOp.Step.const (s := s3) (i := R) 0) : IExec I prog _ _ _ _)
  have h := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.skip s4))))
  change IExec I prog base s _ _ at h
  convert h using 1 <;> omega

lemma base_call_exec (I : List Sym) (s : IState NS) (z : ℤ) (tail : List Item)
    (ha : s.G A = .int z::.mark::tail) (hd : s.cl D ≠ Cls.mark) :
    IExec I prog (.call 0) s
      ((s.upd A tail).upd R (.int 0::.mark::s.G R)) (2*zsz z+34) := by
  have hbase := base_exec I s z tail ha
  have hbody : IExec I prog body s _ ((2*zsz z+7)+25) :=
    IExec.iteF (by simp only [decide_eq_false_iff_not]; exact hd) hbase
  have hcall := IExec.call (j := (0 : Fin 1)) (show IExec I prog (prog 0) s _ _ from hbody)
  convert hcall using 1 <;> omega













end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z



lemma between_exec (I : List Sym) (s : IState NS) (lower next : List ℤ) (ta tr th : List Item)
    (ha : s.G A=ta) (hr : s.G R=lower.map Item.int ++ .mark::tr)
    (hh : s.G H1=next.reverse.map Item.int ++ .mark::th) :
    IExec I prog between s (betweenState s lower next ta tr th)
      (moveIntsCost lower+moveIntsCost next.reverse+5) := by
  let s1 := s.upd W0 (.mark::s.G W0)
  let s2 := (s1.upd R (.mark::tr)).upd W0 (lower.reverse.map Item.int ++ s1.G W0)
  let s3 := s2.upd R tr
  let s4 := s3.upd A (.mark::s3.G A)
  let s5 := (s4.upd H1 (.mark::th)).upd A (next.reverse.reverse.map Item.int ++ s4.G A)
  let s6 := s5.upd H1 th
  have h1 : IExec I prog (.op (.mark W0)) s s1 1 := .op (.mark)
  have h2 : IExec I prog (move R W0) s1 s2 (moveIntsCost lower) := by
    exact liftClosed_exec I prog (moveInts_exec I R W0 (by decide) s1 lower (.mark::tr)
      (by simp [cls]) (by simp [s1,hr]))
  have h3 : IExec I prog (.op (.unmark R)) s2 s3 1 := by
    exact .op (.unmark (by simp [s2]))
  have h4 : IExec I prog (.op (.mark A)) s3 s4 1 := .op (.mark)
  have h5 : IExec I prog (move H1 A) s4 s5 (moveIntsCost next.reverse) := by
    exact liftClosed_exec I prog (moveInts_exec I H1 A (by decide) s4 next.reverse (.mark::th)
      (by simp [cls]) (by simp [s4,s3,s2,s1,hh]))
  have h6 : IExec I prog (.op (.unmark H1)) s5 s6 1 := by
    exact .op (.unmark (by simp [s5]))
  have he : s6=betweenState s lower next ta tr th := by
    cases s with
    | mk G ip o =>
      simp only [s6,s5,s4,s3,s2,s1,betweenState,IState.upd]
      congr 1
      funext i
      by_cases hA : i=A
      · subst i; simp [Function.update_apply,ha] <;> exact ha
      by_cases hR : i=R
      · subst i; simp [Function.update_apply]
      by_cases hW : i=W0
      · subst i; simp [Function.update_apply]
      by_cases hH : i=H1
      · subst i; simp [Function.update_apply]
      simp [Function.update_apply,hA,hR,hW,hH]
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5
    (IExec.seq h6 (IExec.skip s6))))))
  change IExec I prog between s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> omega

end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] A R V D C0 H0 H1 W0 U VS HC DC Aux Z



theorem call_exec (I : List Sym) (vs : List ℤ) :
    ∀ (s : IState NS) (xs : List ℤ) (ta td tv : List Item),
    xs.length=2^vs.length → (∀ z∈vs, z=1 ∨ z = -1) → cls td.head? ≠ Cls.mark →
    s.G A=xs.map Item.int ++ .mark::ta →
    s.G D=List.replicate vs.length .mark ++ td →
    s.G V=vs.map Item.int ++ tv →
    s.G HC=[] → s.G DC=[] → s.G Aux=[] →
    IExec I prog (.call 0) s
      ((s.upd A ta).upd R ((wedgeReverse vs xs).map Item.int ++ .mark::s.G R))
      (wedgeCost vs xs) := by
  induction vs with
  | nil =>
    intro s xs ta td tv hlen hsign ht ha hd hv hHC hDC hAux
    have hx : xs.length=1 := by simpa using hlen
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hx
    have hh : s.cl D ≠ Cls.mark := by simpa [IState.cl,hd] using ht
    simpa [wedgeReverse,wedgeCost] using base_call_exec I s x ta (by simpa using ha) hh
  | cons z vs ih =>
    intro s xs ta td tv hlen hsign ht ha hd hv hHC hDC hAux
    let d := vs.length
    let x0 := xs.take (2^d)
    let x1 := xs.drop (2^d)
    let lower := wedgeReverse vs x0
    let upper := wedgeReverse vs x1
    have hp : 2^d ≤ xs.length := by
      have he : xs.length=2^d*2 := by simpa [d,pow_succ] using hlen
      omega
    have hx0 : x0.length=2^d := by simp [x0,List.length_take,Nat.min_eq_left hp]
    have hx1 : x1.length=2^d := by
      simp only [x1,List.length_drop]
      have he : xs.length=2^d*2 := by simpa [d,pow_succ] using hlen
      omega
    have hxy : x0++x1=xs := List.take_append_drop _ _
    have hz : z=1 ∨ z = -1 := hsign z (by simp)
    have hvs : ∀ w∈vs, w=1 ∨ w = -1 := fun w hw => hsign w (by simp [hw])
    have hlower : lower.length=2^d := wedgeReverse_length vs x0 hx0
    have hupper : upper.length=2^d := wedgeReverse_length vs x1 hx1
    let p := prepared s d z vs x0 x1 ta td tv
    have hprep : IExec I prog prepare s p (prepareCost d z x0 x1) :=
      prepare_exec I s d z vs x0 x1 ta td tv hx0 hx1 ht
        (by rw [hxy]; exact ha) (by simpa [d] using hd) (by simpa using hv) hHC hDC hAux
    let l := (p.upd A ta).upd R (lower.map Item.int ++ .mark::p.G R)
    have hfirst : IExec I prog (.call 0) p l (wedgeCost vs x0) :=
      ih p x0 ta td tv hx0 hvs ht (by simp [p,prepared]) (by simp [p,prepared,d])
        (by simp [p,prepared]) (by simp [p,prepared,hHC]) (by simp [p,prepared,hDC])
        (by simp [p,prepared,hAux])
    let b := betweenState l lower x1 ta (s.G R) (s.G H1)
    have hbetween : IExec I prog between l b
        (moveIntsCost lower+moveIntsCost x1.reverse+5) :=
      between_exec I l lower x1 ta (s.G R) (s.G H1)
        (by simp [l]) (by simp [l,p,prepared]) (by simp [l,p,prepared])
    let u := (b.upd A ta).upd R (upper.map Item.int ++ .mark::b.G R)
    have hsecond : IExec I prog (.call 0) b u (wedgeCost vs x1) :=
      ih b x1 ta td tv hx1 hvs ht (by simp [b,betweenState])
        (by simp [b,betweenState,l,p,prepared,d]) (by simp [b,betweenState,l,p,prepared])
        (by simp [b,betweenState,l,p,prepared,hHC]) (by simp [b,betweenState,l,p,prepared,hDC])
        (by simp [b,betweenState,l,p,prepared,hAux])
    let f := finished u z x0 lower upper (s.G R) (s.G C0) (s.G W0) (s.G VS)
    have hfinish : IExec I prog finish u f (finishCost z x0 lower upper) :=
      finish_exec I u z x0 lower upper ta (s.G R) (s.G C0) (s.G W0) (s.G VS) hz
        (hx0.trans hupper.symm) (by simp [u]) (by simp [u,b,betweenState])
        (by simp [u,b,betweenState,l,p,prepared]) (by simp [u,b,betweenState,l,p,prepared])
        (by simp [u,b,betweenState,l,p,prepared])
    have he : f=(s.upd A ta).upd R ((wedgeReverse (z::vs) xs).map Item.int ++ .mark::s.G R) := by
      cases s with
      | mk G ip o =>
        have hD' : G D=List.replicate (d+1) .mark ++ td := hd
        have hV' : G V=.int z::(vs.map Item.int ++ tv) := hv
        simp only [D,V] at hD' hV'
        simp only [f,finished,u,b,betweenState,l,p,prepared,IState.upd]
        congr 1
        funext i
        by_cases hAi : i=A
        · subst i; simp [Function.update_apply]
        by_cases hRi : i=R
        · subst i; simp [Function.update_apply,wedgeReverse,d,x0,x1,lower,upper,List.map_append,List.append_assoc]
        by_cases hDi : i=D
        · subst i; simp [Function.update_apply,hD',List.replicate_succ]
        by_cases hVi : i=V
        · subst i; simp [Function.update_apply,hV']
        by_cases hCi : i=C0
        · subst i; simp [Function.update_apply]
        by_cases hHi : i=H1
        · subst i; simp [Function.update_apply]
        by_cases hWi : i=W0
        · subst i; simp [Function.update_apply]
        by_cases hSi : i=VS
        · subst i; simp [Function.update_apply]
        simp [Function.update_apply,hAi,hRi,hDi,hVi,hCi,hHi,hWi,hSi]
    have hstep := IExec.seq hprep (IExec.seq hfirst (IExec.seq hbetween (IExec.seq hsecond hfinish)))
    change IExec I prog step s f _ at hstep
    have hcond : decide (s.cl D=Cls.mark) = true := by
      simp [IState.cl,hd,List.replicate_succ,cls]
    have hbody := IExec.iteT (i := D) (f := fun c => decide (c=Cls.mark)) (q := base) hcond hstep
    have hcall := IExec.call (j := (0 : Fin 1)) (show IExec I prog (prog 0) s f _ from hbody)
    rw [he] at hcall
    convert hcall using 1
    simp only [wedgeCost]
    dsimp only [d,x0,x1,lower,upper]
    omega

end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (vs : List.{0} Int) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (xs : List.{0} Int)
  (ta td tv : List.{0} NLogN.Item),
  @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)) →
    (∀ (z : Int),
        @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
          Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Eq.{1} Int z
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
      @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark →
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
              (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
              (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark ta)) →
          @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.D)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                (@List.replicate.{0} NLogN.Item (@List.length.{0} Int vs) NLogN.Item.mark) td) →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.V)
                (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                  (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                  (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.HC)
                  (@List.nil.{0} NLogN.Item) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.DC)
                    (@List.nil.{0} NLogN.Item) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.Aux)
                      (@List.nil.{0} NLogN.Item) →
                    @NLogN.IExec KoanaKPaths.Machine.Wedge.NS
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I KoanaKPaths.Machine.Wedge.prog
                      (@NLogN.IStmt.call KoanaKPaths.Machine.Wedge.NS
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (nat_lit 0))))
                      s
                      (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS
                        (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A ta)
                        KoanaKPaths.Machine.Wedge.R
                        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
                            (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs xs))
                          (@List.cons.{0} NLogN.Item NLogN.Item.mark
                            (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.R))))
                      (KoanaKPaths.Machine.Wedge.wedgeCost vs xs) := by
  exact @KoanaKPaths.Machine.Wedge.call_exec

-- Prove2me | solution 1 for KoanaKPaths.Machine.GraphArray.laterArray_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:49:54.497452+00:00
-- url     : https://prove2.me/submissions/50ab4e7d-ed03-4ed9-b67f-e315aee7e57d

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
import Theorems.Thm_KoanaKPaths_Machine_Wedge_call_exec
import Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeCost_bound
import Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeReverse_width
import Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





end KoanaKPaths.Machine.Native

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma moveIntsCost_le (xs : List ℤ) (w : ℕ) (hw : ∀ z ∈ xs, zsz z ≤ w) :
    moveIntsCost xs ≤ (76*w+131)*xs.length+30 := by
  unfold moveIntsCost
  have h : (xs.map (fun z => 2*moveCost (zsz z)+49)).sum ≤ (76*w+131)*xs.length := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      have hz := hw z (by simp)
      have hr := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      unfold moveCost at *
      nlinarith
  omega
































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
open KoanaKPaths.ExteriorCoordinates

















lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith





















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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] Current Tmp Accumulate.Acc Wedge.A Wedge.R Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux



lemma laterArray_runs (I : List Sym) (s : IState NS) (vs xs : List ℤ) (w : ℕ)
    (td tv atail : List Item) (hdt : cls td.head?≠Cls.mark)
    (hd : s.G Wedge.D=List.replicate vs.length .mark ++ td)
    (hv : s.G Wedge.V=vs.map Item.int ++ tv) (hsgn : ∀ x∈vs, x=1 ∨ x= -1)
    (hacc : s.G Accumulate.Acc=xs.map Item.int ++ .mark::atail)
    (hlen : xs.length=2^vs.length) (hw : ∀ x∈xs, zsz x≤ w)
    (hc : s.G Wedge.HC=[]) (hdc : s.G Wedge.DC=[]) (ha : s.G Wedge.Aux=[]) :
    IRuns I Wedge.prog laterArray s
      ((s.upd Accumulate.Acc atail).upd Current
        ((wedgeReverse vs xs).map Item.int ++ .mark::s.G Current))
      (1000000*(vs.length+2)^2*(w+vs.length+2)*2^vs.length) := by
  let next := wedgeReverse vs xs
  let s0 := (s.upd Accumulate.Acc atail).upd Wedge.A (xs.map Item.int ++ .mark::s.G Wedge.A)
  let s1 := (s0.upd Wedge.A (s.G Wedge.A)).upd Wedge.R (next.map Item.int ++ .mark::s.G Wedge.R)
  let s2 := (s1.upd Wedge.R (s.G Wedge.R)).upd Current (next.map Item.int ++ .mark::s.G Current)
  have h0 : IExec I Wedge.prog (liftClosed (transferArray Accumulate.Acc Wedge.A Tmp)) s s0 (2*moveIntsCost xs+4) :=
    liftClosed_exec I Wedge.prog (transferArray_exec I Accumulate.Acc Wedge.A Tmp
      (by decide) (by decide) (by decide) s xs atail hacc)
  have h1 : IExec I Wedge.prog (.call 0) s0 s1 (Wedge.wedgeCost vs xs) := by
    have h := Wedge.call_exec I vs s0 xs (s.G Wedge.A) td tv hlen hsgn hdt (by simp [s0])
      (by simp [s0,hd]) (by simp [s0,hv]) (by simp [s0,hc]) (by simp [s0,hdc]) (by simp [s0,ha])
    simpa [s1,s0,next] using h
  have h2 : IExec I Wedge.prog (liftClosed (transferArray Wedge.R Current Tmp)) s1 s2 (2*moveIntsCost next+4) := by
    have h := liftClosed_exec I Wedge.prog (transferArray_exec I Wedge.R Current Tmp
      (by decide) (by decide) (by decide) s1 next (s.G Wedge.R) (by simp [s1]))
    simpa [s2,s1,s0] using h
  have he : s2=(s.upd Accumulate.Acc atail).upd Current (next.map Item.int ++ .mark::s.G Current) := by
    apply itemState_ext
    · intro i
      by_cases hC : i=Accumulate.Acc
      · subst i; simp [s2,s1,s0]
      by_cases hA : i=Wedge.A
      · subst i; simp [s2,s1,s0]
      by_cases hR : i=Wedge.R
      · subst i; simp [s2,s1,s0]
      by_cases hT : i=Current
      · subst i; simp [s2,s1,s0]
      simp [s2,s1,s0,IState.upd,Function.update_apply,hC,hA,hR,hT]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1) (Native.of_exec h2))
  rw [he] at h
  change IRuns I Wedge.prog laterArray s _ _ at h
  apply Native.mono h
  have hwedge := Wedge.wedgeCost_bound vs xs w hlen hsgn hw
  have hnext := Wedge.wedgeReverse_width vs xs w hsgn hw
  have hlen' : next.length=2^vs.length := wedgeReverse_length vs xs hlen
  have hm0 := Wedge.moveIntsCost_bound xs w hw
  have hm1 := Wedge.moveIntsCost_bound next (w+vs.length) hnext
  rw [hlen] at hm0
  rw [hlen'] at hm1
  have hp : 1≤2^vs.length := Nat.one_le_pow vs.length 2 (by omega)
  nlinarith

end KoanaKPaths.Machine.GraphArray

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.GraphArray.NS) (vs xs : List.{0} Int) (w : Nat)
  (td tv atail : List.{0} NLogN.Item)
  (hdt : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.D)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int vs) NLogN.Item.mark) td))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.V)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv))
  (hsgn :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hacc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark atail)))
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)))
  (hw :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hdc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (ha :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.GraphArray.laterArray s
    (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Accumulate.Acc atail)
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs xs))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Current))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 1000000) (instOfNatNat (nat_lit 1000000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int vs)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int vs))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs))) := by
  exact @KoanaKPaths.Machine.GraphArray.laterArray_runs

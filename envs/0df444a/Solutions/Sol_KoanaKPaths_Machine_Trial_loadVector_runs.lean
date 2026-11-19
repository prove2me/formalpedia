-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.loadVector_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:19.973629+00:00
-- url     : https://prove2.me/submissions/1fea2915-a7b2-4aa2-9d81-d00f8df7af73

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
import Theorems.Thm_KoanaKPaths_Machine_Trial_labelLoop_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_NLogN_smul_runs
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


















lemma copyMarks_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (copyMarks src dst tmp) s
      (s.upd dst (List.replicate m .mark ++ s.G dst)) (65*m+60) := by
  let s1 := (((s.upd src tail).upd dst (List.replicate m .mark ++ s.G dst)).upd tmp
    (List.replicate m .mark ++ s.G tmp))
  have hd := copyMoveMarks_exec I src dst tmp hsd hst hdt s m tail ht hs
  have hm := moveMarks_exec I tmp src (Ne.symm hst) s1 m [] (by decide) (by simp [s1,hx])
  have he : (s1.upd tmp []).upd src (List.replicate m .mark ++ s1.G src) =
      s.upd dst (List.replicate m .mark ++ s.G dst) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=tmp <;> simp_all
  have hrun := IExec.seq hd hm
  rw [he] at hrun
  change IExec I Fin.elim0 (copyMarks src dst tmp) s _ ((33*m+30)+(32*m+30)) at hrun
  convert hrun using 1 <;> omega

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]





































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
namespace KoanaKPaths.Machine.Trial
attribute [local simp] Vertex Row LabelCounter LabelTmp Wedge.V Wedge.D SignDB SignLookup.DB SignLookup.Count
  SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp Total



lemma loadVector_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (k v w : ℕ)
    (kt vt tt rest : List Item) (hw : 1≤ w)
    (hk : s.G 54=.int (k : ℤ)::kt) (hv : s.G Vertex=.int (v : ℤ)::vt)
    (hT : s.G Total=.int (xs.length : ℤ)::tt) (hdb : s.G SignDB=signItems xs++rest)
    (hD : s.G Wedge.D=List.replicate k .mark) (hC : s.G LabelCounter=[]) (hL : s.G LabelTmp=[])
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hi : s.G SignLookup.Count=[]) (hb : s.G SignLookup.Back=[]) (htmp : s.G SignLookup.Tmp=[])
    (hxs : ∀ x∈xs, x=1 ∨ x= -1)
    (he : ∀ row< k, labelExpr.width (labelValues k v row)≤ w)
    (hTw : zsz (xs.length : ℤ)≤ w) (hRw : ∀ row≤ k, zsz (row : ℤ)≤ w)
    (hvalid : ∀ row< k, v*k+row< xs.length) :
    IRuns I Fin.elim0 loadVector s
      (s.upd Wedge.V ((labelBlock xs k v 0 k).reverse.map Item.int ++ .mark::s.G Wedge.V))
      (labelIterationCost xs w*k+65*k+2*zsz (k : ℤ)+95) := by
  let s0 := s.upd Wedge.V (.mark::s.G Wedge.V)
  let s1 := s0.upd Row (.int 0::s.G Row)
  let s2 := s1.upd LabelCounter (List.replicate k .mark)
  let s3 := ((s2.upd LabelCounter []).upd Row (.int (k : ℤ)::s.G Row)).upd Wedge.V
    ((labelBlock xs k v 0 k).reverse.map Item.int ++ .mark::s.G Wedge.V)
  let s4 := s3.upd Row (s.G Row)
  have h0 : IExec I Fin.elim0 (.op (.mark Wedge.V)) s s0 1 := .op (.mark)
  have h1 : IExec I Fin.elim0 (.op (.const Row 0)) s0 s1 2 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s0) (i := Row) 0))
  have h2 : IExec I Fin.elim0 (copyMarks Wedge.D LabelCounter LabelTmp) s1 s2 (65*k+60) := by
    have h := copyMarks_exec I Wedge.D LabelCounter LabelTmp (by decide) (by decide) (by decide)
      s1 k [] (by simp [cls]) (by simp [s1,s0,hD]) (by simp [s1,s0,hL])
    simpa [s2,s1,s0,hC] using h
  have h3 : IRuns I Fin.elim0 labelLoop s2 s3 (labelIterationCost xs w*k+30) := by
    have h := labelLoop_runs I k s2 xs k v 0 w kt vt (s.G Row) tt rest hw (by omega)
      (by simp [s2]) (by simp [s2,s1,s0,hk]) (by simp [s2,s1,s0,hv]) (by simp [s2,s1])
      (by simp [s2,s1,s0,hT]) (by simp [s2,s1,s0,hdb]) (by simp [s2,s1,s0,hc])
      (by simp [s2,s1,s0,ht]) (by simp [s2,s1,s0,hi]) (by simp [s2,s1,s0,hb])
      (by simp [s2,s1,s0,htmp]) hxs he hTw hRw hvalid
    simpa [s3,s2,s1,s0] using h
  have h4 : IExec I Fin.elim0 (.op (.drop Row)) s3 s4 (2*zsz (k : ℤ)+2) := .op (.drop (by simp [s3]))
  have hpost : s4=s.upd Wedge.V
      ((labelBlock xs k v 0 k).reverse.map Item.int ++ .mark::s.G Wedge.V) := by
    apply itemState_ext
    · intro i
      by_cases hV : i=Wedge.V
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hR : i=Row
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hC' : i=LabelCounter
      · subst i; simp [s4,s3,s2,s1,s0,hC]
      simp [s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hV,hR,hC']
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq (Native.of_exec h2) (Native.seq h3 (Native.of_exec h4))))
  rw [hpost] at h
  change IRuns I Fin.elim0 loadVector s _ _ at h
  apply Native.mono h
  omega

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int) (k v w : Nat)
  (kt vt tt rest : List.{0} NLogN.Item)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hk :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 54))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt v)) vt))
  (hT :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest))
  (hD :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.D)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
  (hC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.nil.{0} NLogN.Item))
  (hL :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelTmp)
      (@List.nil.{0} NLogN.Item))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hi :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hxs :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (he :
    ∀ (row : Nat),
      @LT.lt.{0} Nat instLTNat row k →
        @LE.le.{0} Nat instLENat
          (@KoanaKPaths.Machine.Arithmetic.Expr.width (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (KoanaKPaths.Machine.Trial.labelValues k v row) KoanaKPaths.Machine.Trial.labelExpr)
          w)
  (hTw : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w)
  (hRw :
    ∀ (row : Nat),
      @LE.le.{0} Nat instLENat row k → @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt row)) w)
  (hvalid :
    ∀ (row : Nat),
      @LT.lt.{0} Nat instLTNat row k →
        @LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v k) row)
          (@List.length.{0} Int xs)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.loadVector s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (KoanaKPaths.Machine.Trial.labelBlock xs k v (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              k)))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (KoanaKPaths.Machine.Trial.labelIterationCost xs w) k)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65))) k))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt k))))
      (@OfNat.ofNat.{0} Nat (nat_lit 95) (instOfNatNat (nat_lit 95)))) := by
  exact @KoanaKPaths.Machine.Trial.loadVector_runs

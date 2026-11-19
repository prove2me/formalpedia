-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.labelLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:37.76244+00:00
-- url     : https://prove2.me/submissions/701ebead-7c92-4630-a4d3-9c6db739fd8d

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
import Theorems.Thm_KoanaKPaths_Machine_Trial_labelBody_runs
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


lemma loopT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog (.loop i f p) s1 s2 d) :
    IRuns I iprog (.loop i f p) s s2 (c+d+30) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d'+30,by omega,.loopT hf h1 h2⟩
lemma loopF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false) :
    IRuns I iprog (.loop i f p) s s 30 := of_exec (.loopF hf)

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
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]






















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
namespace KoanaKPaths.Machine.Trial
attribute [local simp] Vertex Row LabelCounter LabelTmp Wedge.V SignDB SignLookup.DB SignLookup.Count
  SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp Total







lemma labelLoop_runs (I : List Sym) (m : ℕ) : ∀ (s : IState NS) (xs : List ℤ) (k v r w : ℕ)
    (kt vt rt tt rest : List Item),
    1≤ w → r+m≤ k → s.G LabelCounter=List.replicate m .mark →
    s.G 54=.int (k : ℤ)::kt → s.G Vertex=.int (v : ℤ)::vt → s.G Row=.int (r : ℤ)::rt →
    s.G Total=.int (xs.length : ℤ)::tt → s.G SignDB=signItems xs++rest →
    s.G BitCounter.Count=[] → s.G BitCounter.Tmp=[] → s.G SignLookup.Count=[] →
    s.G SignLookup.Back=[] → s.G SignLookup.Tmp=[] →
    (∀ x∈xs, x=1 ∨ x= -1) →
    (∀ row< k, labelExpr.width (labelValues k v row)≤ w) →
    zsz (xs.length : ℤ)≤ w → (∀ row≤ k, zsz (row : ℤ)≤ w) →
    (∀ row< k, v*k+row< xs.length) →
    IRuns I Fin.elim0 labelLoop s
      (((s.upd LabelCounter []).upd Row (.int ((r+m : ℕ) : ℤ)::rt)).upd Wedge.V
        ((labelBlock xs k v r m).reverse.map Item.int ++ s.G Wedge.V))
      (labelIterationCost xs w*m+30) := by
  induction m with
  | zero =>
    intro s xs k v r w kt vt rt tt rest hw hbound hC hk hv hr hT hdb hc ht hi hb htmp hxs he hTw hRw hvalid
    have hcl : decide (s.cl LabelCounter=Cls.mark)=false := by simp [IState.cl,hC,cls]
    have hpost : (((s.upd LabelCounter []).upd Row (.int ((r+0 : ℕ) : ℤ)::rt)).upd Wedge.V
        ((labelBlock xs k v r 0).reverse.map Item.int ++ s.G Wedge.V))=s := by
      simp only [labelBlock,List.reverse_nil,List.map_nil,List.nil_append,Nat.add_zero]
      have hC' : s.G LabelCounter=[] := by simpa using hC
      rw [← hC',← hr]
      simp
    rw [hpost]
    exact Native.loopF hcl
  | succ m ih =>
    intro s xs k v r w kt vt rt tt rest hw hbound hC hk hv hr hT hdb hc ht hi hb htmp hxs he hTw hRw hvalid
    have hrow : r< k := by omega
    have hj : v*k+r< xs.length := hvalid r hrow
    let z := xs[v*k+r]'hj
    let s0 := s.upd LabelCounter (List.replicate m .mark)
    let s1 := (s0.upd Row (.int ((r+1 : ℕ) : ℤ)::rt)).upd Wedge.V (.int z::s.G Wedge.V)
    have h0 : IExec I Fin.elim0 (.op (.unmark LabelCounter)) s s0 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hC))
    have h1 : IRuns I Fin.elim0 labelBody s0 s1
        (500000*(w+1)^2+10000*(xs.length+1)) :=
      labelBody_runs I s0 xs k v r w kt vt rt tt rest hw
        (by simp [s0,hk]) (by simp [s0,hv]) (by simp [s0,hr]) (by simp [s0,hT])
        (by simp [s0,hdb]) (by simp [s0,hc]) (by simp [s0,ht]) (by simp [s0,hi])
        (by simp [s0,hb]) (by simp [s0,htmp]) hxs (he r hrow) hTw (hRw r (by omega)) hj
    have htail := ih s1 xs k v (r+1) w kt vt rt tt rest hw (by omega)
      (by simp [s1,s0]) (by simp [s1,s0,hk]) (by simp [s1,s0,hv]) (by simp [s1])
      (by simp [s1,s0,hT]) (by simp [s1,s0,hdb]) (by simp [s1,s0,hc]) (by simp [s1,s0,ht])
      (by simp [s1,s0,hi]) (by simp [s1,s0,hb]) (by simp [s1,s0,htmp]) hxs he hTw hRw hvalid
    have hcl : decide (s.cl LabelCounter=Cls.mark)=true := by simp [IState.cl,hC,List.replicate_succ,cls]
    have h := Native.loopT hcl (Native.seq (Native.of_exec h0) h1) htail
    have hget : xs.getD (v*k+r) 1=z := List.getD_eq_getElem _ _ hj
    have hget' : xs[v*k+r]?.getD 1=z := hget
    have hpost : (((s1.upd LabelCounter []).upd Row (.int ((r+1+m : ℕ) : ℤ)::rt)).upd Wedge.V
        ((labelBlock xs k v (r+1) m).reverse.map Item.int ++ s1.G Wedge.V))=
      (((s.upd LabelCounter []).upd Row (.int ((r+(m+1) : ℕ) : ℤ)::rt)).upd Wedge.V
        ((labelBlock xs k v r (m+1)).reverse.map Item.int ++ s.G Wedge.V)) := by
      apply itemState_ext
      · intro i
        by_cases hC : i=LabelCounter
        · subst i; simp [s1,s0]
        by_cases hR : i=Row
        · subst i; simp [s1,s0,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        by_cases hV : i=Wedge.V
        · subst i; simp [s1,s0,labelBlock,List.reverse_cons,List.map_append,List.append_assoc,hget,hget']
        simp [s1,s0,IState.upd,Function.update_apply,hC,hR,hV]
      · rfl
      · rfl
    rw [hpost] at h
    change IRuns I Fin.elim0 labelLoop s _ _ at h
    apply Native.mono h
    unfold labelIterationCost
    ring_nf
    exact le_rfl

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (m : Nat) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int) (k v r w : Nat)
  (kt vt rt tt rest : List.{0} NLogN.Item),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w →
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r m) k →
      @Eq.{1} (List.{0} NLogN.Item)
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
          (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) →
        @Eq.{1} (List.{0} NLogN.Item)
            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
              (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
                (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127))))
                  (nat_lit 54))))
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt) →
          @Eq.{1} (List.{0} NLogN.Item)
              (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
              (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt v)) vt) →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Row)
                (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt r)) rt) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
                  (@List.cons.{0} NLogN.Item
                    (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
                    (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                      (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                      (KoanaKPaths.Machine.Trial.signItems xs) rest) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
                      (@List.nil.{0} NLogN.Item) →
                    @Eq.{1} (List.{0} NLogN.Item)
                        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
                        (@List.nil.{0} NLogN.Item) →
                      @Eq.{1} (List.{0} NLogN.Item)
                          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
                          (@List.nil.{0} NLogN.Item) →
                        @Eq.{1} (List.{0} NLogN.Item)
                            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
                            (@List.nil.{0} NLogN.Item) →
                          @Eq.{1} (List.{0} NLogN.Item)
                              (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
                              (@List.nil.{0} NLogN.Item) →
                            (∀ (x : Int),
                                @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
                                  Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                    (@Eq.{1} Int x
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
                              (∀ (row : Nat),
                                  @LT.lt.{0} Nat instLTNat row k →
                                    @LE.le.{0} Nat instLENat
                                      (@KoanaKPaths.Machine.Arithmetic.Expr.width
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (KoanaKPaths.Machine.Trial.labelValues k v row)
                                        KoanaKPaths.Machine.Trial.labelExpr)
                                      w) →
                                @LE.le.{0} Nat instLENat
                                    (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w →
                                  (∀ (row : Nat),
                                      @LE.le.{0} Nat instLENat row k →
                                        @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt row)) w) →
                                    (∀ (row : Nat),
                                        @LT.lt.{0} Nat instLTNat row k →
                                          @LT.lt.{0} Nat instLTNat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v k) row)
                                            (@List.length.{0} Int xs)) →
                                      @NLogN.IRuns KoanaKPaths.Machine.Trial.NS
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
                                        (@Fin.elim0.{1}
                                          (NLogN.IStmt KoanaKPaths.Machine.Trial.NS
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        KoanaKPaths.Machine.Trial.labelLoop s
                                        (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
                                          (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
                                            (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s
                                              KoanaKPaths.Machine.Trial.LabelCounter (@List.nil.{0} NLogN.Item))
                                            KoanaKPaths.Machine.Trial.Row
                                            (@List.cons.{0} NLogN.Item
                                              (NLogN.Item.int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    m)))
                                              rt))
                                          KoanaKPaths.Machine.Wedge.V
                                          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                                            (List.{0} NLogN.Item)
                                            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item)
                                              (@List.instAppend.{0} NLogN.Item))
                                            (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
                                              (@List.reverse.{0} Int (KoanaKPaths.Machine.Trial.labelBlock xs k v r m)))
                                            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
                                              KoanaKPaths.Machine.Wedge.V)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (KoanaKPaths.Machine.Trial.labelIterationCost xs w) m)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.labelLoop_runs

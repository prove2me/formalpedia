-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.groupFold_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.650836+00:00
-- url     : https://prove2.me/submissions/9609a36c-f791-40ce-a4e2-2e33dd6f1d83

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Trial_groupNative_runs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
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
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main









lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

attribute [local simp] GroupCounter TrialTemplate TrialCounter GroupCopyTmp Coins Balanced.Restore Balanced.Records








lemma groupFold_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (arcs : List (Fin n × Fin n)) (oss : List (List (Fin (trialBits n k)→Bool)))
    (m : ℕ) (tail : List Item) (hk : 1≤ k) (hr : Ready (k := k) s arcs)
    (hlen : ∀ os∈oss, os.length=m)
    (hCount : s.G GroupCounter=List.replicate oss.length .mark)
    (ht : s.G TrialTemplate=List.replicate m .mark) (hc : s.G TrialCounter=[])
    (hx : s.G GroupCopyTmp=[]) (hRestore : s.G Balanced.Restore=[])
    (hCoins : s.G Coins=groupsStream oss++tail) :
    IRuns I Wedge.prog groupFold s (groupFoldState s arcs oss tail)
      ((groupNativeCost n k arcs.length m+31)*oss.length+30) := by
  induction oss generalizing s with
  | nil =>
    have he : groupFoldState (k := k) s arcs [] tail=s := by
      have hco : s.G Coins=tail := by simpa [groupsStream] using hCoins
      have hct : s.G GroupCounter=[] := by simpa using hCount
      simp only [groupFoldState,groupSums,List.map_nil,List.reverse_nil,List.nil_append]
      rw [←hco,←hct]
      simp
    rw [he]
    simpa [groupFold] using (Native.loopF (I := I) (iprog := Wedge.prog)
      (p := .seq (.op (.unmark GroupCounter)) groupNative) (s := s) (by simp [IState.cl,hCount,cls]))
  | cons os oss ih =>
    let rest := groupsStream oss++tail
    let x := (numerators arcs os).sum
    let s0 := s.upd GroupCounter (List.replicate oss.length .mark)
    let s1 := (s0.upd Coins rest).upd Balanced.Records (.int x::s.G Balanced.Records)
    have h0 : IExec I Wedge.prog (.op (.unmark GroupCounter)) s s0 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hCount))
    have hm : os.length=m := hlen os (by simp)
    have h1 : IRuns I Wedge.prog groupNative s0 s1 (groupNativeCost n k arcs.length m) := by
      have h := groupNative_runs I s0 arcs os rest hk (hr.upd GroupCounter (by decide) _)
        (by simp [s0,ht,hm]) (by simp [s0,hc]) (by simp [s0,hx]) (by simp [s0,hRestore])
        (by simpa [s0,groupsStream,rest,List.append_assoc] using hCoins)
      simpa [s1,s0,x,hm] using h
    have hr1 : Ready (k := k) s1 arcs :=
      ((hr.upd GroupCounter (by decide) _).upd Coins (by decide) _).upd Balanced.Records (by decide) _
    have h2 := ih s1 hr1 (fun os hos => hlen os (by simp [hos]))
      (by simp [s1,s0]) (by simp [s1,s0,ht]) (by simp [s1,s0,hc])
      (by simp [s1,s0,hx]) (by simp [s1,s0,hRestore]) (by simp [s1,rest])
    have he : groupFoldState s1 arcs oss tail=groupFoldState s arcs (os::oss) tail := by
      apply itemState_ext
      · intro r
        by_cases h100 : r=100 <;> by_cases h52 : r=52 <;> by_cases h107 : r=107 <;>
          simp [groupFoldState,groupSums,s1,s0,IState.upd,Function.update_apply,h100,h52,h107,x,List.map_append,List.append_assoc]
      · rfl
      · rfl
    rw [he] at h2
    have h := Native.loopT (by simp [IState.cl,hCount,List.replicate_succ,cls])
      (Native.seq (Native.of_exec h0) h1) h2
    change IRuns I Wedge.prog groupFold s _ _ at h
    exact Native.mono h (by simp only [List.length_cons]; nlinarith)

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (oss : List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) (m : Nat) (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hlen :
    ∀ (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)),
      @Membership.mem.{0, 0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
          (List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)))
          (@List.instMembership.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) oss os →
        @Eq.{1} Nat (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os) m)
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)
        NLogN.Item.mark))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialTemplate)
      (@List.replicate.{0} NLogN.Item m NLogN.Item.mark))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.groupsStream n k oss) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupFold s
    (@KoanaKPaths.Machine.Trial.groupFoldState n k s arcs oss tail)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (KoanaKPaths.Machine.Trial.groupNativeCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.groupFold_runs

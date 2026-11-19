-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.querySign_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.28117+00:00
-- url     : https://prove2.me/submissions/9e9d8059-a165-427c-a69a-2cda37cfc29e

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
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_SignLookup_program_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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
namespace KoanaKPaths.Machine.SignLookup







attribute [local simp] DB Out Cache Count Back Tmp

















lemma frames_cons (a : List ℤ) (arrays : List (List ℤ)) :
    frames (a::arrays)=a.map Item.int ++ .mark::frames arrays := by
  simp [frames,List.append_assoc]




















lemma frames_append (as bs : List (List ℤ)) : frames (as++bs)=frames as++frames bs := by
  simp [frames,List.flatMap_append]

lemma frames_split (as : List (List ℤ)) (i : Fin as.length) :
    frames as=frames (as.take i.val) ++ as[i].map Item.int ++ .mark::frames (as.drop (i.val+1)) := by
  have ht : as.take i.val++(as[i]::as.drop (i.val+1))=as := by
    simp only [Fin.getElem_fin]
    rw [← List.drop_eq_getElem_cons i.isLt,List.take_append_drop]
  calc
    _ = frames (as.take i.val++(as[i]::as.drop (i.val+1))) := congrArg frames ht.symm
    _ = _ := by rw [frames_append,frames_cons]; simp [List.append_assoc]

lemma selected_exec (I : List Sym) (s : IState NS) (arrays : List (List ℤ)) (i : Fin arrays.length)
    (rest ct : List Item) (ht : cls ct.head? ≠ Cls.mark)
    (hc : s.G Count=List.replicate i.val .mark ++ ct)
    (hd : s.G DB=frames arrays++rest) (hb : s.G Back=[]) (hx : s.G Tmp=[]) :
    IExec I Fin.elim0 program s (s.upd Out (arrays[i].reverse.map Item.int ++ s.G Out))
      (lookupCost (arrays.take i.val) arrays[i]) := by
  apply program_exec I s (arrays.take i.val) arrays[i] (frames (arrays.drop (i.val+1))++rest) ct ht
  · simpa only [List.length_take,Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hc
  · simpa only [frames_split arrays i,List.append_assoc,List.cons_append] using hd
  · exact hb
  · exact hx

end KoanaKPaths.Machine.SignLookup

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}



lemma clearMarks_exec (I : List Sym) (src : Fin S) (s : IState S) (m : ℕ) (tail : List Item)
    (ht : cls tail.head? ≠ Cls.mark) (hs : s.G src=List.replicate m .mark ++ tail) :
    IExec I Fin.elim0 (clearMarks src) s (s.upd src tail) (31*m+30) := by
  induction m generalizing s with
  | zero =>
    have he : s.upd src tail=s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simp [IState.cl,hs,ht])
  | succ m ih =>
    let s1 := s.upd src (List.replicate m .mark ++ tail)
    have h1 : IExec I Fin.elim0 (.op (.unmark src)) s s1 1 := .op (.unmark (by simpa [List.replicate_succ] using hs))
    have htail := ih s1 (by simp [s1])
    have hrun := IExec.loopT (by simp [IState.cl,hs,List.replicate_succ,cls]) h1 htail
    change IExec I Fin.elim0 (clearMarks src) s _ _ at hrun
    simpa only [s1,upd_upd,show 1+(31*m+30)+30=31*(m+1)+30 by omega] using hrun















end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
attribute [local simp] SignDB SignLookup.DB SignLookup.Out SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp

lemma signItems_frames (xs : List ℤ) :
    signItems xs=SignLookup.frames (xs.reverse.map (fun x => [x])) := by
  unfold signItems SignLookup.frames
  rw [List.flatMap_map]
  rfl



lemma querySign_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (i : Fin xs.length)
    (st rest : List Item) (hsource : s.G BitCounter.Source=.int (i.val : ℤ)::st)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hindex : s.G SignLookup.Count=[]) (hback : s.G SignLookup.Back=[])
    (htmp : s.G SignLookup.Tmp=[]) (hdb : s.G SignDB=signItems xs++rest) :
    IRuns I Fin.elim0 querySign s
      ((s.upd BitCounter.Source st).upd SignLookup.Out
        (.int (xs.reverse[i.val]'(by simpa using i.isLt))::s.G SignLookup.Out))
      (1100*(i.val+1)+SignLookup.lookupCost
        ((xs.reverse.map (fun x => [x])).take i.val) [xs.reverse[i.val]'(by simpa using i.isLt)]) := by
  let arrays := xs.reverse.map (fun x => [x])
  let idx : Fin arrays.length := ⟨i.val,by simpa [arrays] using i.isLt⟩
  let s1 := (s.upd BitCounter.Source st).upd BitCounter.Count (List.replicate i.val .mark)
  let s2 := (s1.upd BitCounter.Count []).upd SignLookup.Count (List.replicate i.val .mark)
  let x := xs.reverse[i.val]'(by simpa using i.isLt)
  let s3 := s2.upd SignLookup.Out (.int x::s.G SignLookup.Out)
  let s4 := s3.upd SignLookup.Count []
  have h1 : IRuns I Fin.elim0 BitCounter.toMarks s s1 (1000*(i.val+1)) := by
    simpa only [hc,List.append_nil] using BitCounter.toMarks_runs I s i.val st hsource (by simp [hc,cls]) ht
  have h2 : IExec I Fin.elim0 (moveMarks BitCounter.Count SignLookup.Count) s1 s2 (32*i.val+30) := by
    have h := moveMarks_exec I BitCounter.Count SignLookup.Count (by decide) s1 i.val []
      (by simp [cls]) (by simp [s1])
    simpa [s2,s1,hindex] using h
  have hdb' : s.G SignDB=SignLookup.frames arrays++rest := by
    simpa only [arrays,signItems_frames] using hdb
  have h3 : IExec I Fin.elim0 SignLookup.program s2 s3
      (SignLookup.lookupCost (arrays.take i.val) [x]) := by
    have h := SignLookup.selected_exec I s2 arrays idx rest [] (by simp [cls])
      (by simp [s2,idx]) (by simpa [s2,s1] using hdb')
      (by simp [s2,s1,hback]) (by simp [s2,s1,htmp])
    simpa [s3,s2,s1,arrays,idx,x] using h
  have h4 : IExec I Fin.elim0 (clearMarks SignLookup.Count) s3 s4 (31*i.val+30) := by
    exact clearMarks_exec I SignLookup.Count s3 i.val [] (by simp [cls]) (by simp [s3,s2])
  have he : s4=(s.upd BitCounter.Source st).upd SignLookup.Out (.int x::s.G SignLookup.Out) := by
    apply itemState_ext
    · intro r
      by_cases hS : r=BitCounter.Source
      · subst r; simp [s4,s3,s2,s1]
      by_cases hC : r=BitCounter.Count
      · subst r; simp [s4,s3,s2,s1,hc]
      by_cases hI : r=SignLookup.Count
      · subst r; simp [s4,s3,s2,s1,hindex]
      by_cases hO : r=SignLookup.Out
      · subst r; simp [s4,s3,s2,s1]
      simp [s4,s3,s2,s1,IState.upd,Function.update_apply,hS,hC,hI,hO]
    · rfl
    · rfl
  have h := Native.seq h1 (Native.seq (Native.of_exec h2)
    (Native.seq (Native.of_exec h3) (Native.of_exec h4)))
  rw [he] at h
  change IRuns I Fin.elim0 querySign s _ _ at h
  apply Native.mono h
  dsimp only [arrays,x]
  omega





end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int)
  (i : Fin (@List.length.{0} Int xs)) (st rest : List.{0} NLogN.Item)
  (hsource :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val (@List.length.{0} Int xs) i))) st))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hindex :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hback :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.querySign s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source st)
      KoanaKPaths.Machine.SignLookup.Out
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) (@List.reverse.{0} Int xs) (@Fin.val (@List.length.{0} Int xs) i)
            (@of_eq_true
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                (@List.length.{0} Int (@List.reverse.{0} Int xs)))
              (@Eq.trans.{1} Prop
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                  (@List.length.{0} Int (@List.reverse.{0} Int xs)))
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i) (@List.length.{0} Int xs)) True
                (@congrArg.{1, 1} Nat Prop (@List.length.{0} Int (@List.reverse.{0} Int xs)) (@List.length.{0} Int xs)
                  (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)) (@List.length_reverse.{0} Int xs))
                (@Fin.is_lt._simp_1 (@List.length.{0} Int xs) i)))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1100) (instOfNatNat (nat_lit 1100)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val (@List.length.{0} Int xs) i)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (KoanaKPaths.Machine.SignLookup.lookupCost
        (@List.take.{0} (List.{0} Int) (@Fin.val (@List.length.{0} Int xs) i)
          (@List.map.{0, 0} Int (List.{0} Int) (fun (x : Int) => @List.cons.{0} Int x (@List.nil.{0} Int))
            (@List.reverse.{0} Int xs)))
        (@List.cons.{0} Int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) (@List.reverse.{0} Int xs) (@Fin.val (@List.length.{0} Int xs) i)
            (@of_eq_true
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                (@List.length.{0} Int (@List.reverse.{0} Int xs)))
              (@Eq.trans.{1} Prop
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                  (@List.length.{0} Int (@List.reverse.{0} Int xs)))
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i) (@List.length.{0} Int xs)) True
                (@congrArg.{1, 1} Nat Prop (@List.length.{0} Int (@List.reverse.{0} Int xs)) (@List.length.{0} Int xs)
                  (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)) (@List.length_reverse.{0} Int xs))
                (@Fin.is_lt._simp_1 (@List.length.{0} Int xs) i))))
          (@List.nil.{0} Int)))) := by
  exact @KoanaKPaths.Machine.Trial.querySign_runs

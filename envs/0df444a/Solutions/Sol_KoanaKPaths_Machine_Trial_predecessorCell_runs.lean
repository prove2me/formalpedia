-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.predecessorCell_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:00:35.154892+00:00
-- url     : https://prove2.me/submissions/a49f0f8d-80f7-4ddb-bb08-fc91995808a1

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_program_exec
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_GraphArray_weightedAdd_runs
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_readSign_runs
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192
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

lemma liftClosed_runs (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IRuns I Fin.elim0 p s s' c) : IRuns I prog (liftClosed p) s s' c := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht,liftClosed_exec I prog h⟩

end KoanaKPaths.Machine

end
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates















lemma sum_map_le_mul {α : Type} (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs, f x≤ C) : (xs.map f).sum ≤ C*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤ w) :
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
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}











lemma Expr.root_width (e : Expr v) (values : Fin v→ℕ) :
    zsz (e.eval values : ℤ)≤ e.width values := by
  cases e <;> exact le_max_left _ _



end KoanaKPaths.Machine.Arithmetic

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup







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

end KoanaKPaths.Machine.ArrayLookup

end
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup

lemma forwardCost_bound (pre : List (List ℤ)) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤ P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤ w) :
    forwardCost pre ≤ (200*(w+1)*(P+1)+35)*pre.length+30 := by
  have hs := Wedge.sum_map_le_mul (fun a => moveIntsCost a+35) pre (200*(w+1)*(P+1)+35) (by
    intro a ha
    have h := Wedge.moveIntsCost_bound a w (hw a ha)
    have hl := hlen a ha
    nlinarith)
  unfold forwardCost
  omega

lemma backwardCost_bound (pre : List (List ℤ)) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤ P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤ w) :
    backwardCost pre ≤ (200*(w+1)*(P+1)+35)*pre.length+30 := by
  have hs := Wedge.sum_map_le_mul (fun a => moveIntsCost a.reverse+35) pre (200*(w+1)*(P+1)+35) (by
    intro a ha
    have h := Wedge.moveIntsCost_bound a.reverse w (by simpa using hw a ha)
    simp only [List.length_reverse] at h
    have hl := hlen a ha
    nlinarith)
  unfold backwardCost
  omega

lemma duplicateMoveIntsCost_bound (xs : List ℤ) (w : ℕ) (hw : ∀ x∈xs, zsz x≤ w) :
    duplicateMoveIntsCost xs ≤ 400*(w+1)*(xs.length+1) := by
  have hs := Wedge.sum_map_le_mul
    (fun z => dupCost (zsz z)+17+(2*moveCost (zsz z)+19)+30) xs (211*w+313) (by
      intro z hz
      have h := hw z hz
      simp only [dupCost,zipCost,moveCost]
      nlinarith)
  unfold duplicateMoveIntsCost
  nlinarith

lemma lookupCost_bound (pre : List (List ℤ)) (target : List ℤ) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤ P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤ w)
    (htlen : target.length≤ P) (htw : ∀ x∈target, zsz x≤ w) :
    lookupCost pre target ≤ 2000*(w+1)*(P+1)*(pre.length+1) := by
  have hf := forwardCost_bound pre P w hlen hw
  have hb := backwardCost_bound pre P w hlen hw
  have hc := duplicateMoveIntsCost_bound target w htw
  have hm := Wedge.moveIntsCost_bound target.reverse w (by simpa using htw)
  simp only [List.length_reverse] at hm
  unfold lookupCost
  nlinarith [Nat.zero_le (w*P),Nat.zero_le (w*P*pre.length),Nat.zero_le (w*pre.length),
    Nat.zero_le (P*pre.length)]

lemma lookupCost_power_bound (pre : List (List ℤ)) (target : List ℤ) (k w : ℕ)
    (hlen : ∀ a∈pre, a.length≤2^k) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤ w)
    (htlen : target.length≤2^k) (htw : ∀ x∈target, zsz x≤ w) :
    lookupCost pre target ≤ 4000*(w+1)*2^k*(pre.length+1) := by
  have h := lookupCost_bound pre target (2^k) w hlen hw htlen htw
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  calc
    _ ≤ 2000*(w+1)*(2^k+1)*(pre.length+1) := h
    _ ≤ 2000*(w+1)*(2*2^k)*(pre.length+1) := by gcongr; omega
    _ = 4000*(w+1)*2^k*(pre.length+1) := by ring

end KoanaKPaths.Machine.ArrayLookup

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Square.Eval Square.Value BitCounter.Source BitCounter.Count BitCounter.Tmp



lemma storeExpr_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (dst : Fin Square.NS) (hd : dst≠Eval) (s : IState Square.NS)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (storeExpr reg e dst) s
      (s.upd dst (.int (e.eval values : ℤ)::s.G dst)) (11000*(e.size+1)*(w+1)^2) := by
  let s1 := s.upd Eval (.int (e.eval values : ℤ)::s.G Eval)
  let s2 := (s1.upd Eval (s.G Eval)).upd dst (.int (e.eval values : ℤ)::s.G dst)
  have h1 := e.compile_runs I reg hreg values w hw s hv
  have h2 : IExec I Fin.elim0 (.op (.mv Eval dst)) s1 s2 (2*moveCost (zsz (e.eval values : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt Square.NS 0))
      (IOp.Step.mv (s := s1) (i := Eval) (j := dst) (a := (e.eval values : ℤ)) (L := s.G Eval)
        (Ne.symm hd) (by simp [s1]))
    simpa [s2,s1,hd] using h
  have he : s2=s.upd dst (.int (e.eval values : ℤ)::s.G dst) := by simp [s2,s1]
  have h := Native.seq h1 (Native.of_exec h2)
  rw [he] at h
  change IRuns I Fin.elim0 (storeExpr reg e dst) s _ _ at h
  apply Native.mono h
  have hx := (e.root_width values).trans hw
  unfold moveCost
  nlinarith [Nat.zero_le (e.size*w*w)]





end KoanaKPaths.Machine.Arithmetic

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix
attribute [local simp] ArrayLookup.DB ArrayLookup.Out ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Wedge.A



lemma queryArray_runs (I : List Sym) (s : IState NS) (arrays : List (List ℤ)) (i : Fin arrays.length)
    (st rest : List Item) (hsource : s.G BitCounter.Source=.int (i.val : ℤ)::st)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hindex : s.G ArrayLookup.Count=[]) (hback : s.G ArrayLookup.Back=[])
    (htmp : s.G ArrayLookup.Tmp=[]) (hdb : s.G ArrayLookup.DB=ArrayLookup.frames arrays++rest) :
    IRuns I Fin.elim0 queryArray s
      ((s.upd BitCounter.Source st).upd Wedge.A (arrays[i].map Item.int ++ .mark::s.G Wedge.A))
      (1100*(i.val+1)+ArrayLookup.lookupCost (arrays.take i.val) arrays[i]+
        moveIntsCost arrays[i].reverse+3) := by
  let a := arrays[i]
  let s0 := (s.upd BitCounter.Source st).upd BitCounter.Count (List.replicate i.val .mark)
  let s1 := (s0.upd BitCounter.Count []).upd ArrayLookup.Count (List.replicate i.val .mark)
  let s2 := s1.upd ArrayLookup.Out (.mark::s.G ArrayLookup.Out)
  let s3 := s2.upd ArrayLookup.Out (a.reverse.map Item.int ++ .mark::s.G ArrayLookup.Out)
  let s4 := s3.upd Wedge.A (.mark::s.G Wedge.A)
  let s5 := (s4.upd ArrayLookup.Out (.mark::s.G ArrayLookup.Out)).upd Wedge.A
    (a.map Item.int ++ .mark::s.G Wedge.A)
  let s6 := s5.upd ArrayLookup.Out (s.G ArrayLookup.Out)
  let s7 := s6.upd ArrayLookup.Count []
  have h0 : IRuns I Fin.elim0 BitCounter.toMarks s s0 (1000*(i.val+1)) := by
    simpa only [hc,List.append_nil] using BitCounter.toMarks_runs I s i.val st hsource (by simp [hc,cls]) ht
  have h1 : IExec I Fin.elim0 (moveMarks BitCounter.Count ArrayLookup.Count) s0 s1 (32*i.val+30) := by
    have h := moveMarks_exec I BitCounter.Count ArrayLookup.Count (by decide) s0 i.val []
      (by simp [cls]) (by simp [s0])
    simpa [s1,s0,hindex] using h
  have h2 : IExec I Fin.elim0 (.op (.mark ArrayLookup.Out)) s1 s2 1 := by
    simpa [s2,s1,s0] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.mark (s := s1) (i := ArrayLookup.Out)))
  have h3 : IExec I Fin.elim0 ArrayLookup.program s2 s3 (ArrayLookup.lookupCost (arrays.take i.val) a) := by
    have h := ArrayLookup.selected_exec I s2 arrays i rest [] (by simp [cls])
      (by simp [s2,s1]) (by simp [s2,s1,s0,hdb]) (by simp [s2,s1,s0,hback]) (by simp [s2,s1,s0,htmp])
    simpa [s3,s2,s1,s0,a] using h
  have h4 : IExec I Fin.elim0 (.op (.mark Wedge.A)) s3 s4 1 := by
    simpa [s4,s3,s2,s1,s0] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.mark (s := s3) (i := Wedge.A)))
  have h5 : IExec I Fin.elim0 (moveInts ArrayLookup.Out Wedge.A) s4 s5 (moveIntsCost a.reverse) := by
    have h := moveInts_exec I ArrayLookup.Out Wedge.A (by decide) s4 a.reverse (.mark::s.G ArrayLookup.Out)
      (by simp [cls]) (by simp [s4,s3])
    simpa [s5,s4,s3,s2,s1,s0] using h
  have h6 : IExec I Fin.elim0 (.op (.unmark ArrayLookup.Out)) s5 s6 1 := .op (.unmark (by simp [s5]))
  have h7 : IExec I Fin.elim0 (clearMarks ArrayLookup.Count) s6 s7 (31*i.val+30) :=
    clearMarks_exec I ArrayLookup.Count s6 i.val [] (by simp [cls]) (by simp [s6,s5,s4,s3,s2,s1])
  have he : s7=(s.upd BitCounter.Source st).upd Wedge.A (a.map Item.int ++ .mark::s.G Wedge.A) := by
    apply itemState_ext
    · intro r
      by_cases hS : r=BitCounter.Source
      · subst r; simp [s7,s6,s5,s4,s3,s2,s1,s0]
      by_cases hC : r=BitCounter.Count
      · subst r; simp [s7,s6,s5,s4,s3,s2,s1,s0,hc]
      by_cases hI : r=ArrayLookup.Count
      · subst r; simp [s7,s6,s5,s4,s3,s2,s1,s0,hindex]
      by_cases hO : r=ArrayLookup.Out
      · subst r; simp [s7,s6,s5,s4,s3,s2,s1,s0]
      by_cases hA : r=Wedge.A
      · subst r; simp [s7,s6,s5,s4,s3,s2,s1,s0]
      simp [s7,s6,s5,s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hS,hC,hI,hO,hA]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq (Native.of_exec h3) (Native.seq (Native.of_exec h4)
      (Native.seq (Native.of_exec h5) (Native.seq (Native.of_exec h6) (Native.of_exec h7)))))))
  rw [he] at h
  change IRuns I Fin.elim0 queryArray s _ _ at h
  apply Native.mono h
  dsimp only [a]
  omega

lemma queryArray_cost (arrays : List (List ℤ)) (i : Fin arrays.length) (k w : ℕ)
    (hl : ∀ a∈arrays, a.length≤2^k) (hw : ∀ a∈arrays, ∀ x∈a, zsz x≤ w) :
    1100*(i.val+1)+ArrayLookup.lookupCost (arrays.take i.val) arrays[i]+
        moveIntsCost arrays[i].reverse+3≤10000*(w+1)*2^k*(arrays.length+1) := by
  have hi : arrays[i]∈arrays := List.getElem_mem _
  have hp := ArrayLookup.lookupCost_power_bound (arrays.take i.val) arrays[i] k w
    (fun a ha => hl a (List.mem_of_mem_take ha)) (fun a ha => hw a (List.mem_of_mem_take ha)) (hl _ hi) (hw _ hi)
  have hm := Wedge.moveIntsCost_bound arrays[i].reverse w (by simpa using hw _ hi)
  have hlen : (arrays.take i.val).length≤ i.val := List.length_take_le _ _
  have htarget : arrays[i].reverse.length≤2^k := by simpa using hl _ hi
  have hpow : 1≤2^k := Nat.one_le_pow k 2 (by omega)
  have hprod : 1≤(w+1)*2^k := Nat.mul_le_mul (by omega : 1≤ w+1) hpow
  nlinarith [i.isLt,Nat.mul_le_mul_right i.val hprod,
    Nat.mul_le_mul_left (200*(w+1)) htarget]

end KoanaKPaths.Machine.Matrix

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix
open Arithmetic Square
attribute [local simp] ArrayLookup.DB ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Wedge.A
variable {v : ℕ}



lemma readArray_runs (I : List Sym) (reg : Fin v→Fin NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (arrays : List (List ℤ)) (k w : ℕ)
    (he : e.width values≤ w) (hj : e.eval values< arrays.length)
    (hl : ∀ a∈arrays, a.length≤2^k) (hw : ∀ a∈arrays, ∀ x∈a, zsz x≤ w)
    (s : IState NS) (rest : List Item)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hi : s.G ArrayLookup.Count=[]) (hb : s.G ArrayLookup.Back=[])
    (htmp : s.G ArrayLookup.Tmp=[]) (hdb : s.G ArrayLookup.DB=ArrayLookup.frames arrays++rest) :
    IRuns I Fin.elim0 (readArray reg e) s
      (s.upd Wedge.A ((arrays[e.eval values]'hj).map Item.int ++ .mark::s.G Wedge.A))
      (11000*(e.size+1)*(w+1)^2+10000*(w+1)*2^k*(arrays.length+1)) := by
  let idx : Fin arrays.length := ⟨e.eval values,hj⟩
  let s0 := s.upd BitCounter.Source (.int (idx.val : ℤ)::s.G BitCounter.Source)
  have h0 : IRuns I Fin.elim0 (storeExpr reg e BitCounter.Source) s s0 (11000*(e.size+1)*(w+1)^2) :=
    storeExpr_runs I reg hreg values e w he BitCounter.Source (by decide) s hv
  have h1 := queryArray_runs I s0 arrays idx (s.G BitCounter.Source) rest
    (by simp [s0]) (by simp [s0,hc]) (by simp [s0,ht]) (by simp [s0,hi])
    (by simp [s0,hb]) (by simp [s0,htmp]) (by simp [s0,hdb])
  have hpost : (s0.upd BitCounter.Source (s.G BitCounter.Source)).upd Wedge.A
      (arrays[idx].map Item.int ++ .mark::s0.G Wedge.A)=
      s.upd Wedge.A ((arrays[e.eval values]'hj).map Item.int ++ .mark::s.G Wedge.A) := by
    simp [s0,idx]
  rw [hpost] at h1
  have h := Native.seq h0 h1
  apply Native.mono h
  have hc := queryArray_cost arrays idx k w hl hw
  omega

end KoanaKPaths.Machine.Matrix

end
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square



attribute [local simp] Predecessor LayerIndex PreviousState Vertex StateIndex GraphArray.Sign
  Wedge.A Accumulate.Acc Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp
  SignLookup.Out ArrayLookup.DB ArrayLookup.Count ArrayLookup.Back ArrayLookup.Tmp BitCounter.Count BitCounter.Tmp












lemma predExpr_eval (k u b : ℕ) : predExpr.eval (predValues k u b)=u*k+b := rfl
lemma laterExpr_eval (n k v a i b : ℕ) : laterExpr.eval (laterValues n k v a i b)=laterIndex n k v a i b := by
  change n*k+(k*n+(i*(k*(k*n))+(a*(k*n)+(b*n+v))))= _
  unfold laterIndex
  omega
lemma predRegs_ne (j : Fin 3) : predRegs j≠Eval := by fin_cases j <;> decide
lemma laterRegs_ne (j : Fin 6) : laterRegs j≠Eval := by fin_cases j <;> decide



lemma predecessorCell_runs (I : List Sym) (s : IState NS) (arrays : List (List ℤ)) (ss ys : List ℤ)
    (n k v a i u b w : ℕ) (nt kt vt atail it ut bt tt matrixTail signTail accTail : List Item)
    (hN : s.G 53=.int (n : ℤ)::nt) (hK : s.G 54=.int (k : ℤ)::kt)
    (hV : s.G Vertex=.int (v : ℤ)::vt) (hA : s.G StateIndex=.int (a : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i : ℤ)::it) (hU : s.G Predecessor=.int (u : ℤ)::ut)
    (hB : s.G PreviousState=.int (b : ℤ)::bt) (hT : s.G Total=.int (ss.length : ℤ)::tt)
    (hMatrix : s.G ArrayLookup.DB=ArrayLookup.frames arrays++matrixTail)
    (hSigns : s.G SignDB=signItems ss++signTail)
    (hAcc : s.G Accumulate.Acc=ys.map Item.int ++ .mark::accTail)
    (hbc : s.G BitCounter.Count=[]) (hbt : s.G BitCounter.Tmp=[])
    (hmc : s.G ArrayLookup.Count=[]) (hmb : s.G ArrayLookup.Back=[]) (hmt : s.G ArrayLookup.Tmp=[])
    (hsc : s.G SignLookup.Count=[]) (hsb : s.G SignLookup.Back=[]) (hst : s.G SignLookup.Tmp=[])
    (hss : ∀ x∈ss, x=1 ∨ x= -1) (hw : 1≤ w)
    (hPredWidth : predExpr.width (predValues k u b)≤ w)
    (hLaterWidth : laterExpr.width (laterValues n k v a i b)≤ w)
    (hTw : zsz (ss.length : ℤ)≤ w) (hBw : zsz (b : ℤ)≤ w)
    (hRows : ∀ xs∈arrays, xs.length=2^k) (hWords : ∀ xs∈arrays, ∀ x∈xs, zsz x≤ w)
    (hys : ys.length=2^k) (hyw : ∀ y∈ys, zsz y≤ w)
    (hj : u*k+b< arrays.length) (hzj : laterIndex n k v a i b< ss.length) :
    IRuns I Wedge.prog predecessorCell s
      ((s.upd PreviousState (.int ((b+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
        ((List.zipWith (·+·) ((arrays[u*k+b]'hj).map
          (fun x => ss[laterIndex n k v a i b]'hzj*x)) ys).map Item.int ++ .mark::accTail))
      (predecessorCellCost arrays.length ss.length k w) := by
  let arr := arrays[u*k+b]'hj
  let z := ss[laterIndex n k v a i b]'hzj
  let sum := List.zipWith (·+·) (arr.map (fun x => z*x)) ys
  let s0 := s.upd Wedge.A (arr.map Item.int ++ .mark::s.G Wedge.A)
  let s1 := s0.upd GraphArray.Sign (.int z::s.G GraphArray.Sign)
  let s2 := s.upd Accumulate.Acc (sum.map Item.int ++ .mark::accTail)
  let s3 := s2.upd PreviousState (.int ((b+1 : ℕ) : ℤ)::bt)
  have hvalsP : ∀ j, ∃ tail, s.G (predRegs j)=.int (predValues k u b j : ℤ)::tail := by
    intro j
    fin_cases j
    · exact ⟨kt,hK⟩
    · exact ⟨ut,hU⟩
    · exact ⟨bt,hB⟩
  have h0 : IRuns I Wedge.prog (liftClosed (Matrix.readArray predRegs predExpr)) s s0
      (11000*(predExpr.size+1)*(w+1)^2+10000*(w+1)*2^k*(arrays.length+1)) := by
    have h := liftClosed_runs I Wedge.prog (Matrix.readArray_runs I predRegs predRegs_ne (predValues k u b)
      predExpr arrays k w hPredWidth (by simpa only [predExpr_eval] using hj)
      (fun xs hx => Nat.le_of_eq (hRows xs hx)) hWords s matrixTail hvalsP hbc hbt hmc hmb hmt hMatrix)
    simpa only [predExpr_eval] using h
  have hvalsL : ∀ j, ∃ tail, s0.G (laterRegs j)=.int (laterValues n k v a i b j : ℤ)::tail := by
    intro j
    fin_cases j
    · exact ⟨nt,by simp [s0,laterRegs,laterValues,hN]⟩
    · exact ⟨kt,by simp [s0,laterRegs,laterValues,hK]⟩
    · exact ⟨vt,by simp [s0,laterRegs,laterValues,hV]⟩
    · exact ⟨atail,by simp [s0,laterRegs,laterValues,hA]⟩
    · exact ⟨it,by simp [s0,laterRegs,laterValues,hI]⟩
    · exact ⟨bt,by simp [s0,laterRegs,laterValues,hB]⟩
  have h1 : IRuns I Wedge.prog (liftClosed (readSign laterRegs laterExpr)) s0 s1
      (30000*(laterExpr.size+2)*(w+1)^2+10000*(ss.length+1)) := by
    have h := liftClosed_runs I Wedge.prog (readSign_runs I laterRegs laterRegs_ne (laterValues n k v a i b)
      laterExpr ss w hw hLaterWidth hTw (by simpa [laterExpr_eval,s1,s0,z,IState.upd] using hzj) s0 tt signTail
      (by simp [s0,hT]) hvalsL (by simp [s0,hbc]) (by simp [s0,hbt])
      (by simp [s0,hsc]) (by simp [s0,hsb]) (by simp [s0,hst]) (by simp [s0,hSigns]) hss)
    simpa [laterExpr_eval,s1,s0,z,IState.upd] using h
  have hlen : arr.length=ys.length := (hRows arr (List.getElem_mem _)).trans hys.symm
  have h2 : IRuns I Wedge.prog GraphArray.weightedAdd s1 s2 (10000*(w+2)*(arr.length+1)) := by
    have h := GraphArray.weightedAdd_runs I s1 z arr ys (s.G Wedge.A) accTail (s.G GraphArray.Sign)
      (hss z (List.getElem_mem _)) hlen (by simp [s1]) (by simp [s1,s0]) (by simp [s1,s0,hAcc])
      w (hWords arr (List.getElem_mem _)) hyw
    have hpost : ((s1.upd Wedge.A (s.G Wedge.A)).upd GraphArray.Sign (s.G GraphArray.Sign)).upd Accumulate.Acc
        (sum.map Item.int ++ .mark::accTail)=s2 := by
      apply itemState_ext
      · intro j
        by_cases h0 : j=0
        · subst j; simp [s2,s1,s0,IState.upd]
        by_cases h25 : j=25
        · subst j; simp [s2,s1,s0,IState.upd]
        by_cases h20 : j=20
        · subst j; simp [s2,s1,s0,IState.upd]
        simp [s2,s1,s0,IState.upd,Function.update_apply,h0,h25,h20]
      · rfl
      · rfl
    rw [hpost] at h
    exact h
  have h3 : IRuns I Wedge.prog (liftClosed (increment PreviousState)) s2 s3 (13000*(w+1)^2) :=
    liftClosed_runs I Wedge.prog (increment_runs I PreviousState (by decide) s2 b w bt (by simp [s2,hB]) hw hBw)
  have hpost : s3=(s.upd PreviousState (.int ((b+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
      (sum.map Item.int ++ .mark::accTail) := by
    apply itemState_ext
    · intro j
      by_cases hB : j=PreviousState
      · subst j; simp [s3,s2]
      by_cases hA : j=Accumulate.Acc
      · subst j; simp [s3,s2]
      simp [s3,s2,IState.upd,Function.update_apply,hB,hA]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq h1 (Native.seq h2 h3))
  rw [hpost] at h
  change IRuns I Wedge.prog predecessorCell s _ _ at h
  apply Native.mono h
  have hp : predExpr.size=5 := rfl
  have hl : laterExpr.size=27 := rfl
  have hArr : arr.length=2^k := hRows arr (List.getElem_mem _)
  rw [hp,hl,hArr]
  unfold predecessorCellCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (arrays : List.{0} (List.{0} Int))
  (ss ys : List.{0} Int) (n k v a i u b w : Nat)
  (nt kt vt atail it ut bt tt matrixTail signTail accTail : List.{0} NLogN.Item)
  (hN :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 53)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 53))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) nt))
  (hK :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 54))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt))
  (hV :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt v)) vt))
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt a)) atail))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt i)) it))
  (hU :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt u)) ut))
  (hB :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousState)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt b)) bt))
  (hT :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int ss))) tt))
  (hMatrix :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.ArrayLookup.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames arrays) matrixTail))
  (hSigns :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems ss) signTail))
  (hAcc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail)))
  (hbc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (hbt :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hmc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.ArrayLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hmb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.ArrayLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (hmt :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.ArrayLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hsc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hsb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (hst :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hss :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) ss x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hPredWidth :
    @LE.le.{0} Nat instLENat
      (@KoanaKPaths.Machine.Arithmetic.Expr.width (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (KoanaKPaths.Machine.Trial.predValues k u b) KoanaKPaths.Machine.Trial.predExpr)
      w)
  (hLaterWidth :
    @LE.le.{0} Nat instLENat
      (@KoanaKPaths.Machine.Arithmetic.Expr.width (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (KoanaKPaths.Machine.Trial.laterValues n k v a i b) KoanaKPaths.Machine.Trial.laterExpr)
      w)
  (hTw : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int ss))) w)
  (hBw : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt b)) w)
  (hRows :
    ∀ (xs : List.{0} Int),
      @Membership.mem.{0, 0} (List.{0} Int) (List.{0} (List.{0} Int)) (@List.instMembership.{0} (List.{0} Int)) arrays
          xs →
        @Eq.{1} Nat (@List.length.{0} Int xs)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
  (hWords :
    ∀ (xs : List.{0} Int),
      @Membership.mem.{0, 0} (List.{0} Int) (List.{0} (List.{0} Int)) (@List.instMembership.{0} (List.{0} Int)) arrays
          xs →
        ∀ (x : Int),
          @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
            @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (hys :
    @Eq.{1} Nat (@List.length.{0} Int ys)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
  (hyw :
    ∀ (y : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) ys y →
        @LE.le.{0} Nat instLENat (NLogN.zsz y) w)
  (hj :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) u k) b)
      (@List.length.{0} (List.{0} Int) arrays))
  (hzj : @LT.lt.{0} Nat instLTNat (KoanaKPaths.Machine.Trial.laterIndex n k v a i b) (@List.length.{0} Int ss)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.predecessorCell s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousState
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          bt))
      KoanaKPaths.Machine.Accumulate.Acc
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.zipWith.{0, 0, 0} Int Int Int
            (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2)
            (@List.map.{0, 0} Int Int
              (fun (x : Int) =>
                @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
                    (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
                    (@List.instGetElemNatLtLength.{0} Int) ss (KoanaKPaths.Machine.Trial.laterIndex n k v a i b) hzj)
                  x)
              (@GetElem.getElem.{0, 0, 0} (List.{0} (List.{0} Int)) Nat (List.{0} Int)
                (fun (as : List.{0} (List.{0} Int)) (i : Nat) =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} (List.{0} Int) as))
                (@List.instGetElemNatLtLength.{0} (List.{0} Int)) arrays
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) u k) b)
                hj))
            ys))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail)))
    (KoanaKPaths.Machine.Trial.predecessorCellCost (@List.length.{0} (List.{0} Int) arrays) (@List.length.{0} Int ss) k
      w) := by
  exact @KoanaKPaths.Machine.Trial.predecessorCell_runs

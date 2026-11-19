-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.terminalCell_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:00:40.533417+00:00
-- url     : https://prove2.me/submissions/2aa4dc45-f899-491e-966b-73319bca2bf9

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
import Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_program_exec
import Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_zipAddInts_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
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

set_option maxHeartbeats 400000
open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates


























lemma subsetOrder_length (k : ℕ) : (subsetOrder k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [subsetOrder,ih,pow_succ]; omega







lemma coefficientList_length {k : ℕ} (A : Coordinates k) : (coefficientList A).length = 2^k := by
  simp [coefficientList,subsetOrder_length]



lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all

















lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl











end KoanaKPaths.ExteriorCoordinates

end
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤ w) (hy : zsz y≤ w) : zsz (x+y)≤ w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega





lemma zipWith_all {α β γ : Type} (f : α → β → γ) (P : γ → Prop) (xs : List α) (ys : List β)
    (h : ∀ x∈xs, ∀ y∈ys, P (f x y)) : ∀ z∈List.zipWith f xs ys, P z := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro z hz
      simp only [List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact h x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) z hz



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



lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

lemma zipAddIntsCost_bound (xs ys : List ℤ) (w : ℕ)
    (hx : ∀ z∈xs, zsz z≤ w) (hy : ∀ z∈ys, zsz z≤ w) :
    zipAddIntsCost xs ys ≤ 1000*(w+1)*(xs.length+1) := by
  have ha : ∀ z∈List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys,
      z≤594*w+423 := by
    apply zipWith_all
    intro x hxm y hym
    rw [addIntCost_formula]
    have hx' := hx x hxm
    have hy' := hy y hym
    omega
  have hs := sum_map_le_mul id
    (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys) (594*w+423) ha
  simp only [List.map_id_fun,id_eq,List.map_id] at hs
  have hl : (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys).length≤ xs.length := by
    simp [List.length_zipWith]
  unfold zipAddIntsCost
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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

lemma moveIntsCost_reverse (xs : List ℤ) : moveIntsCost xs.reverse=moveIntsCost xs := by
  simp [moveIntsCost,List.map_reverse]





end KoanaKPaths.Machine

end
section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates














lemma denseLayer_length {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) :
    (denseLayer arcs σ R p v a).length=2^k := by
  rw [denseLayer_correct]
  exact coefficientList_length _







end KoanaKPaths.Main

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

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma natAbs_sum_le {α : Type} (s : Finset α) (f : α→ℤ) :
    (∑ x∈s, f x).natAbs ≤ ∑ x∈s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)












lemma layerRadius_le_exp (n k ℓ : ℕ) : layerRadius n k ℓ≤2^(n+k+ℓ+3) := by
  have hp : layerRadius n k ℓ≤(n+1)*(k+1)*(ℓ+1) := by
    unfold layerRadius
    nlinarith [Nat.zero_le (n*k),Nat.zero_le (n*ℓ),Nat.zero_le (k*ℓ)]
  have hn : n+1≤2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k+1≤2^(k+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hl : ℓ+1≤2^(ℓ+1) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (n+1)*(k+1)*(ℓ+1) := hp
    _ ≤ 2^(n+1)*2^(k+1)*2^(ℓ+1) := Nat.mul_le_mul (Nat.mul_le_mul hn hk) hl
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega

lemma graphLayer_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) (S : Finset (Fin k)) :
    NLogN.zsz (graphLayer arcs σ R p v a S)≤(n+k+ℓ+3)*p+1 := by
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k ℓ) p
  rw [← pow_mul] at hr
  have h := (graphLayer_natAbs arcs σ R p v a S).trans hr
  have hp : 0<2^((n+k+ℓ+3)*p) := by positivity
  rw [pow_succ]
  omega



end KoanaKPaths.Main

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls







lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self








end KoanaKPaths.Machine.Controls

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main



lemma wordWidth_pos (n k : ℕ) : 1≤ wordWidth n k := by
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]











end KoanaKPaths.Machine.Trial

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main



lemma matrixArrays_length {n k : ℕ} (F : Fin n→Fin k→List ℤ) :
    (matrixArrays F).length=n*k := by simp [matrixArrays]

lemma matrixArrays_get {n k : ℕ} (F : Fin n→Fin k→List ℤ) (v : Fin n) (a : Fin k) :
    (matrixArrays F)[(finProdFinEquiv (v,a)).val]'(by simp [matrixArrays]; exact (finProdFinEquiv (v,a)).isLt)=F v a := by
  unfold matrixArrays
  rw [List.getElem_ofFn]
  change F (finProdFinEquiv.symm (finProdFinEquiv (v,a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (v,a))).2=F v a
  rw [Equiv.symm_apply_apply]



lemma matrixArrays_bounds {n k : ℕ} (F : Fin n→Fin k→List ℤ) (P w : ℕ)
    (hl : ∀ v a, (F v a).length≤ P) (hw : ∀ v a, ∀ x∈F v a, NLogN.zsz x≤ w) :
    (∀ A∈matrixArrays F, A.length≤ P) ∧
      (∀ A∈matrixArrays F, ∀ x∈A, NLogN.zsz x≤ w) := by
  constructor
  · intro A hA
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hA
    rw [← hi]
    exact hl _ _
  · intro A hA
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hA
    rw [← hi]
    exact hw _ _

end KoanaKPaths.Main

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

lemma denseLayer_word_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k+1) (v : Fin n) (a : Fin k) :
    ∀ x∈denseLayer arcs σ R p v a, zsz x≤ wordWidth n k := by
  intro x hx
  rw [denseLayer_correct] at hx
  obtain ⟨S,_,rfl⟩ := List.mem_map.mp hx
  have h := graphLayer_width arcs σ R p v a S
  have hmul := Nat.mul_le_mul_left (n+k+k+3) hp
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]

lemma denseMatrix_word_bounds {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k+1) :
    (∀ A∈matrixArrays (denseLayer arcs σ R p), A.length≤2^k) ∧
    (∀ A∈matrixArrays (denseLayer arcs σ R p), ∀ x∈A, zsz x≤ wordWidth n k) := by
  exact matrixArrays_bounds (denseLayer arcs σ R p) (2^k) (wordWidth n k)
    (fun v a => Nat.le_of_eq (denseLayer_length arcs σ R p v a)) (denseLayer_word_width arcs σ R p hp)

end KoanaKPaths.Machine.Trial

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Accumulate




attribute [local simp] Src Acc Tmp Wedge.A



lemma program_exec (I : List Sym) (s : IState NS) (xs ys : List ℤ) (st atail : List Item)
    (hlen : xs.length=ys.length)
    (hs : s.G Src=xs.map Item.int ++ .mark::st) (ha : s.G Acc=ys.map Item.int ++ .mark::atail) :
    IExec I Fin.elim0 program s
      ((s.upd Src st).upd Acc ((List.zipWith (·+·) xs ys).map Item.int ++ .mark::atail))
      (zipAddIntsCost xs ys+moveIntsCost (List.zipWith (·+·) xs ys)+5) := by
  let sum := List.zipWith (·+·) xs ys
  let s1 := s.upd Tmp (.mark::s.G Tmp)
  let s2 := ((s1.upd Src (.mark::st)).upd Acc (.mark::atail)).upd Tmp (sum.reverse.map Item.int ++ s1.G Tmp)
  let s3 := s2.upd Src st
  let s4 := s3.upd Acc atail
  let s5 := s4.upd Acc (.mark::atail)
  let s6 := (s5.upd Tmp (.mark::s.G Tmp)).upd Acc (sum.reverse.reverse.map Item.int ++ s5.G Acc)
  let s7 := s6.upd Tmp (s.G Tmp)
  have h1 : IExec I Fin.elim0 (.op (.mark Tmp)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (zipAddInts Src Acc Tmp) s1 s2 (zipAddIntsCost xs ys) :=
    zipAddInts_exec I Src Acc Tmp (by decide) (by decide) (by decide) s1 xs ys (.mark::st) (.mark::atail)
      (by simp [cls]) hlen (by simp [s1,hs]) (by simp [s1,ha])
  have h3 : IExec I Fin.elim0 (.op (.unmark Src)) s2 s3 1 := by exact .op (.unmark (by simp [s2]))
  have h4 : IExec I Fin.elim0 (.op (.unmark Acc)) s3 s4 1 := by exact .op (.unmark (by simp [s3,s2]))
  have h5 : IExec I Fin.elim0 (.op (.mark Acc)) s4 s5 1 := by
    simpa only [s5,s4,upd_G_self,upd_upd] using
      (IExec.op (IOp.Step.mark (s := s4) (i := Acc)) : IExec I Fin.elim0 _ _ _ 1)
  have h6 : IExec I Fin.elim0 (moveInts Tmp Acc) s5 s6 (moveIntsCost sum.reverse) :=
    moveInts_exec I Tmp Acc (by decide) s5 sum.reverse (.mark::s.G Tmp) (by simp [cls])
      (by simp [s5,s4,s3,s2,s1])
  have h7 : IExec I Fin.elim0 (.op (.unmark Tmp)) s6 s7 1 := by exact .op (.unmark (by simp [s6]))
  have he : s7=(s.upd Src st).upd Acc (sum.map Item.int ++ .mark::atail) := by
    cases s
    simp only [s7,s6,s5,s4,s3,s2,s1,IState.upd]
    congr 1
    funext i
    by_cases hS : i=Src <;> by_cases hA : i=Acc <;> by_cases hT : i=Tmp <;> simp_all
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 (IExec.seq h6 h7)))))
  change IExec I Fin.elim0 program s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1
  rw [moveIntsCost_reverse]
  dsimp only [sum]
  omega

end KoanaKPaths.Machine.Accumulate

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








end KoanaKPaths.Machine.Trial

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main








lemma Core.at {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∈coreRegisters) : s.G j=coreStack ω arcs p j := h j hj

end KoanaKPaths.Machine.Trial

end
section

set_option autoImplicit false
open scoped BigOperators
namespace KoanaKPaths.Main
universe u
variable {M : Type u} [AddCommMonoid M] {m : ℕ}







lemma finPrefix_succ (f : Fin m→M) (i : ℕ) (hi : i< m) :
    finPrefix f (i+1)=finPrefix f i+f ⟨i,hi⟩ := by
  classical
  have hset : Finset.univ.filter (fun j : Fin m => j.val< i+1)=
      insert ⟨i,hi⟩ (Finset.univ.filter (fun j : Fin m => j.val< i)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j.val=i
      · exact Or.inl (Fin.ext hj)
      · exact Or.inr (by omega)
    · rintro (rfl|h)
      · change i< i+1
        omega
      · omega
  have hnot : (⟨i,hi⟩ : Fin m)∉Finset.univ.filter (fun j : Fin m => j.val< i) := by simp
  simp only [finPrefix,hset,Finset.sum_insert hnot]
  exact add_comm _ _

end KoanaKPaths.Main

end
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

lemma pred_word_width {n k : ℕ} (u : Fin n) (b : Fin k) :
    predExpr.width (predValues k u.val b.val)≤ wordWidth n k := by
  have hk := Controls.zsz_nat_le k
  have hu := Controls.zsz_nat_le u.val
  have hb := Controls.zsz_nat_le b.val
  have hatom : predExpr.atomWidth (predValues k u.val b.val)≤1+n+k := by
    change max (max (zsz (u.val : ℤ)) (zsz (k : ℤ))) (zsz (b.val : ℤ))≤1+n+k
    omega
  have h := predExpr.width_le (predValues k u.val b.val) (1+n+k) hatom
  have hs : predExpr.size=5 := rfl
  rw [hs] at h
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]







end KoanaKPaths.Machine.Trial

end
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates



lemma terminalPrefix_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (a : Fin k) (u : ℕ) :
    ∀ x∈coefficientList (terminalPrefix arcs σ R a u), zsz x≤ Machine.Trial.wordWidth n k := by
  intro x hx
  obtain ⟨S,_,rfl⟩ := List.mem_map.mp hx
  let Q := Finset.univ.filter (fun v : Fin n => v.val< u)
  have h : (terminalPrefix arcs σ R a u S).natAbs≤ n*(layerRadius n k k)^k := by
    calc
      _ ≤ ∑ v∈Q, (graphLayer arcs σ R k v a S).natAbs := by
        simp only [terminalPrefix,finPrefix,Finset.sum_apply]
        exact natAbs_sum_le Q _
      _ ≤ ∑ _v∈Q, (layerRadius n k k)^k := Finset.sum_le_sum (fun v _ => graphLayer_natAbs arcs σ R k v a S)
      _ = Q.card*(layerRadius n k k)^k := by simp
      _ ≤ n*(layerRadius n k k)^k := Nat.mul_le_mul_right _ (by simpa using Q.card_le_univ)
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k k) k
  rw [←pow_mul] at hr
  have hn : n≤2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hh := h.trans (Nat.mul_le_mul hn hr)
  rw [←pow_add] at hh
  have hw : zsz (terminalPrefix arcs σ R a u S)≤ n+(n+k+k+3)*k+1 := by
    apply (Machine.Wedge.zsz_le_iff _ _).mpr
    rw [pow_succ]
    have hp : 0<2^(n+(n+k+k+3)*k) := by positivity
    omega
  unfold Machine.Trial.wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]







end KoanaKPaths.Main

end
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] Predecessor StateIndex Vertex Accumulate.Acc Accumulate.Src Wedge.A


lemma terminalRegs_ne (j : Fin 3) : terminalRegs j≠Square.Eval := by fin_cases j <;> decide





lemma terminalCell_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (a : Fin k) (u : Fin n)
    (atail ut accTail : List Item) (hCore : Core s ω arcs k)
    (hA : s.G StateIndex=.int (a.val : ℤ)::atail) (hU : s.G Predecessor=.int (u.val : ℤ)::ut)
    (hAcc : s.G Accumulate.Acc=(coefficientList
      (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a u.val)).map Item.int ++ .mark::accTail) :
    IRuns I Wedge.prog terminalCell s
      ((s.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)).upd Accumulate.Acc
        ((coefficientList (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a (u.val+1))).map Item.int ++ .mark::accTail))
      (terminalCellCost n k) := by
  let F := denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k
  let arrays := matrixArrays F
  let xs := coefficientList (graphLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k u a)
  let ys := coefficientList (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a u.val)
  let zs := List.zipWith (·+·) xs ys
  let s0 := s.upd Wedge.A (xs.map Item.int ++ .mark::s.G Wedge.A)
  let s1 := s.upd Accumulate.Acc (zs.map Item.int ++ .mark::accTail)
  let s2 := s1.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)
  have hj : u.val*k+a.val< arrays.length := by
    rw [matrixArrays_length]
    have hh := (finProdFinEquiv (u,a)).isLt
    change a.val+k*u.val< n*k at hh
    nlinarith
  have harr : arrays[u.val*k+a.val]'hj=xs := by
    have hh := matrixArrays_get F u a
    have hi : (finProdFinEquiv (u,a)).val=u.val*k+a.val := by change a.val+k*u.val=_; ring
    simpa only [hi] using hh.trans (denseLayer_correct _ _ _ _ _ _)
  have hbnd := denseMatrix_word_bounds arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k (by omega)
  have h0 : IRuns I Wedge.prog (liftClosed (Matrix.readArray terminalRegs predExpr)) s s0
      (66000*(wordWidth n k+1)^2+10000*(wordWidth n k+1)*2^k*(n*k+1)) := by
    have h := liftClosed_runs I Wedge.prog (Matrix.readArray_runs I terminalRegs terminalRegs_ne (predValues k u.val a.val)
      predExpr arrays k (wordWidth n k) (pred_word_width u a) hj hbnd.1 hbnd.2 s []
      (by intro j; fin_cases j
          · exact ⟨[],by simpa [terminalRegs,predValues,coreStack,NS,Wedge.NS] using hCore.at 54 (by decide)⟩
          · exact ⟨ut,hU⟩
          · exact ⟨atail,hA⟩)
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 40 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 41 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 17 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 18 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 19 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 14 (by decide)))
    simpa only [predExpr_eval,harr,arrays,matrixArrays_length,show predExpr.size=5 from rfl,show (11000*(5+1) : ℕ)=66000 from rfl] using h
  have hx : ∀ x∈xs, zsz x≤ wordWidth n k := by
    simpa [xs,←denseLayer_correct] using denseLayer_word_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k (by omega) u a
  have hy := terminalPrefix_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a u.val
  have hlen : xs.length=ys.length := by simp [xs,ys,coefficientList_length]
  have h1 : IRuns I Wedge.prog (liftClosed Accumulate.program) s0 s1 (10000*(wordWidth n k+2)*(2^k+1)) := by
    have h := liftClosed_exec I Wedge.prog (Accumulate.program_exec I s0 xs ys (s.G Wedge.A) accTail hlen
      (by simp [s0]) (by simp [s0,ys,hAcc]))
    have he : (s0.upd Accumulate.Src (s.G Wedge.A)).upd Accumulate.Acc (zs.map Item.int ++ .mark::accTail)=s1 := by
      simp [s1,s0,zs]
    rw [he] at h
    apply Native.mono (Native.of_exec h)
    have hz : ∀ z∈zs, zsz z≤ wordWidth n k+1 :=
      Wedge.zipWith_all _ _ xs ys (fun x hx' y hy' => Wedge.zsz_add_le _ _ _ (hx x hx') (hy y hy'))
    have hzip := Wedge.zipAddIntsCost_bound xs ys (wordWidth n k) hx hy
    have hmove := Wedge.moveIntsCost_bound zs (wordWidth n k+1) hz
    have hxlen : xs.length=2^k := coefficientList_length _
    have hzlen : zs.length=2^k := by simp [zs,List.length_zipWith,←hlen,hxlen]
    rw [hxlen] at hzip
    rw [hzlen] at hmove
    nlinarith
  have h2 : IRuns I Wedge.prog (liftClosed (Square.increment Predecessor)) s1 s2 (13000*(wordWidth n k+1)^2) :=
    liftClosed_runs I Wedge.prog (Square.increment_runs I Predecessor (by decide) s1 u.val (wordWidth n k) ut
      (by simp [s1,hU]) (wordWidth_pos n k) (by
        have hu := Controls.zsz_nat_le u.val
        unfold wordWidth; nlinarith [u.isLt,Nat.zero_le (n*n),Nat.zero_le (k*k)]))
  have hz : zs=coefficientList (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a (u.val+1)) := by
    unfold zs xs ys terminalPrefix
    rw [←coefficientList_add,finPrefix_succ _ u.val u.isLt]
    congr 1
    exact add_comm _ _
  have hpost : s2=(s.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)).upd Accumulate.Acc
      ((coefficientList (terminalPrefix arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 a (u.val+1))).map Item.int ++ .mark::accTail) := by
    rw [←hz]
    apply itemState_ext
    · intro r
      by_cases h80 : r=80 <;> by_cases h20 : r=20 <;> simp [s2,s1,IState.upd,Function.update_apply,h80,h20]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq h1 h2)
  rw [hpost] at h
  change IRuns I Wedge.prog terminalCell s _ _ at h
  exact Native.mono h (by unfold terminalCellCost; nlinarith)

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (a : Fin k)
  (u : Fin n) (atail ut accTail : List.{0} NLogN.Item) (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs k)
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val k a))) atail))
  (hU :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n u))) ut))
  (hAcc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.ExteriorCoordinates.coefficientList k
            (@KoanaKPaths.Main.terminalPrefix n k arcs
              (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              a (@Fin.val n u))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail))),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.terminalCell s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n u)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          ut))
      KoanaKPaths.Machine.Accumulate.Acc
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.ExteriorCoordinates.coefficientList k
            (@KoanaKPaths.Main.terminalPrefix n k arcs
              (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n u)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail)))
    (KoanaKPaths.Machine.Trial.terminalCellCost n k) := by
  exact @KoanaKPaths.Machine.Trial.terminalCell_runs

-- Prove2me | solution 1 for OAI.MatchingFPRAS.thm_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:38:08.315809+00:00
-- url     : https://prove2.me/submissions/3d7e48b0-aa7d-40f5-b730-8d7fd2df8b16

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_algorithm_bound
import Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_algorithm_success
import Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_compute_mean

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_GuardMachineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma statementCost_le_programCost [Fintype Λ] (l : Λ) :
    statementCost (M l)≤programCost M := Finset.le_sup (f:=fun l=>statementCost (M l)) (Finset.mem_univ l)
end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_StackCompilerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCost
open Turing Turing.TM2to1 Turing.TM2to1.Λ' MachineCost

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

omit [DecidableEq K] in
lemma accesses_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    accesses (stRun o q)=accesses q+1 := by cases o <;> rfl
variable (M : Λ → TM2.Stmt Γ Λ σ)
lemma go_time {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤S.length) :
    MachineCost.run (TM1.step (tr M)) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩=
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 from rfl,run_add,ih (by omega)]
    simp only [MachineCost.run,advance,TM1.step]
    rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
      stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa using (show n<S.length by omega))]
    simp only [Option.isNone_some,Bool.cond_false,TM1.stepAux,Option.getD_some]
    rw [Function.iterate_succ_apply']
lemma action_bound {S : ∀ k,List (Γ k)} {H : ℕ} (hS : StackBound S H)
    {k : K} (o : StAct K Γ σ k) (v : σ) :
    StackBound (Function.update S k (stWrite v (S k) o)) (H+1) := by
  intro j
  by_cases hj : j=k
  · subst j
    rw [Function.update_self]
    have hk:=hS k
    cases o <;> simp only [stWrite,List.length_cons,List.length_tail] <;> omega
  · rw [Function.update_of_ne hj]
    exact (hS j).trans (by omega)
lemma stepAux_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (H : ℕ) (hS : StackBound S H) : StackBound (TM2.stepAux q v S).stk (H+accesses q) := by
  induction q using stmtStRec generalizing v S H with
  | run k o q ih =>
    rw [step_run,accesses_run]
    have hh:=ih (stVar v (S k) o) _ (H+1) (action_bound hS o v)
    convert hh using 1; omega
  | load a q ih => exact ih (a v) S H hS
  | branch p q r ihq ihr =>
    cases hp:p v
    · simp only [TM2.stepAux,hp,Bool.cond_false,accesses]
      exact fun k=>(ihr v S H hS k).trans (Nat.add_le_add_left (le_max_right _ _) H)
    · simp only [TM2.stepAux,hp,Bool.cond_true,accesses]
      exact fun k=>(ihq v S H hS k).trans (Nat.add_le_add_left (le_max_left _ _) H)
  | goto f => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS
  | halt => simpa only [TM2.stepAux,accesses,Nat.add_zero] using hS

lemma advance_bound (A : ℕ) (hA : ∀ l,accesses (M l)≤A)
    (c : TM2.Cfg Γ Λ σ) (H : ℕ) (hS : StackBound c.stk H) :
    StackBound (advance (TM2.step M) c).stk (H+A) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => exact fun k=>(hS k).trans (Nat.le_add_right H A)
  | some l =>
    have hh:=stepAux_bound (M l) v S H hS
    exact fun k=>(hh k).trans (Nat.add_le_add_left (hA l) H)
end MatchingFPRAS.StackCost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_BoolPostCompiler
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

lemma down_up (b : Bool) : down (up b)=b := by cases b <;> decide
end MatchingFPRAS.BoolPostCompiler

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_SupportedCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SupportedCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma cost_le {l : Λ} (hl : l ∈ S) : statementCost (M l) ≤ cost M S := Finset.le_sup (f:=fun l=>statementCost (M l)) hl
include hS
omit [Inhabited σ] in
lemma advance_supported {c : TM1.Cfg Γ Λ σ} (hc : c.l ∈ S.insertNone) :
    (advance (TM1.step M) c).l ∈ S.insertNone := by
  cases he:TM1.step M c with
  | none => simpa only [advance,he,Option.getD_none] using hc
  | some c' =>
    simpa only [advance,he,Option.getD_some] using TM1.step_supports M hS he hc
end MatchingFPRAS.SupportedCompiler

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_FixedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
lemma injective : Function.Injective (enc Γ) := by
  classical
  intro a b hab
  by_cases ha : a=default
  · by_cases hb : b=default
    · exact ha.trans hb.symm
    · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ b)) hab
      simp [enc,ha,hb] at hh
  · have hh:=congrArg (fun v : List.Vector Bool (Fintype.card Γ)=>v.get (Fintype.equivFin Γ a)) hab
    simp only [enc,List.Vector.get_ofFn] at hh
    have ht : decide (b≠default ∧ Fintype.equivFin Γ b=Fintype.equivFin Γ a)=true := by
      simpa [ha] using hh.symm
    exact ((Fintype.equivFin Γ).injective (of_decide_eq_true ht).2).symm
lemma left_inverse (a : Γ) : dec Γ (enc Γ a)=a :=
  Function.leftInverse_invFun (injective Γ) a
end MatchingFPRAS.FixedEncoding

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_StackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing MachineCost

variable {K : Type*} {Γ : K → Type*}
lemma rows_projection (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (k : K) : (ListBlank.mk (rows S H)).map (proj k)=ListBlank.mk ((S k).map some).reverse := by
  apply ListBlank.ext
  intro i
  rw [ListBlank.nth_map,ListBlank.nth_mk,List.getI_eq_getElem?_getD]
  simp only [rows,List.getElem?_ofFn,proj,PointedMap.mk_val]
  rw [←List.map_reverse,ListBlank.nth_mk,List.getI_eq_getElem?_getD,List.getElem?_map]
  by_cases hi : i<H
  · simp only [hi,Option.getD_some,dite_true]
    cases (S k).reverse[i]? <;> rfl
  · have hlen : (S k).reverse.length ≤ i := by simpa using (hS k).trans (Nat.le_of_not_gt hi)
    simp [hi,List.getElem?_eq_none hlen]
lemma word_blank (S : ∀ k,List (Γ k)) (H : ℕ) :
    ListBlank.mk (word S H)=TM2to1.addBottom (ListBlank.mk (rows S H)) := by
  simp only [word,TM2to1.addBottom,ListBlank.head_mk,ListBlank.tail_mk,
    ListBlank.map_mk]
  exact (ListBlank.cons_mk _ _).symm
lemma unique_rows (S : ∀ k,List (Γ k)) (H : ℕ) (hS : StackCost.StackBound S H)
    (L : ListBlank (∀ k,Option (Γ k)))
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    L=ListBlank.mk (rows S H) := by
  apply ListBlank.ext
  intro i
  funext k
  rw [TM2to1.stk_nth_val i (hL k),TM2to1.stk_nth_val i (rows_projection S H hS k)]
end MatchingFPRAS.StackWords

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SumLiftMate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

 theorem paired_prefix_weight (a : Bool) (xs ys : List ℝ) :
    wordWeight a (duplicate xs ++ ys) = xs.prod * wordWeight a ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

theorem profile_weight (a : Bool) (left right : List ℝ) (lam : ℝ) :
    wordWeight a (duplicate left ++ [lam] ++ duplicate right) =
      left.prod * right.prod * (if a then lam else 1) := by
  rw [List.append_assoc, paired_prefix_weight]
  simp only [List.singleton_append, wordWeight]
  have h := paired_prefix_weight (!a) right []
  simp only [List.append_nil, wordWeight_nil, mul_one] at h
  rw [h]
  ring

theorem wordWeight_ofFn (n : ℕ) (w : Fin n → ℝ) (a : Bool) :
    wordWeight a (List.ofFn w) = ∏ i, (if alternating a i.val then w i else 1) := by
  induction n generalizing a with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [wordWeight, Fin.val_zero, alternating_zero]
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp

 theorem intact_weight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m)
    (h : Valid ∅ b) : selectedWeight w b = wordWeight (b 0) (List.ofFn w) := by
  rw [wordWeight_ofFn]
  unfold selectedWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [(intact_iff b).mp h]

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

 theorem profileActivity_ofFn (p : ℕ) (B Hu Hv lam : ℝ) :
    List.ofFn (profileActivity p B Hu Hv lam) = profile p B Hu Hv lam := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, profileActivity, List.get_eq_getElem, Fin.val_cast]

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
 theorem deletion_weight [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    (∏ e, selectedWeight (w e) (b e)) =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        ∏ e, if extract U b e then lam e else 1 := by
  classical
  unfold deletionConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : (U e).Nonempty
  · have heq := broken_unique he (hb0.1 e) (hb.1 e)
    simp [extract,he,heq]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [extract,he,↓reduceIte]
    rw [intact_weight _ _ (by simpa [he'] using hb.1 e),hw e,profile_weight]

theorem deletion_partition_identity {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    realHolePartition u v m R₀ U w =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        logicalHolePartition u v (residualHoles u v R₀ U base) (broken U) lam := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  let := Fintype.ofFinite {s : E → Bool //
    LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s}
  unfold realHolePartition logicalHolePartition
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (deletionEquiv hm u v R₀ U base hb)
  intro b
  exact deletion_weight u v R₀ U base b.val hb b.property w left right lam hw

end Deletion

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Height
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_mono (r w : E → ℝ) (hr : ∀ e,0 ≤ r e) (hrw : ∀ e,r e≤w e)
    (U : Finset V) : partitionWeight inc r U≤partitionWeight inc w U :=
  Finset.sum_le_sum (fun _ _ => Finset.prod_le_prod (fun e _ => hr e) (fun e _ => hrw e))

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

variable {R s hs}

lemma selection_weight (w : V → V → ℝ) (m : Mate V) :
    (∏ e : LogicalEdge V, if select m e then logicalActivity w e else 1)=weight w m := by
  classical
  unfold weight
  rw [← Finset.prod_filter,← Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => source e)
  · intro e he
    have hh := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hh]
    exact e.property
  · intro e he f hf h
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    have hf' := (select_eq_true m f).mp (Finset.mem_filter.mp hf).2
    exact Subtype.ext (Prod.ext h (he'.symm.trans ((congrArg m.val h).trans hf')))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨⟨(x,m.val x),hx'⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [select,source,target]⟩
  · intro e he
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [logicalActivity,edgeActivity,show source e < target e from e.property,ite_true,he']

lemma asMate_weight (w : V → V → ℝ) :
    (∏ e : LogicalEdge V, if s e then logicalActivity w e else 1)=weight w (asMate R s hs) := by
  rw [← selection_weight,select_asMate]

theorem logical_partition_eq (w : V → V → ℝ) (R : Finset V) :
    logicalHolePartition source target R ∅ (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  let := Fintype.ofFinite {m : Mate V // HasHoles m R}
  unfold logicalHolePartition partition
  rw [Finset.sum_subtype (matchings R) (fun m => mem_matchings m R)]
  apply Fintype.sum_equiv (matchingEquiv R)
  intro s
  exact asMate_weight w

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Representation
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma pathConstant_pos (p : ℕ) (B Hu Hv : ℝ) (hB : 0 < B) :
    0 < pathConstant p B Hu Hv := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i hi <;> exact hB.trans_le (le_max_left _ _)

theorem intact_partition_identity (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition w ∅=0 := by
      simp [partition,Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m,hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles,broken,deletionConstant,List.prod_ofFn,pathConstant,
    logical_partition_eq] using hid

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

omit [DecidableEq E] in
lemma selectedSet_weight (w : E → Fin (m+1) → ℝ) (b : E → Selection m) :
    (∏ q ∈ selectedSet m b,w q.1 q.2)=∏ e,selectedWeight (w e) (b e) := by
  classical
  simp only [selectedSet,Finset.prod_filter,selectedWeight,Fintype.prod_prod_type]

omit [DecidableEq V] in
theorem realMatching_partition (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m))
    (w : E → Fin (m+1) → ℝ) :
    partitionWeight (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (fun q => w q.1 q.2) (survivors m R U)=
      realHolePartition u v m R U w := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R U b}
  unfold partitionWeight realHolePartition
  rw [←(realMatchingEquiv u v m huv R U).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact selectedSet_weight m w b.val

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_MatchingMap
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

lemma matchingMap_injective (U : Finset V) : Function.Injective (matchingMap inc inc' f hinc U) := by
  intro a b h
  apply Subtype.ext
  exact Finset.map_injective f (congrArg Subtype.val h)

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_on [Fintype F] [DecidableEq E] (w : E → ℝ) (e : E) : edgeExtension f w (f e)=w e := by
  classical
  unfold edgeExtension
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg w (f.injective (Exists.choose_spec (show ∃ e',f e'=f e from ⟨e,rfl⟩)))

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_off [Fintype F] [DecidableEq E] (w : E → ℝ) (q : F) (hq : ¬∃ e,f e=q) : edgeExtension f w q=0 := by
  classical
  simp [edgeExtension,hq]

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_nonneg [Fintype F] [DecidableEq E] (w : E → ℝ) (hw : ∀ e,0≤w e) (q : F) : 0≤edgeExtension f w q := by
  classical
  unfold edgeExtension
  split_ifs <;> first | exact hw _ | norm_num

lemma matchingMap_weight (w : E → ℝ) (U : Finset V) (M : Matchings inc U) :
    (∏ q∈(matchingMap inc inc' f hinc U M).val,edgeExtension f w q)=∏ e∈M.val,w e := by
  dsimp [matchingMap]
  rw [Finset.prod_map]
  simp_rw [edgeExtension_on]

include hinc in

theorem partition_embedding (w : E → ℝ) (U : Finset V) :
    partitionWeight inc' (edgeExtension f w) U=partitionWeight inc w U := by
  classical
  unfold partitionWeight
  symm
  apply Finset.sum_bij_ne_zero (fun M _ _ => matchingMap inc inc' f hinc U M)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ h
    exact matchingMap_injective inc inc' f hinc U h
  · intro N _ hN
    have hr : ∀ q∈N.val,∃ e,f e=q := by
      intro q hq
      by_contra hn
      apply hN
      exact Finset.prod_eq_zero hq (edgeExtension_off f w q hn)
    let S := univ.filter fun e : E => f e∈N.val
    have hS : S.map f=N.val := by
      ext q
      constructor
      · intro hq
        obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
        exact (Finset.mem_filter.mp he).2
      · intro hq
        obtain ⟨e,rfl⟩ := hr q hq
        exact Finset.mem_map.mpr ⟨e,by simp [S,hq],rfl⟩
    let M : Matchings inc U := ⟨S,(matching_map_iff inc inc' f hinc S U).mp (hS.symm ▸ N.property)⟩
    have hM : matchingMap inc inc' f hinc U M=N := Subtype.ext hS
    refine ⟨M,Finset.mem_univ _,?_,hM⟩
    rw [←matchingMap_weight inc inc' f hinc w U M,hM]
    exact hN
  · intro M _ _
    exact (matchingMap_weight inc inc' f hinc w U M).symm

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags
lemma sourceRealPortion_partition (w : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)) := by
  classical
  rw [show sourceRealPortion w K=edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

lemma sourceRealActivity_pos (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : SourceRealEdge V K) : 0 < sourceRealActivity w K e := by
  have hl : 0<logicalActivity w e.1 := by
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  exact hl.trans_le (profile_lower _ _ _ _ _
    (edgeActivity_le_bottleneck w _ _ (source_ne_target e.1)) e.2)

lemma sourceRealPortion_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ sourceRealPortion w K e := by
  classical
  exact edgeExtension_nonneg _ _ (fun q => (sourceRealActivity_pos w hw K q).le) e

lemma sourceRealPortion_full (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) univ =
      (∏ e, pathConstant (2*K+2) (bottleneck w (source e) (target e))
        (sourceHeight w (source e)) (sourceHeight w (target e))) * partition w ∅ := by
  rw [←survivors_empty (V := V) K,sourceRealPortion_partition]
  exact intact_partition_identity w hz _ _ _ _

lemma sourceRealPortion_full_pos (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    0<partitionWeight BagEdge.Incident (sourceRealPortion w K) univ := by
  rw [sourceRealPortion_full w hz K]
  apply mul_pos _ hz
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck w _ _))



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_1_r79c9d5_1 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma bagHeight_one (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 1 ≤ bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

lemma bagHeight_pos (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 0 < bagHeight w K l :=
  zero_lt_one.trans_le (bagHeight_one w K l)

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Marked
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma mass_nonneg (part : E → I → ℝ) (hp : ∀ e i,0 ≤ part e i) (a : Marked (I:=I) inc) :
    0 ≤ mass inc part a := Finset.prod_nonneg fun _ _ => hp _ _

omit [DecidableEq V] in
lemma pattern_sum (part : E → I → ℝ)
    (pattern : (M : Matchings inc univ) → ↥M.val → I)
    (u : Matchings inc univ → ℝ) :
    (∑ a : Marked (I:=I) inc, if a.2=pattern a.1 then mass inc part a*u a.1 else 0)=
      ∑ M : Matchings inc univ,(∏ e : M.val,part e.val (pattern M e))*u M := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  simp only [Finset.sum_ite_eq',mem_univ,ite_true,mass]

omit [DecidableEq V] in
lemma allReal_mean (part : E → I → ℝ) (real : I) (u : E → ℝ) :
    (∑ a : Marked (I:=I) inc,law inc part a *
      (if a.2=(fun _ => real) then ∏ e ∈ a.1.val,u e else 0))=
    partitionWeight inc (fun e => part e real*u e) univ /
      partitionWeight inc (collapse part) univ := by
  classical
  calc
    _ = (∑ a : Marked (I:=I) inc,
        if a.2=(fun _ => real) then mass inc part a*(∏ e ∈ a.1.val,u e) else 0) /
        partitionWeight inc (collapse part) univ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [law,mul_zero,zero_div,div_mul_eq_mul_div]
    _ = _ := by
      congr 1
      rw [pattern_sum inc part (fun _ _ => real) (fun M => ∏ e ∈ M.val,u e)]
      unfold partitionWeight
      apply Finset.sum_congr rfl
      intro M _
      rw [←Finset.prod_subtype M.val (fun _ => Iff.rfl) (fun e => part e real),
        ←Finset.prod_mul_distrib]

omit [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma law_from_reveal (part : E → I → ℝ) (hc : ∀ e,collapse part e≠0)
    (a : Marked (I:=I) inc) :
    ((∏ e ∈ a.1.val,collapse part e)/partitionWeight inc (collapse part) univ) *
      conditional inc part a.1 a.2 = law inc part a := by
  classical
  rw [conditional,Finset.prod_div_distrib,←Finset.prod_subtype a.1.val (fun _ => Iff.rfl)]
  have hn : (∏ e ∈ a.1.val,collapse part e)≠0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hc e)
  unfold law mass
  field_simp

end MatchingFPRAS.Marking

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_3
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_4
lemma frozenPortion_partition (w w₁ : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w₁)) := by
  classical
  rw [show frozenPortion w w₁ K=edgeExtension (sourceRealEmbedding w K) (frozenActivity w w₁ K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

lemma profile_reweight (p : ℕ) (B Hu Hv lam r : ℝ) (i : Fin (4*p+1)) :
    profileActivity p B Hu Hv (lam*r) i =
      profileActivity p B Hu Hv lam i*(if i.val=2*p then r else 1) := by
  rcases lt_trichotomy i.val (2*p) with hi|hi|hi
  · rw [profile_left _ _ _ _ _ _ hi,profile_left _ _ _ _ _ _ hi,ite_eq_right (ne_of_lt hi),mul_one]
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he]; simp
  · rw [profile_right _ _ _ _ _ _ hi,profile_right _ _ _ _ _ _ hi,ite_eq_right (ne_of_gt hi),mul_one]

lemma bagReweight_identity (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K : ℕ) :
    (fun e => sourceRealPortion w K e*bagReweight w w₁ K e)=frozenPortion w w₁ K := by
  classical
  funext e
  by_cases he : ∃ q,sourceRealEmbedding w K q=e
  · obtain ⟨q,rfl⟩ := he
    rw [sourceRealPortion,frozenPortion,edgeExtension_on,edgeExtension_on,bagReweight_on]
    have hl : logicalActivity w q.1≠0 := by
      unfold logicalActivity edgeActivity
      split_ifs <;> exact (hw _ _).ne'
    dsimp only [sourceRealActivity,frozenActivity,pathActivity,rawReweight]
    rw [←profile_reweight,mul_div_cancel₀ _ hl]
  · rw [sourceRealPortion,frozenPortion,edgeExtension_off _ _ _ he,edgeExtension_off _ _ _ he,zero_mul]

lemma bagReweight_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ bagReweight w w₁ K e ∧ bagReweight w w₁ K e ≤ 1 := by
  classical
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · have h₀ : 0 < logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw _ _
      have h₁ : 0 ≤ logicalActivity w₁ he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw₁ _ _
      have h₂ : logicalActivity w₁ he.choose.1 ≤ logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hle _ _
      exact ⟨div_nonneg h₁ h₀.le,(div_le_one h₀).mpr h₂⟩
    · norm_num
  · norm_num

lemma sourcePortions_collapse (w : V → V → ℝ) (K D : ℕ) :
    Marking.collapse (sourcePortions w K D)=sourceBagWeight w K D := by
  funext e
  simp [Marking.collapse,sourcePortions,Fin.sum_univ_succ,sourceBagWeight]

lemma sourcePortions_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) (i : Fin 3) : 0 ≤ sourcePortions w K D e i := by
  classical
  fin_cases i
  · exact sourceRealPortion_nonneg w hw K e
  · change 0 ≤ bagHeight w K e.val.val.2/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D)
  · change 0 ≤ probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity

open scoped Classical

lemma sourceLaw_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (hz : 0 ≤ sourceBagZ w K D) (a : SourceMarked w K) : 0 ≤ sourceLaw w K D a := by
  unfold sourceLaw Marking.law
  rw [sourcePortions_collapse]
  exact div_nonneg (Marking.mass_nonneg _ _ (sourcePortions_nonneg w hw K D) a) hz

lemma observableD_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y)
    (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableD w w₁ K a ∧ observableD w w₁ K a ≤ 1 := by
  classical
  unfold observableD
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeList
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma size_encode_list (as : List A) :
    TreeFunction.size (encode as) = 1+as.length+(as.map (fun a=>TreeFunction.size (encode a))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [encode_list_cons,size_cons,ih,List.length_cons,List.map_cons,List.sum_cons]; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma weight_pos (a : A) : 0<weight a := by
  change 0<TreeFunction.size (encode a)
  cases encode a <;> simp only [size_nil,size_cons] <;> omega
lemma list_length_le_weight (as : List A) : as.length≤weight as := by
  rw [weight,size_encode_list]; omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_AdaptiveStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

lemma average_const (n : ℕ) (a : ℚ) : average (fun _ : Bits n=>a)=a := by
  simp [average]

lemma average_split {n m : ℕ} (f : Bits (n+m) → ℚ) :
    average f=average (fun a : Bits n=>average (fun b : Bits m=>f (concat a b))) := by
  unfold average
  have h : (∑ b : Bits (n+m),f b)=∑ a : Bits n,∑ b : Bits m,f (concat a b) := by
    calc
      _ = ∑ ab : Bits n × Bits m,f (concat ab.1 ab.2) :=
        Fintype.sum_equiv (split n m) f (fun ab=>f (concat ab.1 ab.2)) (fun b=>by
          change f b=f ((split n m).symm ((split n m) b))
          rw [Equiv.symm_apply_apply])
      _ = _ := Fintype.sum_prod_type _
  rw [h,←sum_div,pow_add,div_div]
  congr 1
  ring

lemma average_one (f : Bits 1 → ℚ) :
    average f=(f (fun _=>false)+f (fun _=>true))/2 := by
  have h : (∑ b : Bits 1,f b)=f (fun _=>false)+f (fun _=>true) := by
    let e : Bits 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
    have hh:=Fintype.sum_equiv e f (fun b=>f (fun _=>b)) (fun b=>by
      congr 1; funext i; exact congrArg b (Subsingleton.elim i default))
    simpa only [Fintype.sum_bool,add_comm] using hh
  simp only [average,h,pow_one]

lemma shift_extend_concat {n m : ℕ} (a : Bits n) (b : Bits m) (i : ℕ) (hi : i < m) :
    shift n (extend (concat a b)) i=extend b i := by
  have hni : n+i<n+m := Nat.add_lt_add_left hi n
  simp only [shift,extend,dite_eq_left hi,dite_eq_left hni]
  exact concat_right a b ⟨i,hi⟩

lemma extend_concat_zero {m : ℕ} (a : Bits 1) (b : Bits m) :
    extend (concat a b) 0=a 0 := by
  simp only [extend,dite_eq_left (by omega : 0<1+m)]
  exact concat_left a b 0

namespace Experiment
variable {α β : Type}

lemma run_cost (p : Experiment α) (b : Stream) : (p.run b).2≤p.cost := by
  induction p generalizing b with
  | done a => rfl
  | read p ih =>
    simp only [run,cost]
    have h:=ih (b 0) (shift 1 b)
    cases hb : b 0 <;> simp only [hb] at h <;> omega
  | delay n p ih => exact Nat.add_le_add_left (ih (shift n b)) n

lemma run_congr (p : Experiment α) (a b : Stream)
    (h : ∀ i,i<p.cost → a i=b i) : p.run a=p.run b := by
  induction p generalizing a b with
  | done x => rfl
  | read p ih =>
    have h0 : a 0=b 0 := h 0 (by simp [cost])
    simp only [run,h0]
    have hh : run (p (b 0)) (shift 1 a)=run (p (b 0)) (shift 1 b) := by
      apply ih
      intro i hi
      apply h
      cases he : b 0 <;> simp only [he] at hi <;> simp only [cost] <;> omega
    rw [hh]
  | delay n p ih =>
    simp only [run]
    have hh : run p (shift n a)=run p (shift n b) := by
      apply ih
      intro i hi
      exact h (n+i) (by simp only [cost]; omega)
    rw [hh]

lemma run_suffix {n m : ℕ} (p : Experiment α) (h : p.cost ≤ m)
    (a : Bits n) (b : Bits m) :
    p.run (shift n (extend (concat a b)))=p.run (extend b) := by
  apply run_congr
  intro i hi
  exact shift_extend_concat a b i (lt_of_lt_of_le hi h)

theorem average_run (p : Experiment α) (f : α → ℚ) (n : ℕ) (hn : p.cost≤n) :
    average (fun b : Bits n=>f (p.run (extend b)).1)=p.mean f := by
  induction p generalizing n with
  | done a => exact average_const n (f a)
  | delay k p ih =>
    have hk : k≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm : p.cost ≤ m := by simpa only [cost,Nat.add_le_add_iff_left] using hn
    rw [average_split]
    have hrun (a : Bits k) (b : Bits m) :
        f ((delay k p).run (extend (concat a b))).1=f (p.run (extend b)).1 := by
      simp only [run,run_suffix p hm a b]
    simp_rw [hrun,ih m hm]
    exact average_const k (p.mean f)
  | read p ih =>
    have hk : 1≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm (b : Bool) : (p b).cost ≤ m := by
      simp only [cost,Nat.add_le_add_iff_left] at hn
      cases b <;> omega
    rw [average_split]
    have hrun (a : Bits 1) (b : Bits m) :
        f ((read p).run (extend (concat a b))).1=f ((p (a 0)).run (extend b)).1 := by
      simp only [run,extend_concat_zero,run_suffix _ (hm (a 0)) a b]
    simp_rw [hrun,ih _ m (hm _)]
    rw [average_one]
    rfl

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalPost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

lemma execute_add (M : Table Γ Q) (n m : ℕ) (c : Cfg Γ Q) (b : Stream) :
    execute M (n+m) c b=execute M m (execute M n c b) (shift n b) := by
  induction n generalizing c b with
  | zero => simp only [execute,Nat.zero_add,shift_zero]
  | succ n ih =>
    rw [Nat.succ_add,execute,ih,execute]
    congr 1
    funext i
    simp only [shift]
    congr 1
    omega

lemma execute_halted (M : Table Γ Q) (n : ℕ) (T : Tape Γ) (b : Stream) :
    execute M n ⟨none,T⟩ b=⟨none,T⟩ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => exact ih (shift 1 b)

variable [Fintype Q] [Inhabited Q]

lemma tick_seal (M : Table Symbol Q) (c : Cfg Symbol Q) (b : Bool) :
    MatchingFPRAS.tick (machine M) (sealCfg M c) b=sealCfg M (tick M c b) := by
  cases c with
  | mk s T => cases s with
    | none => rfl
    | some q =>
      simp only [MatchingFPRAS.tick,sealCfg,machine,Option.map_some,Equiv.symm_apply_apply,tick]
      cases h:M q T.head b with
      | none => rfl
      | some qa => rcases qa with ⟨q',a⟩; cases a <;> rfl

omit [Fintype Q] [Inhabited Q] in
lemma execute_list (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Bits n) :
    execute M n c (extend b)=(List.ofFn b).foldl (tick M) c := by
  induction n generalizing c with
  | zero => simp [execute]
  | succ n ih =>
    rw [execute,List.ofFn_succ,List.foldl_cons]
    have h0 : extend b 0=b 0 := by simp [extend]
    rw [h0,←ih]
    have he : ∀ i, i<n → shift 1 (extend b) i=extend (fun j : Fin n=>b j.succ) i := by
      intro i hi
      simp only [shift,extend,dite_eq_left hi,dite_eq_left (by omega : 1+i<n+1)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hc : ∀ (k : ℕ) (a d : Stream), (∀ i,i<k→a i=d i) →
        ∀ c, execute M k c a=execute M k c d := by
      intro k
      induction k with
      | zero => intros; rfl
      | succ k hk =>
        intro a d had c
        simp only [execute,had 0 (by omega)]
        apply hk
        intro i hi
        exact had (1+i) (by omega)
    exact hc n _ _ he _

lemma foldl_seal (M : Table Symbol Q) (bs : List Bool) (c : Cfg Symbol Q) :
    bs.foldl (MatchingFPRAS.tick (machine M)) (sealCfg M c)=sealCfg M (bs.foldl (tick M) c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => rw [List.foldl_cons,tick_seal,ih,List.foldl_cons]

lemma initial_seal (M : Table Symbol Q) (input : List Symbol) :
    sealCfg M ⟨some default,Tape.mk₁ input⟩=MatchingFPRAS.initial (machine M) input := by
  change (⟨some (enumeration default),Tape.mk₁ input⟩ : Configuration (machine M))=⟨some 0,Tape.mk₁ input⟩
  rw [enumeration_default]
  rfl

theorem run_seal (M : Table Symbol Q) (input : List Symbol) (n : ℕ) (b : Bits n) :
    MatchingFPRAS.run (machine M) input b=
      sealCfg M (execute M n ⟨some default,Tape.mk₁ input⟩ (extend b)) := by
  unfold MatchingFPRAS.run
  rw [←initial_seal,foldl_seal,execute_list]

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_CoinTM1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

lemma execute_first_eq (M : PhysicalPost.Table Γ (State Γ Λ σ))
    (x y : PhysicalPost.Cfg Γ (State Γ Λ σ)) (h : ∀ b,PhysicalPost.tick M x b=PhysicalPost.tick M y b)
    {n : ℕ} (hn : 0 < n) (b : Stream) : PhysicalPost.execute M n x b=PhysicalPost.execute M n y b := by
  cases n with
  | zero => omega
  | succ n => simp only [PhysicalPost.execute,h]

theorem statement_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ k,0 < k ∧ k ≤ statementCost q ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (pending q v T) b=trCfg (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.move d)
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | write f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih v (T.write (f T.head v))
    refine ⟨k+1,by omega,by simp only [statementCost]; omega,fun b=>?_⟩
    simpa only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux] using he (shift 1 b)
  | load f q ih =>
    obtain ⟨k,hk,hc,he⟩:=ih (f T.head v) T
    refine ⟨k,hk,hc,fun b=>?_⟩
    rw [execute_first_eq (table M coin) (pending (.load f q) v T) (pending q (f T.head v) T) (fun _=>rfl) hk]
    exact he b
  | branch f q r ihq ihr =>
    cases h:f T.head v with
    | false =>
      obtain ⟨k,hk,hc,he⟩:=ihr v T
      refine ⟨k,hk,hc.trans (le_max_right _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending r v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,Bool.false_eq_true,ite_false]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_false] using he b
    | true =>
      obtain ⟨k,hk,hc,he⟩:=ihq v T
      refine ⟨k,hk,hc.trans (le_max_left _ _),fun b=>?_⟩
      rw [execute_first_eq (table M coin) (pending (.branch f q r) v T) (pending q v T) (fun _=>by
        simp only [PhysicalPost.tick,pending,table,aux,h,ite_true]) hk]
      simpa only [TM1.stepAux,h,Bool.cond_true] using he b
  | goto f =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    simp only [PhysicalPost.execute,PhysicalPost.tick,pending,table,aux,TM1.stepAux,trCfg,Option.map_some,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,le_rfl,fun b=>?_⟩
    rfl

lemma entry_ticks (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (hl : coin l=none) :
    ∃ k,0 < k ∧ k ≤ statementCost (M l) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (trCfg ⟨some l,v,T⟩) b=
        trCfg (TM1.stepAux (M l) v T) := by
  obtain ⟨k,hk,hc,he⟩:=statement_ticks M coin (M l) v T
  refine ⟨k,hk,hc,fun b=>?_⟩
  rw [execute_first_eq (table M coin) (trCfg ⟨some l,v,T⟩) (pending (M l) v T) (fun _=>by
    simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,pending]) hk]
  exact he b

lemma coin_tick (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ)
    (l : Λ) (v : σ) (T : Tape Γ) (f : Bool → Λ) (hl : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (trCfg ⟨some l,v,T⟩) b=trCfg ⟨some (f b),v,T⟩ := by
  simp only [PhysicalPost.tick,trCfg,Option.map_some,table,hl,Tape.write_self]

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalRestriction
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

lemma tick_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (c : Cfg Γ {q // q∈S}) (b : Bool) :
    tick M (liftCfg S c) b=liftCfg S (tick (restrict M S h) c b) := by
  cases c with
  | mk state T => cases state with
    | none => rfl
    | some q =>
      cases e:M q.val T.head b with
      | none => simp only [tick,liftCfg,Option.map_some,restrict,e,Option.map_none]
      | some qa =>
        rcases qa with ⟨q',act⟩
        have hq' : q'∈S:=h q.val q.property T.head b q' act e
        simp only [tick,liftCfg,Option.map_some,restrict,e,dite_eq_left hq']

lemma execute_lift (M : Table Γ Q) (S : Finset Q) (h : Supported M S)
    (n : ℕ) (c : Cfg Γ {q // q∈S}) (b : Stream) :
    execute M n (liftCfg S c) b=liftCfg S (execute (restrict M S h) n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_lift,ih,execute]

lemma restrictedMachine_run (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S)
    (input : List Symbol) (n : ℕ) (b : Bits n) :
    letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
    MatchingFPRAS.run (restrictedMachine M S h q₀ hq₀) input b=
      sealCfg (restrict M S h)
        (execute (restrict M S h) n ⟨some default,Tape.mk₁ input⟩ (extend b)) :=
by
  let : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  exact run_seal (restrict M S h) input n b

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SafeTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SafeTrace
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

namespace Path
variable {M : Λ → TM1.Stmt Γ Λ σ} {safe : Λ → Prop}
lemma single (c : TM1.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→safe l) :
    Path M safe 1 c (advance (TM1.step M) c) := .cons hc (.refl _)
lemma trans {n m : ℕ} {a b c : TM1.Cfg Γ Λ σ}
    (h : Path M safe n a b) (g : Path M safe m b c) : Path M safe (n+m) a c := by
  induction h with
  | refl a => simpa only [Nat.zero_add] using g
  | @cons n a b ha hr ih => simpa only [Nat.succ_add] using Path.cons ha (ih g)
lemma of_run (n : ℕ) (c : TM1.Cfg Γ Λ σ)
    (h : ∀ i,i<n→∀ l,(MachineCost.run (TM1.step M) i c).l=some l→safe l) :
    Path M safe n c (MachineCost.run (TM1.step M) n c) := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih =>
    refine .cons (h 0 (by omega)) (ih _ ?_)
    intro i hi l hl
    exact h (i+1) (by omega) l hl

theorem physical {n : ℕ} {a b : TM1.Cfg Γ Λ σ} (h : Path M safe n a b)
    (coin : CoinTM1.Coins Λ) (hcoin : ∀ l,safe l→coin l=none)
    (C : ℕ) (hC : ∀ l,safe l→statementCost (M l)≤C) :
    ∃ k,k≤n*C ∧ ∀ bits : Stream,
      PhysicalPost.execute (CoinTM1.table M coin) k (CoinTM1.trCfg a) bits=CoinTM1.trCfg b := by
  induction h with
  | refl a => exact ⟨0,by simp,fun _=>rfl⟩
  | @cons n c d hc hr ih =>
    obtain ⟨k,hk,he⟩:=ih
    rcases c with ⟨l,v,T⟩
    cases l with
    | none =>
      refine ⟨k,le_trans hk ?_,he⟩
      exact Nat.mul_le_mul_right C (by omega)
    | some l =>
      have hs:=hc l rfl
      obtain ⟨j,hj,hjc,hje⟩:=CoinTM1.entry_ticks M coin l v T (hcoin l hs)
      refine ⟨j+k,?_,fun bits=>?_⟩
      · have hb:=hC l hs
        calc j+k≤C+n*C := Nat.add_le_add (hjc.trans hb) hk
             _=(n+1)*C := by ring
      · rw [PhysicalPost.execute_add,hje]
        exact he (shift j bits)
end Path
end MatchingFPRAS.SafeTrace

namespace MatchingFPRAS.SafeTrace.Path
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ]
lemma with_support {M : Λ → TM1.Stmt Γ Λ σ} {safe : Λ → Prop} {S : Finset Λ}
    (hS : TM1.Supports M S) {n : ℕ} {a b : TM1.Cfg Γ Λ σ}
    (h : Path M safe n a b) (ha : ∀ l,a.l=some l→l∈S) :
    Path M (fun l=>safe l ∧ l∈S) n a b := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d hc hr ih =>
    refine .cons (fun l hl=>⟨hc l hl,ha l hl⟩) (ih ?_)
    intro l hl
    rcases c with ⟨lc,v,T⟩
    cases lc with
    | none => simp [advance,TM1.step] at hl
    | some lc =>
      have hs:=TM1.step_supports M hS (c:=⟨some lc,v,T⟩) (c':=TM1.stepAux (M lc) v T) rfl (by
        simp only [Finset.some_mem_insertNone]; exact ha lc rfl)
      simp only [advance,TM1.step,Option.getD_some] at hl
      exact Finset.some_mem_insertNone.mp (hl ▸ hs)
end MatchingFPRAS.SafeTrace.Path

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing TM1 TM1to1 MachineCost SafeTrace

variable {Γ Λ σ : Type} [Inhabited Γ]

variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default=List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)

include encdec

theorem statement_path (p : Λ → Prop) (q : TM1.Stmt Γ Λ σ) (v : σ) (L R : ListBlank Γ) :
    ∃ t,t≤AlphabetCost.writesCount q ∧
      Path (tr enc dec M) (safe p) t
        (stepAux (trNormal dec q) v (trTape' enc0 L R))
        (trCfg enc enc0 (stepAux q v (Tape.mk' L R))) := by
  induction q generalizing v L R with
  | move d q ih =>
    cases d <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,AlphabetCost.writesCount] <;>
      apply ih
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    obtain ⟨a,R,rfl⟩:=R.exists_cons
    obtain ⟨t,ht,he⟩:=ih v L (R.cons (f a v))
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l hl; cases hl; trivial)
    simp only [advance,TM1.step,tr,Option.getD_some,Tape.mk'_head,ListBlank.head_cons]
    rw [stepAux_write enc0,stepAux_move,trTape'_move_left enc0]
    simpa using he
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,AlphabetCost.writesCount]
    exact ih _ _ _
  | branch p' q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,Tape.mk'_head,AlphabetCost.writesCount]
    cases h:p' R.head v
    · simp only [Bool.cond_false]
      obtain ⟨t,ht,he⟩:=ihr v L R
      exact ⟨t,ht.trans (le_max_right _ _),he⟩
    · simp only [Bool.cond_true]
      obtain ⟨t,ht,he⟩:=ihq v L R
      exact ⟨t,ht.trans (le_max_left _ _),he⟩
  | goto f =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',Tape.mk'_head,Option.map_some]
    exact .refl _
  | halt =>
    refine ⟨0,le_rfl,?_⟩
    simp only [trNormal,stepAux,trCfg,trTape_mk',Option.map_none]
    exact .refl _

lemma one_step_path (p : Λ → Prop) (c : TM1.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→p l) :
    ∃ t,t≤(match c.l with | none=>0 | some l=>AlphabetCost.writesCount (M l)+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 c)
        (trCfg enc enc0 (advance (TM1.step M) c)) := by
  rcases c with ⟨l,v,T⟩
  obtain ⟨L,R,rfl⟩:=T.exists_mk'
  cases l with
  | none => exact ⟨0,le_rfl,.refl _⟩
  | some l =>
    obtain ⟨t,ht,he⟩:=statement_path enc dec enc0 encdec M p (M l) v L R
    refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
    apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
    simpa only [advance,TM1.step,Option.map_some,trCfg,tr,Option.getD_some,trTape_mk'] using he

theorem path_supported [Inhabited Λ] [Inhabited σ] (S : Finset Λ) (hS : TM1.Supports M S)
    {p : Λ → Prop} {k : ℕ} {a b : TM1.Cfg Γ Λ σ}
    (h : Path M p k a b) (ha : a.l∈S.insertNone) :
    ∃ t,t≤k*(AlphabetCost.supportedWrites M S+1) ∧
      Path (tr enc dec M) (safe p) t (trCfg enc enc0 a) (trCfg enc enc0 b) := by
  classical
  induction h with
  | refl a => exact ⟨0,by simp,.refl _⟩
  | @cons k a b hs hr ih =>
    obtain ⟨i,hi,hiP⟩:=one_step_path enc dec enc0 encdec M p a hs
    obtain ⟨j,hj,hjP⟩:=ih (SupportedCompiler.advance_supported M S hS ha)
    have hi' : i≤AlphabetCost.supportedWrites M S+1 := by
      rcases a with ⟨l,v,T⟩
      cases l with
      | none => dsimp at hi; omega
      | some l =>
        have hl:=Finset.some_mem_insertNone.mp ha
        have hw : AlphabetCost.writesCount (M l)≤AlphabetCost.supportedWrites M S :=
          Finset.le_sup (f:=fun l=>AlphabetCost.writesCount (M l)) hl
        dsimp at hi
        omega
    refine ⟨i+j,?_,hiP.trans hjP⟩
    calc i+j≤(AlphabetCost.supportedWrites M S+1)+k*(AlphabetCost.supportedWrites M S+1) := Nat.add_le_add hi' hj
         _=(k+1)*(AlphabetCost.supportedWrites M S+1) := by ring

omit [Inhabited Γ] encdec in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | write a q => rfl
end MatchingFPRAS.CoinAlphabet

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinStack
open Turing TM2to1 TM2to1.Λ' MachineCost StackCost SafeTrace

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

variable (M : Λ → TM2.Stmt Γ Λ σ) (p : Λ → Prop)
lemma go_path {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k,Option (Γ k))}
    (hL : L.map (proj k)=ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n≤ S.length) :
    Path (tr M) (safe p) n ⟨some (go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  rw [←go_time M o q v hL n hn]
  apply Path.of_run
  intro i hi l hl
  rw [go_time M o q v hL i (by omega)] at hl
  cases hl
  trivial

lemma return_path (q : TM2.Stmt Γ Λ σ) (v : σ) (L : ListBlank (∀ k,Option (Γ k))) (n : ℕ) :
    Path (tr M) (safe p) n
      ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Path.cons (by intro l hl; cases hl; trivial)
    have hs : advance (TM1.step (tr M))
        ⟨some (ret q),v,(Tape.move .right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v,(Tape.move .right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,Bool.cond_false]
      rw [Function.iterate_succ_apply',Tape.move_right_left]
      rfl
    rw [hs]
    exact ih

theorem statement_path (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k,List (Γ k))
    (L : ListBlank (∀ k,Option (Γ k))) (H : ℕ) (hS : StackBound S H)
    (hL : ∀ k,L.map (proj k)=ListBlank.mk ((S k).map some).reverse) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 2*accesses q*(H+accesses q+1) ∧ TrCfg (TM2.stepAux q v S) b ∧
      Path (tr M) (safe p) t
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b := by
  induction q using stmtStRec generalizing v S L H with
  | run k o q ih =>
    let v':=stVar v (S k) o
    let S':=Function.update S k (stWrite v (S k) o)
    have hS' : StackBound S' (H+1):=action_bound hS o v
    obtain ⟨L',hL',hact⟩:=tr_respects_aux₂
      (q:=TM1.Stmt.goto fun _ _=>ret q) hL o
    obtain ⟨t,b,ht,hb,he⟩:=ih v' S' L' (H+1) hS' hL'
    have hgo:=go_path M p o q v (hL k) (S k).length le_rfl
    have hs : advance (TM1.step (tr M))
        ⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩=
        ⟨some (ret q),v',(Tape.move .right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [advance,TM1.step]
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hL k),List.getElem?_eq_none (le_of_eq List.length_reverse)]
      simp only [Option.isNone_none,Bool.cond_true]
      rw [hact]
      rfl
    have hstep:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (go k o q),v,(Tape.move .right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩)
      (by intro l hl; cases hl; trivial)
    rw [hs] at hstep
    have hret:=return_path M p q v' L' (S' k).length
    have hlast:=Path.single (M:=tr M) (safe:=safe p)
      (⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩)
      (by intro l hl; cases hl; trivial)
    have hf : advance (TM1.step (tr M)) ⟨some (ret q),v',Tape.mk' ∅ (addBottom L')⟩=
        TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L')) := by
      simp only [advance,TM1.step,tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst,
        Bool.cond_true,Option.getD_some]
    rw [hf] at hlast
    refine ⟨(S k).length+1+(S' k).length+1+t,b,?_,?_,?_⟩
    · rw [accesses_run]
      have h₁:=hS k
      have h₂:=hS' k
      nlinarith
    · simpa only [step_run] using hb
    · simpa only [trNormal_run,TM1.stepAux] using (((hgo.trans hstep).trans hret).trans hlast).trans he
  | load a q ih => exact ih (a v) S L H hS hL
  | branch f q r ihq ihr =>
    cases hp:f v
    · obtain ⟨t,b,ht,hb,he⟩:=ihr v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_right _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_false] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_false] using he
    · obtain ⟨t,b,ht,hb,he⟩:=ihq v S L H hS hL
      refine ⟨t,b,ht.trans ?_,?_,?_⟩
      · simp only [accesses]; gcongr <;> exact le_max_left _ _
      · simpa only [TM2.stepAux,hp,Bool.cond_true] using hb
      · simpa only [trNormal,TM1.stepAux,hp,Bool.cond_true] using he
  | goto f => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | halt => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩

lemma one_step_path (A : ℕ) (hA : ∀ l,accesses (M l)≤ A)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : ∀ l,c.l=some l→p l) (H : ℕ) (hS : StackBound c.stk H) :
    ∃ (t : ℕ) (b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ),
      t≤ 1+2*A*(H+A+1) ∧ TrCfg (advance (TM2.step M) c) b ∧ Path (tr M) (safe p) t a b := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S
  cases l with
  | none => exact ⟨0,_,Nat.zero_le _,⟨L,hL⟩,.refl _⟩
  | some l =>
    obtain ⟨t,b,ht,hb,he⟩:=statement_path M p (M l) v S L H hS hL
    refine ⟨t+1,b,?_,hb,?_⟩
    · have hh : 2*accesses (M l)*(H+accesses (M l)+1)≤ 2*A*(H+A+1) := by
        gcongr <;> exact hA l
      omega
    · apply Path.cons (by intro l' hl; cases hl; exact hc l rfl)
      simpa only [advance,TM1.step,Option.map_some,tr,Option.getD_some] using he

omit [DecidableEq K] in
lemma coins_none {c : CoinTM1.Coins Λ} {l : Λ' K Γ Λ σ}
    (h : safe (fun l=>c l=none) l) : coins c l=none := by
  cases l with
  | normal l => simp only [coins,safe] at *; rw [h]; rfl
  | go k o q => rfl
  | ret q => rfl
end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_CoinSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ]
lemma cfg_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    {n : ℕ} (enc : Γ → List.Vector Bool n) (enc0 : enc default=List.Vector.replicate n false)
    (c : TM1.Cfg Γ Λ σ) (hc : c.l∈S.insertNone) :
    (TM1to1.trCfg enc enc0 c).l∈(TM1to1.trSupp M S).insertNone := by
  rcases c with ⟨l,v,T⟩
  cases l with
  | none => simp [TM1to1.trCfg]
  | some l => simpa only [TM1to1.trCfg,Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinAlphabet

namespace MatchingFPRAS.CoinStack
open Turing TM2to1
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
omit [DecidableEq K] in
lemma cfg_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ)
    {c : TM2.Cfg Γ Λ σ} {a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hca : TrCfg c a) (hc : c.l∈S.insertNone) : a.l∈(trSupp M S).insertNone := by
  rcases hca with ⟨L,hL⟩
  rename_i l v S'
  cases l with
  | none => simp
  | some l => simpa only [Option.map_some,Finset.some_mem_insertNone,normal_mem] using hc
end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

namespace Implements
variable {M : Table Γ Q} {out : α → Cfg Γ Q} {c : Cfg Γ Q} {p : Experiment α}

lemma execution (h : Implements M out c p) (b : Stream) :
    execute M (p.run b).2 c b=out (p.run b).1 := by
  induction h generalizing b with
  | done a => rfl
  | read c f h ih =>
    simp only [Experiment.run,execute_add]
    exact ih (b 0) (shift 1 b)
  | delay c d n p hs hr ih =>
    simp only [Experiment.run,execute_add,hs]
    exact ih (shift n b)

lemma padded_execution (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (b : Stream) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2 ≤ n:=(Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,h.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      have hstate := halt (p.run b).1
      rw [e] at hstate
      change state = none at hstate
      subst state
      rfl
  rw [he,execute_halted]

theorem fair_law (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=p.mean (fun a=>f (out a)) := by
  simp_rw [h.padded_execution halt n hn]
  exact Experiment.average_run p (fun a=>f (out a)) n hn

end Implements
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PhysicalAlphabet
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream BoolPostCompiler

variable {Q : Type}

lemma tick_up (M : Table Bool Q) (c : Cfg Bool Q) (b : Bool) :
    tick (liftBool M) (upCfg c) b=upCfg (tick M c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some q =>
    simp only [tick,upCfg,liftBool,(show (T.map up).head=up T.head from rfl),down_up]
    cases e:M q T.head b with
    | none => rfl
    | some qa =>
      rcases qa with ⟨q',act⟩
      cases act with
      | move d => simp only [Option.map_some,TM0.Stmt.map,Tape.map_move]
      | write a => simp only [Option.map_some,TM0.Stmt.map,Tape.map_write]
lemma execute_up (M : Table Bool Q) (n : ℕ) (c : Cfg Bool Q) (b : Stream) :
    execute (liftBool M) n (upCfg c) b=upCfg (execute M n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_up,ih,execute]
lemma Implements.up {α : Type} {M : Table Bool Q} {out : α → Cfg Bool Q}
    {c : Cfg Bool Q} {p : Experiment α} (h : Implements M out c p) :
    Implements (liftBool M) (fun a=>upCfg (out a)) (upCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih =>
    apply Implements.read
    intro b
    rw [tick_up]
    exact ih b
  | delay c d n p hs hr ih =>
    apply Implements.delay (upCfg c) (upCfg d) n p _ ih
    intro b
    rw [execute_up,hs]
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_OnlineStackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream SafeTrace
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
omit [DecidableEq K] [∀ k,Fintype (Γ k)] in
lemma height_bound (S : ∀ k,List (Γ k)) : StackCost.StackBound S (height S) :=
  fun k=>Finset.le_sup (f:=fun k=>(S k).length) (Finset.mem_univ k)
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_spec [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] (c : TM2.Cfg Γ Λ σ) : TM2to1.TrCfg c (stackCfg c) := by
  rcases c with ⟨l,v,S⟩
  have h:=TM2to1.TrCfg.mk (Λ:=Λ) (σ:=σ) (q:=l) (v:=v)
    (ListBlank.mk (StackWords.rows S (height S))) (StackWords.rows_projection S _ (height_bound S))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_unique [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] {c : TM2.Cfg Γ Λ σ}
    {a : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ} (h : TM2to1.TrCfg c a) : a=stackCfg c := by
  rcases h with ⟨L,hL⟩
  rename_i l v S
  rw [StackWords.unique_rows S (height S) (height_bound S) L hL]
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl

variable (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
lemma encdec (a : Alpha K Γ) : dec (enc a)=a := FixedEncoding.left_inverse _ a
omit [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ]
  [Inhabited σ] [Fintype σ] in
lemma accesses_bound (l : Λ) : StackCost.accesses (M l)≤accesses M :=
  Finset.le_sup (f:=fun l=>StackCost.accesses (M l)) (Finset.mem_univ l)

theorem deterministic (c : TM2.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→coin l=none)
    (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ k,k≤overhead M*(1+2*accesses M*(H+accesses M+1)) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (cfg c) b=cfg (advance (TM2.step M) c) := by
  obtain ⟨i,a,hi,ha,hpath⟩:=CoinStack.one_step_path M (fun l=>coin l=none)
    (accesses M) (accesses_bound M) (stackCfg_spec c) hc H hH
  have hc1 : (stackCfg c).l∈(support1 M).insertNone :=
    CoinStack.cfg_supported M Finset.univ (stackCfg_spec c) (by simp)
  obtain ⟨j,hj,hpath2⟩:=CoinAlphabet.path_supported enc dec enc0 encdec (program1 M)
    (support1 M) (supports1 M) hpath hc1
  have hc2 : (TM1to1.trCfg enc enc0 (stackCfg c)).l∈(support2 M).insertNone :=
    CoinAlphabet.cfg_supported (program1 M) (support1 M) enc enc0 (stackCfg c) hc1
  have hh:=hpath2.with_support (supports2 M) (fun l hl=>Finset.some_mem_insertNone.mp (hl ▸ hc2))
  obtain ⟨k,hk,he⟩:=hh.physical (coin2 coin)
    (fun l hl=>CoinAlphabet.coins_none (by
      cases l with
      | normal l => exact CoinStack.coins_none hl.1
      | write a q => trivial))
    (SupportedCompiler.cost (program2 M) (support2 M)) (fun l hl=>SupportedCompiler.cost_le _ _ hl.2)
  refine ⟨k,?_,fun b=>?_⟩
  · calc
      k≤(i*(AlphabetCost.supportedWrites (program1 M) (support1 M)+1))*
          SupportedCompiler.cost (program2 M) (support2 M) := hk.trans (Nat.mul_le_mul_right _ hj)
      _=overhead M*i := by unfold overhead; ring
      _≤overhead M*(1+2*accesses M*(H+accesses M+1)) := Nat.mul_le_mul_left _ hi
  · rw [stackCfg_unique ha] at he
    exact he b

omit [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ] in
lemma random [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) (f : Bool → Λ) (hf : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (cfg ⟨some l,v,S⟩) b=cfg ⟨some (f b),v,S⟩ := by
  apply CoinTM1.coin_tick
  simp only [coin2,CoinAlphabet.coins,CoinStack.coins,hf,Option.map_some]

end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Online
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_mono [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H H' n n' : ℕ) (hH : H≤H') (hn : n≤n') :
    factor M H n ≤ factor M H' n' := by unfold factor; gcongr
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_shift [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H n : ℕ) : factor M (H+accesses M) n=factor M H (1+n) := by
  unfold factor
  congr 3; ring

theorem compile (h : Executes M coin out c p) (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ q : Experiment α,
      PhysicalPost.Implements (table M coin) (fun a=>cfg (out a)) (cfg c) q ∧
      (∀ f : α → ℚ,q.mean f=p.mean f) ∧ q.cost ≤ p.cost*factor M H p.cost := by
  induction h generalizing H with
  | done a => exact ⟨.done a,.done a,fun _=>rfl,by simp [Experiment.cost]⟩
  | read l v S f p hf rest ih =>
    choose q hq hmean hcost using fun b=>ih b H hH
    refine ⟨.read q,.read _ q (fun b=>?_),?_,?_⟩
    · rw [random M coin l v S f hf b]
      exact hq b
    · intro g
      simp only [Experiment.mean,hmean]
    · have hn0 : (p false).cost≤1+max (p false).cost (p true).cost := by omega
      have hn1 : (p true).cost≤1+max (p false).cost (p true).cost := by omega
      have hc0 := (hcost false).trans (Nat.mul_le_mul_left (p false).cost (factor_mono (M:=M) H H _ _ le_rfl hn0))
      have hc1 := (hcost true).trans (Nat.mul_le_mul_left (p true).cost (factor_mono (M:=M) H H _ _ le_rfl hn1))
      have hp : 1≤factor M H (1+max (p false).cost (p true).cost) := by unfold factor; omega
      simp only [Experiment.cost]
      have hf0 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_left (p false).cost (p true).cost)
      have hf1 := Nat.mul_le_mul_right (factor M H (1+max (p false).cost (p true).cost)) (le_max_right (p false).cost (p true).cost)
      calc
        1+max (q false).cost (q true).cost ≤ 1+max (p false).cost (p true).cost*factor M H (1+max (p false).cost (p true).cost) := by omega
        _≤ (1+max (p false).cost (p true).cost)*factor M H (1+max (p false).cost (p true).cost) := by nlinarith
  | step l v S p safe rest ih =>
    let c : TM2.Cfg Γ Λ σ:=⟨some l,v,S⟩
    have hs : ∀ u,c.l=some u→coin u=none := by intro u hu; cases hu; exact safe
    obtain ⟨k,hk,he⟩:=deterministic M coin c hs H hH
    obtain ⟨q,hq,hm,hc⟩:=ih (H+accesses M) (StackCost.advance_bound M _ (accesses_bound M) c H hH)
    refine ⟨.delay k q,.delay _ _ k q he hq,hm,?_⟩
    simp only [Experiment.cost]
    rw [factor_shift] at hc
    have hfac : k≤factor M H (1+p.cost) := by
      apply hk.trans
      unfold factor
      have hh : H+accesses M+1≤H+(1+p.cost)*accesses M+1 := by nlinarith
      have hb : overhead M*(1+2*accesses M*(H+accesses M+1))≤
        overhead M*(1+2*accesses M*(H+(1+p.cost)*accesses M+1)) := by gcongr
      omega
    nlinarith
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ExperimentSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_run (p : Experiment α) (P : α → Prop) (h : All p P) (b : Stream) : P (p.run b).1 := by
  induction p generalizing b with
  | done a => exact h
  | read p ih =>
    cases hb : b 0 <;> simp only [run,hb] <;> apply ih <;> first | exact h.1 | exact h.2
  | delay n p ih => exact ih h (shift n b)
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

variable {α : Type}
lemma worst_le (p : Experiment α) (f : α → ℕ) (N : ℕ) (h : All p (fun a=>f a≤N)) : p.worst f≤N := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
omit [Fintype B] in
lemma qaverage_congr (f g : A → ℚ) (h : ∀ a,f a=g a) : qaverage f=qaverage g := by
  rw [show f=g from funext h]
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related2
attribute [-instance] _root_.OAI.MatchingFPRAS.NumberedHierarchy.treeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

lemma labelEquiv_level {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) :
    (labelEquiv B hsym htri H l).1=l.1 := rfl

end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

lemma realPortion_on (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    realPortion w K (coloredReal w K q)=pathActivity w K q.1 q.2 := by
  simp only [realPortion,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]

lemma realPortion_off (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : realPortion w K e=0 := by
  apply sum_eq_zero
  intro q _
  exact ite_eq_right (fun h=>he ⟨q,h⟩)

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RelabelMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

lemma labelCast_level {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') (l : Hierarchy.Label B s t H) :
    (labelCast s t s' t' hB hH l).1.val=l.1.val := by
  cases hB;cases hH;rfl

lemma labelsEquiv_level (w : V → V → ℚ) (K : ℕ)
    (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (labelsEquiv w K l).1.val=l.1.val := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,NumberedHierarchy.labelEquiv_level,labelCast_level]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RelabelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement
open Transport

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceLabelDecidableEq
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceBagEdgeFintype
lemma realPortion_on (w : V → V → ℝ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceRealPortion w K (sourceColoredReal w K q)=sourceRealActivity w K q := by
  classical
  exact edgeExtension_on (sourceRealEmbedding w K) (sourceRealActivity w K) q
lemma realPortion_off (w : V → V → ℝ) (K : ℕ) (e : BagEdge (sourceBags w K))
    (he : ¬∃ q,sourceColoredReal w K q=e) : sourceRealPortion w K e=0 := by
  classical
  exact edgeExtension_off (sourceRealEmbedding w K) (sourceRealActivity w K) e he
end MatchingFPRAS.Enlargement
namespace MatchingFPRAS.RationalSource
open MatchingFPRAS Transport Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal
lemma sourceEdgeEquiv_color (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (sourceEdgeEquiv w K e).color=labelsEquiv w K e.color := rfl
lemma bagHeight_cast (w : V → V → ℚ) (K : ℕ) (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (bagHeight w K (labelsEquiv w K l):ℝ)=Enlargement.bagHeight (fun x y=>(w x y:ℝ)) K l := by
  simp only [bagHeight,Enlargement.bagHeight,labelsEquiv_level]
  norm_cast
lemma realPortion_cast (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (realPortion w K (sourceEdgeEquiv w K e):ℝ)=sourceRealPortion (fun x y=>(w x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,realPortion_on,Enlargement.realPortion_on]
    exact pathActivity_cast w K q.1 q.2
  · rw [realPortion_off w K _ ?_,Enlargement.realPortion_off _ _ _ he]
    norm_num
    rintro ⟨q,hq⟩
    apply he
    refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
    rwa [sourceEdgeEquiv_real]
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_CompleteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS



lemma graph_edges_subset_complete (G : GraphInput) : G.edges ⊆ (completeGraph G.n).edges := by
  classical
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.increasing e he⟩

lemma mem_perfectMatchings (G : GraphInput) (M) : M ∈ perfectMatchings G ↔ Perfect G M := by
  classical
  simp only [perfectMatchings, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1,h⟩⟩

lemma pm_subset_complete (G : GraphInput) : perfectMatchings G ⊆ perfectMatchings (completeGraph G.n) := by
  intro M hM
  apply (mem_perfectMatchings _ _).mpr
  have h := (mem_perfectMatchings _ _).mp hM
  exact ⟨h.1.trans (graph_edges_subset_complete G), h.2⟩

lemma rawWeight_nonneg (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (M) : 0 ≤ rawWeight G x M := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> positivity

lemma rawWeight_one (G : GraphInput) (x : ℚ) (M) (hM : M ⊆ G.edges) : rawWeight G x M = 1 := by
  classical
  apply Finset.prod_eq_one
  intro e he
  simp [hM he]

lemma rawWeight_bad (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (M)
    (hM : ¬ M ⊆ G.edges) : rawWeight G x M ≤ x := by
  classical
  obtain ⟨e, he, hbad⟩ := Finset.not_subset.mp hM
  have hp : (∏ f ∈ M.erase e, if f ∈ G.edges then (1:ℚ) else x) ≤ 1 := by
    apply Finset.prod_le_one (fun f _ => by split_ifs <;> positivity)
    intro f hf
    split_ifs <;> simp_all
  change (∏ f ∈ M, if f ∈ G.edges then (1:ℚ) else x) ≤ x
  rw [← Finset.mul_prod_erase M _ he, ite_eq_right hbad]
  simpa using mul_le_mul_of_nonneg_left hp hx



theorem raw_padding_bound (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (Z G : ℚ) ≤ rawPartition G x ∧
    rawPartition G x ≤ (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
  classical
  let full := perfectMatchings (completeGraph G.n)
  let good := perfectMatchings G
  let indicator : Finset (Fin G.n × Fin G.n) → ℚ := fun M => if M ∈ good then 1 else 0
  have hind : (∑ M ∈ full, indicator M) = (Z G : ℚ) := by
    have heq := Finset.sum_subset (f := indicator) (pm_subset_complete G)
      (fun M _ hnot => ite_eq_right hnot)
    change (∑ M ∈ good, indicator M) = ∑ M ∈ full, indicator M at heq
    rw [← heq]
    simp [indicator,good,Z]
  have hlo (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : indicator M ≤ rawWeight G x M := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
    · have hi : indicator M = 0 := ite_eq_right hM
      rw [hi]
      exact rawWeight_nonneg G x hx M
  have hup (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : rawWeight G x M ≤ indicator M+x := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
      linarith
    · have hsub : ¬ M ⊆ G.edges := by
        intro hh
        apply hM
        apply (mem_perfectMatchings G M).mpr
        exact ⟨hh, ((mem_perfectMatchings (completeGraph G.n) M).mp hMF).2⟩
      have hi : indicator M = 0 := ite_eq_right hM
      rw [hi, zero_add]
      exact rawWeight_bad G x hx hx1 M hsub
  constructor
  · rw [← hind]
    exact Finset.sum_le_sum hlo
  · calc
      rawPartition G x ≤ ∑ M ∈ full, (indicator M+x) := Finset.sum_le_sum hup
      _ = (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
        rw [Finset.sum_add_distrib, hind]
        simp [Z,full]



end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StageAnalysis

open Finset MatchingFPRAS.Switching MatchingFPRAS.Initializer

variable {V : Type*} [Fintype V] [LinearOrder V]



open Finset MatchingFPRAS.Switching

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma mate_vertex_product (s : V → ℝ) (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    (∏ x ∈ univ.filter (fun x => x < m.val x),s x*s (m.val x))=∏ x ∈ Rᶜ,s x := by
  let L := univ.filter fun x => x < m.val x
  let H := univ.filter fun x => m.val x < x
  have himg : L.image m.val=H := by
    ext x
    simp only [L,H,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro hx
      exact ⟨m.val x,by simpa using hx,mate_mate m x⟩
  have hdis : Disjoint L H := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hunion : L∪H=Rᶜ := by
    ext x
    simp only [L,H,mem_union,mem_filter,mem_univ,true_and,mem_compl]
    rw [←ne_iff_lt_or_gt]
    simpa only [ne_eq,eq_comm] using not_congr (hm x)
  have hp : (∏ x ∈ L,s (m.val x))=∏ x ∈ H,s x := by
    rw [←himg]
    exact (prod_image m.property.injective.injOn).symm
  change (∏ x ∈ L,s x*s (m.val x))=_
  rw [prod_mul_distrib,hp,←prod_union hdis,hunion]

theorem weight_vertex_scaling (w : V → V → ℝ) (s : V → ℝ)
    (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    weight (fun x y => w x y*s x*s y) m=weight w m*(∏ x ∈ Rᶜ,s x) := by
  unfold weight
  rw [←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x)*s x*s (m.val x)),
    ←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x))]
  calc
    _ = (∏ x ∈ univ.filter (fun x => x < m.val x),w x (m.val x)*(s x*s (m.val x))) := by
      apply prod_congr rfl
      intro x _
      ring
    _ = _ := by rw [prod_mul_distrib,mate_vertex_product s m R hm]

theorem partition_vertex_scaling (w : V → V → ℝ) (s : V → ℝ) (R : Finset V) :
    partition (fun x y => w x y*s x*s y) R=partition w R*(∏ x ∈ Rᶜ,s x) := by
  unfold partition
  rw [sum_mul]
  exact sum_congr rfl fun m hm => weight_vertex_scaling w s m R ((mem_matchings _ _).mp hm)

end MatchingFPRAS.StageAnalysis

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

open scoped Classical

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_6
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_7
lemma sourceBagZ_pos (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz : 0 < partition w ∅) (K D : ℕ) : 0 < sourceBagZ w K D := by
  apply (sourceRealPortion_full_pos w hz K).trans_le
  apply partitionWeight_mono BagEdge.Incident _ _ (sourceRealPortion_nonneg w hw K)
  intro e
  exact le_add_of_nonneg_right (div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D))

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

lemma selected_prod {A : Type*} [CommMonoid A] (s : LogicalEdge (Fin n) → Bool)
    (w : Fin n × Fin n → A) :
    (∏ e ∈ selectedEdges s,w e)=∏ e : LogicalEdge (Fin n),if s e then w e.val else 1 := by
  rw [selectedEdges,prod_map]
  exact prod_filter (fun e => s e=true) (fun e => w e.val)

theorem weighted_partition (w : Fin n → Fin n → ℝ) :
    (∑ M ∈ perfectMatchings (completeGraph n),∏ e ∈ M,w e.1 e.2)=partition w ∅ := by
  classical
  rw [←logical_partition_eq w ∅]
  let := Fintype.ofFinite {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s}
  let := Fintype.ofFinite {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M}
  rw [Finset.sum_subtype (perfectMatchings (completeGraph n)) (mem_perfectMatchings _)]
  unfold logicalHolePartition
  symm
  apply Fintype.sum_equiv perfectEquiv
  intro s
  rw [show (perfectEquiv s).val=selectedEdges s.val from rfl,selected_prod]
  apply prod_congr rfl
  intro e _
  simp [logicalActivity,edgeActivity,source,target,e.property]

theorem raw_partition (G : GraphInput) (x : ℚ) :
    (rawPartition G x:ℝ)=partition (rawActivity G x) ∅ := by
  unfold rawPartition rawWeight
  push_cast
  rw [←weighted_partition]
  apply sum_congr rfl
  intro M hM
  apply prod_congr rfl
  intro e he
  have hi := (completeGraph G.n).increasing e (((mem_perfectMatchings (completeGraph G.n) M).mp hM).1 he)
  simp only [rawActivity,min_eq_left hi.le,max_eq_right hi.le]
  split_ifs <;> simp

end MatchingFPRAS.GraphBridge

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Marking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_2_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma markingTable_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) (i : Fin 3) :
    (markingTable w hw K D hD e).law i=portions w K D e i/bagWeight w K D e := by
  change (∑ j : Fin 3,if j=i then portions w K D e j/bagWeight w K D e else 0)=_
  simp only [sum_ite_eq',mem_univ,ite_true]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelabelMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma mass_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.mass j part (markedEquiv e he a)=Marking.mass inc (part ∘ e) a := by
  apply Fintype.prod_equiv (selectedEquiv e he a.1).symm
  intro x
  change part x.val ((markedEquiv e he a).2 x)=part (e ((selectedEquiv e he a.1).symm x).val) (a.2 ((selectedEquiv e he a.1).symm x))
  rw [←markedEquiv_mark e he a]
  simp only [Equiv.apply_symm_apply]
  congr 1
  exact (e.apply_symm_apply x.val).symm
lemma partitionWeight_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) : partitionWeight j w univ=partitionWeight inc (w ∘ e) univ := by
  classical
  unfold partitionWeight
  symm
  apply Fintype.sum_equiv (pmEquiv e he)
  intro M
  exact (matchingWeight_pmEquiv e he w M).symm
lemma law_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.law j part (markedEquiv e he a)=Marking.law inc (part ∘ e) a := by
  unfold Marking.law
  rw [mass_markedEquiv,partitionWeight_pmEquiv e he]
  rfl
end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
lemma probePortion_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (probePortion w K D (sourceEdgeEquiv w K e):ℝ)=Enlargement.probePortion (fun x y=>(w x y:ℝ)) K D e := by
  classical
  have he : (∃ q,centralEdge w K q=sourceEdgeEquiv w K e) ↔
      ∃ q,Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q=e := by
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,(sourceEdgeEquiv w K).injective ((sourceEdgeEquiv_central w K q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(sourceEdgeEquiv_central w K q).symm⟩
  simp only [probePortion,Enlargement.probePortion,he]
  split_ifs <;> push_cast <;> rfl
lemma portions_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (i : Fin 3) :
    (portions w K D (sourceEdgeEquiv w K e) i:ℝ)=sourcePortions (fun x y=>(w x y:ℝ)) K D e i := by
  fin_cases i
  · exact realPortion_cast w K e
  · change ((bagHeight w K (sourceEdgeEquiv w K e).color/D-probePortion w K D (sourceEdgeEquiv w K e):ℚ):ℝ)=_
    rw [Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,probePortion_cast,sourceEdgeEquiv_color,bagHeight_cast]
    rfl
  · exact probePortion_cast w K D e
lemma portions_collapse (w : V → V → ℚ) (K D : ℕ) :
    Marking.collapse (fun e i=>(portions w K D e i:ℝ))=fun e=>(bagWeight w K D e:ℝ) := by
  funext e
  change (∑ i : Fin 3,(portions w K D e i:ℝ))=(bagWeight w K D e:ℝ)
  exact_mod_cast portions_sum w K D e
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_1
lemma markedLaw_eq (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : Marked w K) :
    markedLaw w K D a=Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) a := by
  have hc : ∀ e,Marking.collapse (fun e i=>(portions w K D e i:ℝ)) e≠0 := by
    intro e
    rw [portions_collapse]
    dsimp only
    exact_mod_cast (bagWeight_pos w hw K D hD e).ne'
  have h:=Marking.law_from_reveal BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) hc a
  rw [portions_collapse] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [markedLaw,Variation.sigmaLift,product,gibbs,matchingWeight,partition,Marking.conditional,
    portions_collapse,Rat.cast_div,partitionWeight]
  all_goals (try congr 3)
  all_goals (try ext)
  all_goals (try simp)
lemma markedLaw_equiv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    markedLaw w K D (sourceMarkedEquiv w K a)=sourceLaw (fun x y=>(w x y:ℝ)) K D a := by
  rw [markedLaw_eq w hw K D hD]
  change Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ))
    (markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl) a)=_
  rw [law_markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)]
  have hp : ((fun e i=>(portions w K D e i:ℝ)) ∘ sourceEdgeEquiv w K)=
        sourcePortions (fun x y=>(w x y:ℝ)) K D := by
    funext e i
    exact portions_cast w K D e i
  rw [hp]
  rfl
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

lemma inputStacks_bound {A : Type} [Codec A] (a : A) : StackCost.StackBound (inputStacks a) (weight a) := by
  intro i
  have h:=weight_pos a
  cases i with
  | inr i => simp [inputStacks,encodeEnv]
  | inl i =>
    simp only [inputStacks,encodeEnv,env]
    split_ifs <;> first
    | exact le_rfl
    | simpa only [TreeData.encode,List.length_singleton] using (Nat.succ_le_iff.mpr h)

end MatchingFPRAS.TreePost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeEncodingInjective
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData
lemma encode_prefix_injective (a : Data) : ∀ b xs ys,
    encode a++xs=encode b++ys → a=b ∧ xs=ys := by
  induction a with
  | nil=>
    intro b xs ys h
    cases b with
    | nil=>simpa [encode] using h
    | cons b c=>simp [encode] at h
  | cons a c ia ic=>
    intro b xs ys h
    cases b with
    | nil=>simp [encode] at h
    | cons b d=>
      simp only [encode,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨hab,he⟩:=ia b _ _ h
      obtain ⟨hcd,hxy⟩:=ic d xs ys he
      exact ⟨congrArg₂ Data.cons hab hcd,hxy⟩
lemma encode_injective : Function.Injective encode := by
  intro a b h
  exact (encode_prefix_injective a b [] [] (by simpa using h)).1
lemma ofList_injective : Function.Injective ofList := by
  intro a
  induction a with
  | nil=>intro b h; cases b <;> simp_all [ofList]
  | cons a as ih=>
    intro b h
    cases b with
    | nil=>simp [ofList] at h
    | cons b bs=>
      obtain ⟨rfl,he⟩:=Data.cons.inj h
      rw [ih he]
lemma bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
end MatchingFPRAS.TreeData

namespace MatchingFPRAS.TreeTyped
open TreeData

lemma list_encode_injective {A : Type} [Codec A] (hf : Function.Injective (encode (A:=A))) :
    Function.Injective (encode (A:=List A)) := by
  intro a b h
  exact (List.map_injective_iff.mpr hf) (ofList_injective h)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Initializer
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

attribute [instance] Layer.finite

noncomputable local instance instDecidableEqSourceLabelFinNCastReal_2_r79c9d5_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma output_nonneg (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) : 0 ≤ output p x := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact prod_nonneg fun i _=>(layers p p.K le_rfl).ratios_nonneg x i

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Amplification
open Finset

variable {k : ℕ}

open Finset MatchingFPRAS.Adaptive MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma median_nonneg {k : ℕ} (out : Fin (2*k+1) → ℚ) (h : ∀ i,0≤out i) : 0 ≤ median out := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn out) (· ≤ ·)
  have hx : (sortedList out)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn out :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
  rw [←hi]
  exact h i

open Finset MatchingFPRAS.Adaptive
open scoped Classical

end MatchingFPRAS.Amplification

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BitComplexity

lemma PolynomiallyBounded.const (c : ℕ) : PolynomiallyBounded (fun _=>c) := by
  exact ⟨c,0,fun _ _=>by simp⟩
lemma PolynomiallyBounded.id : PolynomiallyBounded (fun x=>x) := by
  exact ⟨1,1,fun _ _=>by simp⟩
lemma PolynomiallyBounded.add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x+g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C+E,d+k,fun x hx=>?_⟩
  have h₁ : x^d≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  have h₂ : x^k≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  calc
    _ ≤ C*x^d+E*x^k := Nat.add_le_add (hf x hx) (hg x hx)
    _ ≤ C*x^(d+k)+E*x^(d+k) := Nat.add_le_add (Nat.mul_le_mul_left C h₁) (Nat.mul_le_mul_left E h₂)
    _ = _ := (Nat.add_mul _ _ _).symm
lemma PolynomiallyBounded.mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x*g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C*E,d+k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)*(E*x^k) := Nat.mul_le_mul (hf x hx) (hg x hx)
    _ = _ := by rw [pow_add]; ac_rfl
lemma PolynomiallyBounded.pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun x=>(f x)^k) := by
  obtain ⟨C,d,hf⟩:=hf
  refine ⟨C^k,d*k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)^k := Nat.pow_le_pow_left (hf x hx) k
    _ = _ := by rw [mul_pow,pow_mul]
open Transport

end MatchingFPRAS.BitComplexity

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Guard
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WeightedOptions
open Finset FiniteChoice

lemma draw_law_pos {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : WeightedOptions Ω) (k : ℕ) (bits : Fin k → Bool) :
    0 < c.law (c.draw k bits) := by
  let i := chooseBits c.mass c.total k bits
  have hi : 0 < c.mass i := chooseBits_pos c.mass c.total k bits
  apply hi.trans_le
  unfold law
  calc
    c.mass i = (if c.out i = c.draw k bits then c.mass i else 0) := by simp [draw, i]
    _ ≤ ∑ j, if c.out j = c.draw k bits then c.mass j else 0 :=
      single_le_sum (f := fun j => if c.out j = c.draw k bits then c.mass j else 0)
        (fun j _ => by split_ifs <;> [exact c.nonneg j; exact le_rfl]) (mem_univ i)

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Enlargement
open Finset Switching Subdivision RealGeometry MatchingFPRAS.Representation

theorem intact_partition_identity_even {V : Type*} [Fintype V] [LinearOrder V]
    (he : Even (Fintype.card V)) (w : V → V → ℝ)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hz := StageAnalysis.partition_pos_of_even (fun _ _ : V => (1:ℝ)) (by intros; norm_num) ∅
    (by simpa using he)
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition (fun _ _ : V => (1:ℝ)) ∅ = 0 := by
      simp [partition, Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m, hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles, broken, deletionConstant, List.prod_ofFn, pathConstant,
    logical_partition_eq] using hid

open Transport
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_11
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_12
theorem frozenPortion_full_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (K : ℕ) :
    Transport.partitionWeight BagEdge.Incident (frozenPortion w w₁ K) Finset.univ =
      sourceC w K * Switching.partition w₁ ∅ := by
  rw [←survivors_empty (V:=V) K, frozenPortion_partition,
    intact_partition_identity_even he w₁]
  rfl

theorem observableD_mean_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y) (K D : ℕ) :
    (∑ a : SourceMarked w K, sourceLaw w K D a * observableD w w₁ K a) =
      sourceC w K * Switching.partition w₁ ∅ / sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (bagReweight w w₁ K)
  simp only [sourcePortions, Matrix.cons_val_zero] at h
  rw [bagReweight_identity w w₁ hw K, frozenPortion_full_even he w w₁] at h
  simpa only [sourceLaw, observableD, sourcePortions_collapse, sourceBagZ] using h

theorem observableD_zero_of_partition_zero (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y)
    (hw₁ : ∀ x y, 0 ≤ w₁ x y) (hle : ∀ x y, w₁ x y ≤ w x y)
    (hz : 0 < Switching.partition w ∅) (K D : ℕ)
    (hz₁ : Switching.partition w₁ ∅ = 0) (a : SourceMarked w K)
    (ha : 0 < sourceLaw w K D a) : observableD w w₁ K a = 0 := by
  have hB : 0 < sourceBagZ w K D := sourceBagZ_pos w hw hz K D
  have hmean := observableD_mean_even he w w₁ hw K D
  rw [hz₁, mul_zero, zero_div] at hmean
  have hnonneg (b : SourceMarked w K) : 0 ≤ sourceLaw w K D b * observableD w w₁ K b :=
    mul_nonneg (sourceLaw_nonneg w hw K D hB.le b)
      (observableD_range w w₁ hw hw₁ hle K b).1
  have hz' := (sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hmean a (mem_univ a)
  exact (mul_eq_zero.mp hz').resolve_left ha.ne'

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.TableMarking
open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
variable (inc : E → V → Prop)
variable {A : Type*} [Fintype A] [Nonempty A]

omit [Fintype A] [Nonempty A] [DecidableEq E] in
lemma draw_law_pos [DecidableEq E] (f : A → PM inc) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (c : E → WeightedOptions I) (k : ℕ) (bits : A × (E → Fin k → Bool)) :
    0 < law inc w c (draw inc f c k bits) := by
  classical
  change 0 < gibbs w (f bits.1) * ∏ e : (f bits.1).val, ((c e.val).law ((c e.val).draw k (bits.2 e.val)) : ℝ)
  apply mul_pos (gibbs_pos w hw _)
  exact Finset.prod_pos fun e _ => by exact_mod_cast (c e.val).draw_law_pos k (bits.2 e.val)

end MatchingFPRAS.TableMarking

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelCastReal_5_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_5_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_6_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma marking_law_eq (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y)
    (K D : ℕ) (hD : 0 < D) :
    TableMarking.law BagEdge.Incident (fun e => (bagWeight w K D e : ℝ))
      (markingTable w hw K D hD) = markedLaw w K D := by
  funext a
  simp only [TableMarking.law, markedLaw, Variation.sigmaLift, Variation.product, TableMarking.portion, markingTable_law]

theorem source_draw_support {A : Type*} [Fintype A] [Nonempty A]
    (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y) (K D k : ℕ) (hD : 0 < D)
    (f : A → BagPM (bags w K)) (bits : A × (BagEdge (bags w K) → Fin k → Bool)) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      ((sourceMarkedEquiv w K).symm
        (TableMarking.draw BagEdge.Incident f (markingTable w hw K D hD) k bits)) := by
  rw [←markedLaw_equiv w hw K D hD, Equiv.apply_symm_apply, ←marking_law_eq w hw K D hD]
  apply TableMarking.draw_law_pos
  intro e
  exact_mod_cast bagWeight_pos w hw K D hD e

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.GraphBridge
open Finset Switching

lemma unpadded_partition (G : GraphInput) :
    partition (rawActivity G 0) ∅ = (Z G : ℝ) := by
  have h := raw_padding_bound G 0 (by norm_num) (by norm_num)
  have he : rawPartition G 0 = (Z G : ℚ) := le_antisymm (by simpa using h.2) h.1
  have hc := raw_partition G 0
  rw [he] at hc
  simpa using hc.symm

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial
open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} {j K : ℕ} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_2_r79c9d5_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_nonneg (s : ScaleState G j) (a b : Fin G.n) :
    0 ≤ s.certificateActivity a b := by
  unfold ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs
  · simpa only [one_mul] using mul_nonneg (s.positive a).le (s.positive b).le
  · simp

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_le (s : ScaleState G j) (a b : Fin G.n) :
    s.certificateActivity a b ≤ s.activity a b := by
  unfold ScaleState.certificateActivity ScaleState.activity raw GraphBridge.rawActivity
  split_ifs
  · rfl
  · simp only [zero_mul]
    exact mul_nonneg (mul_nonneg (pow_pos (cooling_pos G.n) j).le (s.positive a).le) (s.positive b).le

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_partition (s : ScaleState G j) :
    Switching.partition s.certificateActivity ∅ = (Z G : ℝ) * ∏ i, s.scale i := by
  change Switching.partition (fun a b => GraphBridge.rawActivity G 0 a b * s.scale a * s.scale b) ∅ = _
  rw [partition_vertex_scaling, GraphBridge.unpadded_partition]
  simp

theorem ScaleState.certificate_zero (s : ScaleState G j) (he : Even G.n)
    (hZ : Z G = 0) (D : ℕ) (a : SourceMarked s.activity K)
    (ha : 0 < sourceLaw s.activity K D a) :
    observableD s.activity s.certificateActivity K a = 0 := by
  apply observableD_zero_of_partition_zero (by simpa using he) s.activity s.certificateActivity
    s.activity_pos s.certificateActivity_nonneg s.certificateActivity_le
    (s.partition_pos he) K D
  · rw [s.certificateActivity_partition, hZ]
    simp
  · exact ha

open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

end MatchingFPRAS.Trial

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqSourceLabelCastReal_6_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_6_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_7_r79c9d5_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
theorem fixedSampler_support (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (bits : Fin (totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊) → Bool) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      (fixedSampler w hw K D m hD hN h hq M η bits) := by
  simp only [fixedSampler, padSampler, bitSampler, Function.comp_apply, markedSampler]
  exact source_draw_support w hw K D _ hD _ _

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_GuardProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_6_r79c9d5_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_cast [Nontrivial (Fin G.n)] {j : ℕ} (s : ScaleState G j) :
    (fun a b => (s.certificateActivity a b : ℝ)) = s.toReal.certificateActivity := by
  funext a b
  unfold ScaleState.certificateActivity Trial.ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs <;> simp [ScaleState.toReal]

lemma ScaleState.certificate_cast {j : ℕ} (s : ScaleState G j) (K : ℕ)
    (a : SourceMarked (fun x y => (s.activity x y : ℝ)) K) :
    (s.certificate K a : ℝ) = observableD (fun x y => (s.activity x y : ℝ))
      (fun x y => (s.certificateActivity x y : ℝ)) K a :=
  RationalSource.observableD_cast _ _ _ _

theorem ScaleState.drawOne_certificate_zero (p : Trial.Parameters G) {j : ℕ}
    (hj : j ≤ p.K) (s : ScaleState G j) (hZ : Z G = 0) (b : Fin (oneBits p) → Bool) :
    s.certificate p.K (s.drawOne p hj b) = 0 := by
  have hs : 0 < sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D (s.drawOne p hj b) :=
    RationalSource.fixedSampler_support _ _ _ _ _ _ _ _ _ _ _ _
  have hc := s.toReal.certificate_zero (K:=p.K) p.even hZ p.D
  rw [←s.activity_cast, ←s.certificateActivity_cast] at hc
  have hh := hc (s.drawOne p hj b) hs
  rw [←s.certificate_cast] at hh
  exact_mod_cast hh

end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_7_r79c9d5_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma guardedOutput_nonneg (p : Trial.Parameters G) (x : GuardedTrial p) : 0 ≤ guardedOutput p x := by
  unfold guardedOutput
  split_ifs
  · exact output_nonneg _ _
  · rfl

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_const {A : Type} [Fintype A] [Nonempty A] (q : ℚ) :
    qaverage (fun _ : A=>q)=q := by
  simp only [qaverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card A:ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_GuardBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive Amplification Finset
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_8_r79c9d5_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma ScaleState.drawGuard_no_certificate (p : Trial.Parameters G) (s : ScaleState G p.K)
    (hZ : Z G = 0) (b : Fin (guardBits p) → Bool) : ¬guardPass p s (s.drawGuard p b) := by
  dsimp only [guardBits] at b
  dsimp only [guardPass, ScaleState.drawGuard, guardBits, Function.comp_apply]
  simp only [s.drawOne_certificate_zero p le_rfl hZ, lt_self_iff_false, exists_const, not_false_eq_true]

theorem guardedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (b : Fin (guardedBits p) → Bool) :
    guardedBitOutput p b=0 := by
  unfold guardedBitOutput drawGuarded
  simp only [Function.comp_apply, guardedOutput]
  exact ite_eq_right (ScaleState.drawGuard_no_certificate p _ hZ _)

lemma guardedAmplifiedBitOutput_nonneg (p : Trial.Parameters G) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : 0≤guardedAmplifiedBitOutput p δ b :=
  median_nonneg _ (fun _=>guardedOutput_nonneg p _)

omit [Nontrivial (Fin G.n)] in
lemma median_eq_of_constant {k : ℕ} (x : Fin (2*k+1) → ℚ) (a : ℚ) (hx : ∀ i,x i=a) : median x=a := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn x) (· ≤ ·)
  have hm : (sortedList x)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn x :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  rw [←hi, hx]

theorem guardedAmplifiedBitOutput_zero (p : Trial.Parameters G) (hZ : Z G=0) (δ : ℚ)
    (b : Fin (guardedAmplifiedBits p δ) → Bool) : guardedAmplifiedBitOutput p δ b=0 := by
  apply median_eq_of_constant
  intro i
  exact guardedBitOutput_zero p hZ _

end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

lemma count_empty_graph {G : GraphInput} (hn : G.n=0) : Z G=1 := by
  classical
  have hv (v : Fin G.n) : False := by have := v.isLt; omega
  have he : G.edges=∅ := Finset.eq_empty_of_forall_notMem (fun e _=>hv e.1)
  have hp : Perfect G ∅ := ⟨Finset.empty_subset _,fun v=>False.elim (hv v)⟩
  simp only [Z,perfectMatchings,he,Finset.powerset_empty]
  have hf : Finset.filter (Perfect G) {∅}=({∅} : Finset (Finset (Fin G.n×Fin G.n))) := by
    ext M
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl,hp⟩
  rw [hf]
  rfl

end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma weight_word (as : List Symbol) : weight as=18*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [weight_cons,weight_symbol,ih,List.length_cons]; omega

lemma natWord_eq (n : ℕ) : natWord n=encodeNat n := rfl

lemma ratWord_repr (q : ℚ) (hq : 0≤q) : ratWord (TreeFraction.repr q)=encodeRat q := by
  have hn : ¬q.num<0 := not_lt.mpr (Rat.num_nonneg.mpr hq)
  simp only [ratWord,TreeFraction.repr,natWord_eq,encodeRat,encodeInt,ite_eq_right hn,List.singleton_append]
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Parse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
lemma encodeInt_fold (z : ℤ) (ns : List ℕ) :
    (encodeInt z).foldr (fun a ns=>numStep (a,ns)) ns=z.natAbs::ns := by
  unfold encodeInt
  rw [List.foldr_append,encodeNat_fold]
  split_ifs <;> simp [numStep]
lemma encodeRat_fold (q : ℚ) (ns : List ℕ) :
    (encodeRat q).foldr (fun a ns=>numStep (a,ns)) ns=q.num.natAbs::q.den::ns := by
  rw [encodeRat,List.foldr_append,encodeNat_fold,encodeInt_fold]
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Input
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped TreeFunction Polynomial LiteralParse

lemma pair_pair (i j : ℕ) (es : List (ℕ×ℕ)) :
    pairStep (i,pairStep (j,((false,0),es)))=((false,0),(i,j)::es) := rfl
lemma pairs_reverse (es : List (ℕ×ℕ)) (acc : List (ℕ×ℕ)) :
    ((es.flatMap (fun e=>[e.1,e.2])).reverse.foldl (fun s n=>pairStep (n,s)) ((false,0),acc))=
      ((false,0),es++acc) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,pair_pair]
    rfl

lemma edges_fold (es : List (ℕ×ℕ)) (ns : List ℕ) :
    (es.flatMap (fun e=>encodeNat e.1++encodeNat e.2)).foldr (fun a ns=>numStep (a,ns)) ns=
      es.flatMap (fun e=>[e.1,e.2])++ns := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold]
    rfl
lemma parse_source (G : GraphInput) (ε δ : ℚ) : LiteralParse.parse (encodeInput G ε δ)=
    G.n::G.edges.card::(edgeNumbers G).flatMap (fun e=>[e.1,e.2])++[ε.num.natAbs,ε.den,δ.num.natAbs,δ.den] := by
  unfold encodeInput LiteralParse.parse
  simp only [List.foldr_append,encodeNat_fold,encodeRat_fold]
  rw [show (((G.edges.map toLex.toEmbedding).sort (·≤·)).flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val)=
    (edgeNumbers G).flatMap (fun e=>encodeNat e.1++encodeNat e.2) by simp only [edgeNumbers,List.flatMap_map]]
  rw [edges_fold]
  rfl
lemma parseInput_source (G : GraphInput) (ε δ : ℚ) :
    parseInput (encodeInput G ε δ)=(G.n,(edgeNumbers G,(TreeFraction.repr ε,TreeFraction.repr δ))) := by
  rw [parseInput,parse_source]
  unfold fromNumbers
  simp only [List.cons_append,List.headD_cons,List.tail_cons,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
  unfold ratTail
  simp only [List.headD_cons,List.tail_cons]
  unfold pairs
  rw [pairs_reverse]
  simp only [List.append_nil]
  rfl
end MatchingFPRAS.LiteralInput

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma edgeNumbers_length (G : GraphInput) : (edgeNumbers G).length=G.edges.card := by
  simp only [edgeNumbers,List.length_map,Finset.length_sort,Finset.card_map]
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A B : Type}
lemma All.and {p : Experiment A} {P Q : A→Prop} (hp : p.All P) (hq : p.All Q) :
    p.All (fun a=>P a ∧ Q a) := by
  induction p with
  | done a => exact ⟨hp,hq⟩
  | read p ih => exact ⟨ih false hp.1 hq.1,ih true hp.2 hq.2⟩
  | delay n p ih => exact ih hp hq
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineHistoryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
lemma all_of_qaverage {A B : Type} [Fintype B] [Nonempty B] (p : Experiment A) (f : B→A)
    (hm : ∀ h,p.mean h=qaverage (h ∘ f)) (P : A→Prop) (hf : ∀ b,P (f b)) : p.All P := by
  classical
  rw [all_indicator,hm]
  calc
    _=qaverage (fun _ : B=>(0:ℚ)) := by
      apply qaverage_congr
      intro b
      simp only [Function.comp_apply,ite_eq_left (hf b)]
    _=0 := qaverage_const 0
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AlgorithmLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
namespace Experiment
lemma mean_mono {A : Type} (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a≤g a)) : p.mean f≤p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => exact div_le_div_of_nonneg_right (add_le_add (ih false h.1) (ih true h.2)) (by norm_num)
end Experiment
end MatchingFPRAS.PhysicalStream

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

lemma empty_source (G : GraphInput) (ε δ : ℚ) : empty (parseInput (encodeInput G ε δ))=decide (G.n=0) := by
  rw [parseInput_source];rfl
lemma invalid_source (G : GraphInput) (ε δ : ℚ) : invalid (parseInput (encodeInput G ε δ))=
    (!(decide (G.n%2=0)) || decide (2*G.edges.card<G.n)) := by
  rw [parseInput_source]
  simp only [invalid,ExecutableInput.tooSparse,edgeNumbers_length]
lemma valid_even (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) : Even G.n := by
  rw [invalid_source] at h
  by_contra he
  have he' : ¬G.n%2=0 := fun hm=>he (Nat.even_iff.mpr hm)
  simp only [he',decide_false,Bool.not_false,Bool.true_or,Bool.true_eq_false] at h
lemma valid_two (G : GraphInput) (ε δ : ℚ) (he : empty (parseInput (encodeInput G ε δ))=false)
    (hi : invalid (parseInput (encodeInput G ε δ))=false) : 2≤G.n := by
  have h0 := of_decide_eq_false (show decide (G.n=0)=false by rwa [empty_source] at he)
  have hev:=Nat.even_iff.mp (valid_even G ε δ hi)
  omega

lemma algorithm_proper (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ) :
    (algorithm (encodeInput G ε δ)).All (Proper G) := by
  unfold algorithm
  rw [Experiment.all_map]
  have hen : LiteralCodec.ratWord (1,1)=encodeRat 1 := LiteralCodec.ratWord_repr 1 (by norm_num)
  have hzero : LiteralCodec.ratWord (0,1)=encodeRat 0 := LiteralCodec.ratWord_repr 0 (by norm_num)
  cases hE:empty (parseInput (encodeInput G ε δ)) with
  | true =>
    have hn : G.n=0 := of_decide_eq_true (by rwa [empty_source] at hE)
    have hz:=count_empty_graph hn
    simp only [count,hE,ite_true,Experiment.All]
    exact ⟨1,by norm_num,hen,by intro h;omega⟩
  | false =>
    cases hI:invalid (parseInput (encodeInput G ε δ)) with
    | true =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false,ite_true,Experiment.All]
      exact ⟨0,by norm_num,hzero,fun _=>rfl⟩
    | false =>
      simp only [count,hE,hI,Bool.false_eq_true,ite_false]
      have hn:=valid_two G ε δ hE hI
      have hev:=valid_even G ε δ hI
      let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
      apply Experiment.all_of_qaverage _ (fun b=>TreeFraction.repr
        (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b))
      · exact compute_mean hn hev ε δ he he1 hd
      · intro b
        let p:=FiniteTrial.parameters G hn hev ε he he1
        have hq:=FiniteTrial.guardedAmplifiedBitOutput_nonneg p δ b
        exact ⟨_,hq,LiteralCodec.ratWord_repr _ hq,fun hz=>FiniteTrial.guardedAmplifiedBitOutput_zero p hz δ b⟩

end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalSequential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

lemma tick_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (q : Q) (T : Tape Γ) (b : Bool) :
    tick (seq M N r₀) (leftCfg r₀ ⟨some q,T⟩) b=leftCfg r₀ (tick M ⟨some q,T⟩ b) := by
  cases h : M q T.head b with
  | none => simp only [tick,leftCfg,seq,h,Option.elim_some,Option.elim_none,Tape.write_self]
  | some qa => rcases qa with ⟨q',act⟩;cases act <;> simp only [tick,leftCfg,seq,h,Option.elim_some]
lemma tick_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (c : Cfg Γ R) (b : Bool) :
    tick (seq M N r₀) (rightCfg c) b=rightCfg (tick N c b) := by
  rcases c with ⟨s,T⟩
  cases s with
  | none => rfl
  | some r =>
    cases h:N r T.head b with
    | none => simp only [tick,rightCfg,Option.map_some,seq,h,Option.map_none]
    | some ra => rcases ra with ⟨r',act⟩;cases act <;> simp only [tick,rightCfg,seq,h,Option.map_some]
lemma execute_right (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ R) (b : Stream) :
    execute (seq M N r₀) n (rightCfg c) b=rightCfg (execute N n c b) := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih => rw [execute,tick_right,ih,execute]
lemma Implements.right {M : Table Γ Q} {N : Table Γ R} (r₀ : R) {out : α→Cfg Γ R}
    {c : Cfg Γ R} {p : Experiment α} (h : Implements N out c p) :
    Implements (seq M N r₀) (rightCfg ∘ out) (rightCfg c) p := by
  induction h with
  | done a => exact .done a
  | read c f h ih => apply Implements.read;intro b;rw [tick_right];exact ih b
  | delay c d n p hs hr ih =>
    exact .delay _ _ n _ (fun b=>by rw [execute_right,hs]) ih

lemma early_cost (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : (early M n c).cost≤n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    cases h:c.state <;> simp only [early,h,Experiment.cost]
    · omega
    · have h0:=ih (tick M c false); have h1:=ih (tick M c true); omega
lemma early_run (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (b : Stream) :
    ((early M n c).run b).1=execute M n c b := by
  induction n generalizing c b with
  | zero => rfl
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => rw [execute_halted];rfl
    | some q => simp only [early,Experiment.run,execute];exact ih _ _
lemma early_mean (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=average (fun b : Bits n=>f (execute M n c (extend b))) := by
  simpa only [early_run] using (Experiment.average_run (early M n c) f n (early_cost M n c)).symm
lemma early_left (M : Table Γ Q) (N : Table Γ R) (r₀ : R) (n : ℕ) (c : Cfg Γ Q) :
    Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q =>
      apply Implements.read
      intro b
      rw [tick_left]
      exact ih _
lemma Implements.early_mean {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) (f : Cfg Γ Q→ℚ) :
    (early M n c).mean f=p.mean (fun a=>f (out a)) := by
  rw [PhysicalPost.early_mean]
  exact h.fair_law halt n hn f
lemma Implements.bind_all {M : Table Γ Q} {out : α→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment α} (h : Implements M out c p) (q : α→Experiment β) (out' : β→Cfg Γ Q)
    (hq : p.All (fun a=>Implements M out' (out a) (q a))) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq
  | read c f h ih => exact .read c _ (fun b=>by cases b;exact ih false hq.1;exact ih true hq.2)
  | delay c d n p hs hr ih => exact .delay c d n _ hs (ih hq)
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TapeTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma mk₂_left_nil (R : List Γ) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (default::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk,ListBlank.tail_mk,ListBlank.head_mk]
lemma blank_zero (n : ℕ) : (ListBlank.mk (List.replicate n (default : Γ)))=ListBlank.mk [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,←ListBlank.cons_mk,ih]; exact ListBlank.cons_head_tail (ListBlank.mk [])
lemma blank_append_zero (L : List Γ) (n : ℕ) :
    ListBlank.mk (L++List.replicate n default)=ListBlank.mk L := by
  induction L with
  | nil => exact blank_zero n
  | cons a L ih => rw [List.cons_append,←ListBlank.cons_mk,ih,ListBlank.cons_mk]

lemma Exec.refl (M : Λ→TM1.Stmt Γ Λ σ) (c : TM1.Cfg Γ Λ σ) : Exec M c c 0 := ⟨0,le_rfl,rfl⟩
lemma Exec.step (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) (T : Tape Γ) :
    Exec M ⟨some l,v,T⟩ (TM1.stepAux (M l) v T) 1 := ⟨1,le_rfl,rfl⟩
lemma Exec.trans {M : Λ→TM1.Stmt Γ Λ σ} {c d e : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (g : Exec M d e t) : Exec M c e (s+t) := by
  obtain ⟨i,hi,he⟩:=h
  obtain ⟨j,hj,hf⟩:=g
  exact ⟨i+j,Nat.add_le_add hi hj,by rw [MachineCost.run_add,he,hf]⟩
lemma Exec.mono {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {s t : ℕ}
    (h : Exec M c d s) (hst : s≤t) : Exec M c d t :=
  let ⟨k,hk,he⟩:=h; ⟨k,hk.trans hst,he⟩

lemma select_step [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) (v : σ) (hv : v∈vs) (T : Tape Γ) :
    TM1.stepAux (select vs f fallback) v T=TM1.stepAux (f v) v T := by
  induction vs with
  | nil => simp at hv
  | cons a as ih =>
    simp only [List.mem_cons] at hv
    simp only [select,List.foldr_cons,TM1.stepAux]
    by_cases h:v=a
    · simp only [h,decide_true,Bool.cond_true]
    · simp only [h,decide_false,Bool.cond_false]
      exact ih (hv.resolve_left h)

lemma writeLeft_step (xs : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) (R : List Γ) :
    TM1.stepAux (writeLeft xs q) v (Tape.mk₂ [] (default::R))=
      TM1.stepAux q v (Tape.mk₂ [] (default::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeLeft,List.foldr_cons,TM1.stepAux,mk₂_write,mk₂_left_nil]
    rw [show List.foldr (fun a tail=>TM1.Stmt.write (fun _ _=>a) (.move .left tail)) q bs=writeLeft bs q from rfl,ih]
    simp only [List.reverse_cons,List.cons_append,List.append_assoc,List.nil_append]

lemma eraseToLeft_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseToLeft xs.length q) v (Tape.mk₂ (xs++L) R)=
      TM1.stepAux q v (Tape.mk₂ L (List.replicate xs.length default++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseToLeft,TM1.stepAux,List.cons_append,mk₂_left,mk₂_write]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.move .left (.write (fun _ _=>default) tail)) xs.length=eraseToLeft xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

variable {I : Type} [DecidableEq I]
lemma grab_step (is : List I) (f v : I→Γ) (q : TM1.Stmt Γ Λ (I→Γ)) (L R : List Γ) :
    TM1.stepAux (grab is q) v (Tape.mk₂ L (is.map f++R))=
      TM1.stepAux q (is.foldl (fun v i=>Function.update v i (f i)) v)
        (Tape.mk₂ ((is.map f).reverse++L) R) := by
  induction is generalizing v L with
  | nil => rfl
  | cons i is ih =>
    simp only [grab,List.foldr_cons,List.map_cons,List.cons_append,TM1.stepAux,mk₂_head,mk₂_right,List.foldl_cons]
    rw [show List.foldr (fun i tail=>TM1.Stmt.load (fun a v=>Function.update v i a) (.move .right tail)) q is=grab is q from rfl,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
omit [Inhabited Γ] in
lemma fold_updates (is : List I) (f v : I→Γ) (i : I) :
    (is.foldl (fun v i=>Function.update v i (f i)) v) i=if i∈is then f i else v i := by
  induction is generalizing v with
  | nil => simp
  | cons a is ih =>
    rw [List.foldl_cons,ih]
    by_cases hi:i∈is <;> by_cases ha:i=a <;> simp [hi,ha]
lemma grab_fin (n : ℕ) (f v : Fin n→Γ) (q : TM1.Stmt Γ Λ (Fin n→Γ)) (L R : List Γ) :
    TM1.stepAux (grab (List.finRange n) q) v (Tape.mk₂ L (List.ofFn f++R))=
      TM1.stepAux q f (Tape.mk₂ ((List.ofFn f).reverse++L) R) := by
  have he : (List.finRange n).map f=List.ofFn f := List.ofFn_eq_map.symm
  rw [←he,grab_step]
  have hf : (List.finRange n).foldl (fun v i=>Function.update v i (f i)) v=f := by
    funext i
    rw [fold_updates]
    simp
  rw [hf]
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Physical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
omit [Inhabited Λ] [Fintype σ] [Inhabited σ] in
lemma Exec.physical {M : Λ→TM1.Stmt Γ Λ σ} {c d : TM1.Cfg Γ Λ σ} {t : ℕ}
    (h : Exec M c d t) : ∃ k,k≤t*programCost M ∧ ∀ b : Stream,
      PhysicalPost.execute (table M) k (CoinTM1.trCfg c) b=CoinTM1.trCfg d := by
  obtain ⟨n,hn,he⟩:=h
  have hp:=SafeTrace.Path.of_run (safe:=fun _=>True) (M:=M) n c (fun _ _ _ _=>trivial)
  rw [he] at hp
  obtain ⟨k,hk,hb⟩:=hp.physical (fun _=>none) (fun _ _=>rfl) (programCost M)
    (fun l _=>statementCost_le_programCost M l)
  exact ⟨k,hk.trans (Nat.mul_le_mul_right _ hn),hb⟩
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma mean_congr_all (p : Experiment A) (f g : A→ℚ) (h : p.All (fun a=>f a=g a)) : p.mean f=p.mean g := by
  induction p with
  | done a => exact h
  | delay n p ih => exact ih h
  | read p ih => simp only [mean,ih false h.1,ih true h.2]
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]
lemma Implements.map_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (f : A→B) (out' : B→Cfg Γ Q)
    (he : p.All (fun a=>out a=out' (f a))) : Implements M out' c (p.map f) := by
  induction h with
  | done a => rw [he];exact .done (f a)
  | read c p h ih => exact .read _ _ (fun b=>by cases b;exact ih false he.1;exact ih true he.2)
  | delay c d n p hs hr ih => exact .delay _ _ n _ hs (ih he)
lemma early_implements (M : Table Γ Q) (n : ℕ) (c : Cfg Γ Q) : Implements M id c (early M n c) := by
  induction n generalizing c with
  | zero => exact .done c
  | succ n ih =>
    rcases c with ⟨s,T⟩
    cases s with
    | none => exact .done _
    | some q => exact .read _ _ (fun b=>ih _)
lemma Implements.early_all {M : Table Γ Q} {out : A→Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost≤n) : (early M n c).All (fun d=>d.state=none) := by
  apply Experiment.all_of_mean_eq (p:=(p.map out)) (fun f=>by rw [Experiment.mean_map];exact h.early_mean halt n hn f)
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun a _=>halt a)

namespace Program
lemma earlyTapes_cost (P : Program) (n : ℕ) (T : Tape Symbol) : (P.earlyTapes n T).cost≤n := by
  rw [earlyTapes,Experiment.cost_map];exact early_cost _ _ _
lemma Realizes.early {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) :
    Implements P.table P.final (P.initial input) (P.earlyTapes N input) ∧
      (∀ w,(P.earlyTapes N input).mean w=f.mean w) := by
  obtain ⟨p,hp,hm,hc⟩:=h
  refine ⟨?_,fun w=>?_⟩
  · apply (early_implements P.table N (P.initial input)).map_all Cfg.tape P.final
    exact (hp.early_all (fun _=>rfl) N hc).mono (by intro d hd;cases d; simp only [id_eq,final] at *;cases hd;rfl)
  · rw [earlyTapes,Experiment.mean_map,hp.early_mean (fun _=>rfl) N hc]
    exact hm w
lemma seq_realizes (P R : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol))
    (g : Tape Symbol→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input f N) (hR : f.All (fun T=>R.Realizes T (g T) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  let p:=early P.table N (P.initial input)
  let q:=fun c : Cfg Symbol P.State=>R.earlyTapes S c.tape
  have hmean (h : Cfg Symbol P.State→ℚ) : p.mean h=f.mean (fun T=>h (P.final T)) := by
    obtain ⟨v,hv,hm,hc⟩:=hP
    rw [hv.early_mean (fun _=>rfl) N hc]
    exact hm _
  have hall : p.All (fun c=>c.state=none ∧ R.Realizes c.tape (g c.tape) S) := by
    apply Experiment.all_of_mean_eq (p:=f.map P.final) (fun h=>by rw [Experiment.mean_map];exact hmean h)
    rw [Experiment.all_map]
    exact hR.mono (fun T hT=>⟨rfl,hT⟩)
  have himpl : Implements (P.seq R).table (fun T=>rightCfg (R.final T))
      ((P.seq R).initial input) (p.bind q) := by
    apply (early_left P.table R.table R.entry N (P.initial input)).bind_all q _
    exact hall.mono (by
      intro c hc
      have hq:=(hc.2.early).1.right (M:=P.table) R.entry
      have he:leftCfg R.entry c=rightCfg (R.initial c.tape) := by
        rcases c with ⟨s,T⟩;simp only at hc;cases hc.1;rfl
      rw [he]
      exact hq)
  refine ⟨p.bind q,himpl,?_,?_⟩
  · intro w
    rw [Experiment.mean_bind,hmean,Experiment.mean_bind]
    apply Experiment.mean_congr_all
    exact hR.mono (fun T hT=>hT.early.2 w)
  · exact (Experiment.cost_bind_le p q S (fun c=>earlyTapes_cost R S c.tape)).trans
      (Nat.add_le_add_right (early_cost _ N _) S)

lemma realizes_TM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v v' : σ) (input output : Tape Symbol) (n : ℕ)
    (he : LiteralTape.Exec M ⟨some l,v,input⟩ ⟨none,v',output⟩ n) :
    (ofTM1 M l v).Realizes input (.done output) (n*MachineCost.programCost M) := by
  obtain ⟨k,hk,hb⟩:=he.physical
  refine ⟨.delay k (.done output),?_,fun _=>rfl,by simpa only [Experiment.cost,Nat.add_zero] using hk⟩
  exact .delay _ _ k _ hb (.done output)
end Program
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open Turing TreeTyped TreeData TreeFunction TreeMachine TreePost PhysicalPost PhysicalStream

lemma input_height {A : Type} [Codec A] (a : A) : OnlineStack.height (inputStacks a)=weight a := by
  apply le_antisymm
  · exact Finset.sup_le (fun k _=>inputStacks_bound a k)
  · have h:=OnlineStack.height_bound (inputStacks a) (Sum.inl (0 : Reg))
    simpa only [inputStacks,encodeEnv,env,ite_true,weight,TreeFunction.size] using h

lemma cfg_packed {A : Type} [Codec A] (P : OnlineProc.Proc (K Reg)) (a : A) (l : Option P.Label) :
    upCfg (OnlineStack.cfg (⟨l,none,inputStacks a⟩ : StoreCfg P))=
      ⟨l.map (fun u=>(Sum.inl (TM1to1.Λ'.normal (TM2to1.Λ'.normal u)),none)),Tape.mk₁ (packed a)⟩ := by
  simp only [upCfg,OnlineStack.cfg,OnlineStack.stackCfg,input_height,CoinTM1.trCfg,
    TM1to1.trCfg,TM1to1.trTape,TM1to1.trTape',Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,
    ListBlank.flatMap_mk,List.flatMap_nil,Option.map_map]
  rw [Tape.map_mk']
  rfl

lemma physical_realizes {A B : Type} [Codec A] [Codec B]
    {f : A→Experiment B} (F : Realizer f) (a : A) :
    (physicalProgram F).Realizes (Tape.mk₁ (packed a))
      ((f a).map (fun b=>Tape.mk₁ (packed b))) (physicalCost F a) := by
  obtain ⟨p,hp,hm,hc⟩:=F.correct a .nil
  obtain ⟨q,hq,hqm,hqc⟩:=hp.compile (weight a) (inputStacks_bound a)
  have he:=hq.up
  have hi : upCfg (OnlineStack.cfg (initial F.program (encode a) .nil))=
      (physicalProgram F).initial (Tape.mk₁ (packed a)) := cfg_packed F.program a (some default)
  have ho (b : B) : upCfg (OnlineStack.cfg (final F.program (encode b) .nil))=
      (physicalProgram F).final (Tape.mk₁ (packed b)) := cfg_packed F.program b none
  rw [hi] at he
  simp_rw [ho] at he
  refine ⟨q.map (fun b=>Tape.mk₁ (packed b)),?_,?_,?_⟩
  · exact he.map_all _ _ (Experiment.all_true _ |>.mono (fun _ _=>rfl))
  · intro w
    rw [Experiment.mean_map,hqm,hm,Experiment.mean_map]
  · rw [Experiment.cost_map]
    exact hqc.trans (Nat.mul_le_mul hc (OnlineStack.Executes.factor_mono _ _ _ _ le_rfl hc))
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProgramMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma Realizes.congr {P : Program} {input : Tape Symbol} {f g : Experiment (Tape Symbol)} {N : ℕ}
    (h : P.Realizes input f N) (he : ∀ w,f.mean w=g.mean w) : P.Realizes input g N := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,fun w=>(hm w).trans (he w),hc⟩
lemma Realizes.mono {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N S : ℕ}
    (h : P.Realizes input f N) (hn : N≤S) : P.Realizes input f S := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,hm,hc.trans hn⟩
lemma seq_realizes_map {A : Type} (P R : Program) (input : Tape Symbol) (f : Experiment A)
    (enc : A→Tape Symbol) (g : A→Experiment (Tape Symbol)) (N S : ℕ)
    (hP : P.Realizes input (f.map enc) N) (hR : f.All (fun a=>R.Realizes (enc a) (g a) S)) :
    (P.seq R).Realizes input (f.bind g) (N+S) := by
  have hR' : (f.map enc).All (fun T=>R.Realizes T (R.earlyTapes S T) S) := by
    rw [Experiment.all_map]
    exact hR.mono (fun a ha=>⟨R.earlyTapes S (enc a),ha.early.1,fun _=>rfl,earlyTapes_cost R S (enc a)⟩)
  apply (seq_realizes P R input (f.map enc) (R.earlyTapes S) N S hP hR').congr
  intro w
  rw [Experiment.mean_bind,Experiment.mean_map,Experiment.mean_bind]
  exact f.mean_congr_all _ _ (hR.mono (fun a ha=>ha.early.2 w))
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_BlockMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Λ σ : Type}
lemma scan_left (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .left⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,(Tape.mk₂ (xs++mark::L) R).move .left⟩
      ⟨some l,v,Tape.mk₂ L (mark::(xs.reverse++R))⟩ xs.length := by
  induction xs generalizing R with
  | nil => simpa using Exec.refl M (⟨some l,v,Tape.mk₂ L (mark::R)⟩ : TM1.Cfg Symbol Λ σ)
  | cons a xs ih =>
    simp only [List.cons_append,mk₂_left]
    have h1:=Exec.step M l v (Tape.mk₂ (xs++mark::L) (a::R))
    rw [hs v _ (by simpa using hx a (by simp))] at h1
    have h2:=ih (a::R) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
lemma scan_right (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .right⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,Tape.mk₂ L (xs++mark::R)⟩
      ⟨some l,v,Tape.mk₂ (xs.reverse++L) (mark::R)⟩ xs.length := by
  induction xs generalizing L with
  | nil => exact Exec.refl M _
  | cons a xs ih =>
    simp only [List.cons_append]
    have h1:=Exec.step M l v (Tape.mk₂ L (a::(xs++mark::R)))
    rw [hs v _ (by simpa using hx a (by simp)),mk₂_right] at h1
    have h2:=ih (a::L) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
end MatchingFPRAS.LiteralTape

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)
local notation "M" => code w h header
lemma seek_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .seek) v T=⟨some .seek,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma back_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .back) v T=⟨some .back,v,T.move .right⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopSep_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .stopSep) v T=⟨some .stopSep,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopOut_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .stopOut) v T=⟨some .stopOut,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]

lemma start_step (input : List Symbol) (v : Block w) :
    Exec M ⟨some .start,v,Tape.mk₁ input⟩ ⟨some .read,v,working [] 0 input⟩ 1 := by
  have hh:=Exec.step M .start v (Tape.mk₁ input)
  simpa only [code,TM1.stepAux,Tape.mk₁,mk₂_left_nil,mk₂_write,mk₂_right,working,List.replicate_zero,
    List.reverse_nil,List.nil_append] using hh

lemma seek_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .seek,v,Tape.mk₂ [] (6::R)⟩
      ⟨some .back,v,Tape.mk₂ [6] (h v++R)⟩ 1 := by
  have hh:=Exec.step M .seek v (Tape.mk₂ [] (6::R))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true] at hh
  rw [select_step _ _ _ v (by simp)] at hh
  have hs:=writeLeft_step (Γ:=Symbol) (h v).reverse
    (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>Label.back)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [TM1.stepAux,mk₂_write,hs] using hh
lemma stopOut_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .stopOut,v,Tape.mk₂ [] (6::R)⟩
      ⟨none,v,Tape.mk₂ [0] (header++R)⟩ 1 := by
  have hh:=Exec.step M .stopOut v (Tape.mk₂ [] (6::R))
  have hs:=writeLeft_step (Γ:=Symbol) header.reverse
    (.write (fun _ _=>0) (.move .right (.halt : TM1.Stmt Symbol Label (Block w)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write,hs] using hh

lemma read_block (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .seek,b,(Tape.mk₂ (List.replicate gap 0++out.reverse++[6])
        (List.replicate w 0++7::input)).move .left⟩ 1 := by
  have hh:=Exec.step M .read v (working out gap (List.ofFn b++input))
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at hh
  rw [working,grab_fin] at hh
  simp only [TM1.stepAux,hb,decide_false,Bool.cond_false] at hh
  cases hr : (List.ofFn b).reverse with
  | nil => have hl:=congrArg List.length hr; simp at hl; omega
  | cons a xs =>
    have hl : (xs++[7]).length=w := by
      have hh:=congrArg List.length hr
      simp only [List.length_reverse,List.length_ofFn,List.length_cons] at hh
      simp only [List.length_append,List.length_singleton]; omega
    rw [hr] at hh
    simp only [List.cons_append,mk₂_left,mk₂_write] at hh
    rw [show xs++7::(List.replicate gap 0++out.reverse++[6])=
      (xs++[7])++(List.replicate gap 0++out.reverse++[6]) by simp] at hh
    have ht:=eraseToLeft_step (xs++[7]) (List.replicate gap 0++out.reverse++[6]) (7::input)
      (.move .left (.goto (fun _ _=>Label.seek))) b
    rw [hl] at ht
    rw [ht] at hh
    exact hh
lemma cycle (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) (hh : ∀ a∈h b,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .read,b,working (h b++out) (gap+w) input⟩
      (3+2*(out.length+gap)+(h b).length+w) := by
  have ha:=read_block w h header hw b v hb out input gap
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := (List.eq_of_mem_replicate ha); subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hs:=scan_left M .seek 6 (seek_path w h header)
    (List.replicate gap 0++out.reverse) [] (List.replicate w 0++7::input) b hx
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(List.replicate w 0++7::input)=
      out++List.replicate (gap+w) 0++7::input := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc]
  rw [he] at hs
  have ht:=seek_write w h header b (out++List.replicate (gap+w) 0++7::input)
  have hy : ∀ a∈h b++out++List.replicate (gap+w) (0:Symbol),a≠7 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · exact (hh a ha).2
      · exact (ho a ha).2
    · have := List.eq_of_mem_replicate ha; subst a; decide
  have hu:=scan_right M .back 7 (back_path w h header)
    (h b++out++List.replicate (gap+w) 0) [6] input b hy
  have hv:=Exec.step M .back b
    (Tape.mk₂ ((h b++out++List.replicate (gap+w) 0).reverse++[6]) (7::input))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_right] at hv
  simp only [List.append_assoc] at ha hs ht hu hv
  have hh:=((ha.trans hs).trans ht).trans (hu.trans hv)
  simp only [working,List.append_assoc,List.reverse_append,List.reverse_replicate,List.length_append,
    List.length_replicate,List.length_reverse] at hh ⊢
  apply Exec.mono hh
  omega

lemma mk₂_blanks (L R : List Symbol) (n : ℕ) :
    Tape.mk₂ L (R++List.replicate n 0)=Tape.mk₂ L R := by
  simp only [Tape.mk₂,show (0:Symbol)=default from rfl,blank_append_zero]
lemma mk₂_replicate (L : List Symbol) (n : ℕ) :
    Tape.mk₂ L (List.replicate n 0)=Tape.mk₂ L [] := by
  simpa only [List.nil_append] using mk₂_blanks L [] n
lemma mk₂_zero_left (R : List Symbol) : Tape.mk₂ [0] R=Tape.mk₁ R := by
  change Tape.mk' (ListBlank.mk (List.replicate 1 (default:Symbol))) _=Tape.mk' (ListBlank.mk []) _
  rw [blank_zero]

lemma finish (v : Block w) (out : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap []⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++out)⟩ (3+w+gap+out.length) := by
  have hz : List.ofFn (fun _ : Fin w=>(0:Symbol))=List.replicate w 0 := by simp
  have ha:=Exec.step M .read v (working out gap [])
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at ha
  rw [working,←mk₂_blanks _ [] w] at ha
  simp only [List.nil_append,←hz] at ha
  rw [show List.ofFn (fun _ : Fin w=>(0:Symbol))=
    List.ofFn (fun _ : Fin w=>(0:Symbol))++[] by simp,grab_fin] at ha
  simp only [TM1.stepAux,decide_true,Bool.cond_true,hz,List.reverse_replicate] at ha
  have hs:=scan_left M .stopSep 7 (stopSep_path w h header) (List.replicate w 0)
    (List.replicate gap 0++out.reverse++[6]) [] (fun _=>0)
    (by intro a ha; have := List.eq_of_mem_replicate ha; subst a; decide)
  have ht:=Exec.step M .stopSep (fun _ : Fin w=>(0:Symbol))
    (Tape.mk₂ (List.replicate gap 0++out.reverse++[6]) (7::List.replicate w 0))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write] at ht
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := List.eq_of_mem_replicate ha; subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hu:=scan_left M .stopOut 6 (stopOut_path w h header)
    (List.replicate gap 0++out.reverse) [] (0::List.replicate w 0) (fun _=>0) hx
  have hv:=stopOut_write w h header (fun _=>0)
    (out++List.replicate (gap+1+w) 0)
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(0::List.replicate w 0)=
      out++List.replicate (gap+1+w) 0 := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc,List.replicate_one,List.singleton_append]
  rw [he] at hu
  simp only [List.length_replicate,List.reverse_replicate,List.append_nil] at hs
  have hb:=((ha.trans hs).trans ht).trans (hu.trans hv)
  rw [←List.append_assoc,mk₂_blanks,mk₂_zero_left] at hb
  simp only [List.append_assoc,List.length_append,List.length_reverse,List.length_replicate] at hb
  simp only [List.append_nil,mk₂_replicate] at hb
  simp only [working,List.append_assoc]
  apply Exec.mono hb
  omega

lemma blocks (hw : 0<w) (bs : List (Block w)) (v : Block w) (out : List Symbol) (gap H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h++out)⟩
      (budget w H bs.length (out.length+gap)) := by
  induction bs generalizing v out gap with
  | nil =>
    simpa only [List.flatMap_nil,List.reverse_nil,List.append_nil,List.nil_append]
      using (finish w h header v out gap ho).mono (by simp only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.one_mul]; omega)
  | cons b bs ih =>
    have ha:=cycle w h header hw b v (hb b (by simp)) out (bs.flatMap List.ofFn) gap ho (hh b (by simp))
    have hs:=ih b (h b++out) (gap+w)
      (fun a ha=>hb a (by simp [ha])) (fun a ha=>hh a (by simp [ha]))
      (fun a ha=>hH a (by simp [ha]))
      (by intro a ha; rcases List.mem_append.mp ha with ha|ha; exact hh b (by simp) a ha; exact ho a ha)
    have he:=ha.trans hs
    simp only [List.reverse_cons,List.flatMap_append,List.append_assoc,
      List.flatMap_cons] at he ⊢
    apply he.mono
    have hlen:=hH b (by simp)
    simp only [budget,List.length_cons,List.length_append]
    nlinarith

lemma computes (hw : 0<w) (bs : List (Block w)) (H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H) :
    Exec M ⟨some .start,(fun _=>0),Tape.mk₁ (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h)⟩
      (1+budget w H bs.length 0) := by
  have ha:=start_step w h header (bs.flatMap List.ofFn) (fun _=>0)
  have hs:=blocks w h header hw bs (fun _=>0) [] 0 H hb hh hH (by simp)
  simpa only [List.append_nil,List.length_nil,Nat.zero_add] using ha.trans hs

end MatchingFPRAS.LiteralBlockMap

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

lemma rows_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.rows (inputStacks a) (weight a)=baseRow::bs.map bitRow := by
  have hw : weight a=bs.length+1 := by
    have h:=congrArg List.length hs
    simpa only [List.length_reverse,List.length_cons,weight,TreeFunction.size] using h
  apply List.ext_getElem
  · simp only [StackWords.rows,List.length_ofFn,List.length_cons,List.length_map,hw]
  · intro i hi hj
    simp only [StackWords.rows,List.getElem_ofFn]
    funext k
    cases k with
    | inr k =>
      cases i <;> simp [inputStacks,encodeEnv,baseRow,bitRow]
    | inl r =>
      by_cases hr:r=0
      · subst r
        simp only [inputStacks,encodeEnv,env,ite_true,hs]
        cases i <;> simp [baseRow,bitRow]
      · have hn : env (TreeTyped.encode a) .nil .nil r=.nil := by simp [env,hr]
        simp only [inputStacks,encodeEnv,hn,TreeData.encode,List.reverse_singleton]
        cases i <;> simp [baseRow,bitRow,hr]
lemma word_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.word (inputStacks a) (weight a)=bottom::bs.map letter := by
  rw [StackWords.word,rows_eq a bs hs]
  simp only [List.headI_cons,List.tail_cons]
  change (true,baseRow)::(bs.map bitRow).map (fun a=>(false,a)) = (true,baseRow)::bs.map LiteralPacked.letter
  rw [List.map_map]
  rfl

lemma list_bits (as : List Symbol) :
    (TreeData.encode (TreeTyped.encode as)).reverse=false::as.reverse.flatMap symbolBits := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [TreeTyped.encode_list_cons,TreeData.encode,List.reverse_cons,List.reverse_append,ih,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,symbolBits,
      List.cons_append,List.append_assoc]

lemma packed_eq (as : List Symbol) : TreePost.packed as=header++as.reverse.flatMap chunk := by
  unfold TreePost.packed StackWords.encoded FixedAlphabetCompiler.word FixedAlphabetCompiler.bitsWord
  rw [word_eq as _ (list_bits as)]
  simp only [List.flatMap_cons,List.map_append,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,LiteralPacked.header,LiteralPacked.block]
  rfl
lemma block_alphabet (a : Alphabet) (s : Symbol) (hs : s∈block a) : s=0 ∨ s=1 := by
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
  cases b <;> simp [BoolPostCompiler.up]
lemma chunk_alphabet (a s : Symbol) (hs : s∈chunk a) : s≠6 ∧ s≠7 := by
  obtain ⟨b,_,hb⟩:=List.mem_flatMap.mp hs
  rcases block_alphabet _ _ hb with rfl|rfl <;> decide
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreePost

lemma symbol_encode_injective : Function.Injective (TreeTyped.encode (A:=Symbol)) := by
  intro a b h
  have hh : TreeTyped.encode (LiteralCodec.parts a)=TreeTyped.encode (LiteralCodec.parts b) := h
  have he := (TreeData.Data.cons.inj hh).1
  have hs : (LiteralCodec.parts a).1=(LiteralCodec.parts b).1 :=
    list_encode_injective (show Function.Injective (TreeTyped.encode (A:=Bool)) from bit_injective) he
  apply Fin.ext
  simpa only [LiteralCodec.parts,List.length_replicate] using congrArg List.length hs
lemma symbolBits_injective : Function.Injective symbolBits := by
  intro a b h
  have h1:=List.append_cancel_right (show _++[true]=_++[true] from h)
  exact symbol_encode_injective (TreeData.encode_injective (List.reverse_injective h1))
lemma encoding_injective (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    Function.Injective (fun a : Γ=>(FixedEncoding.enc Γ a).toList.map BoolPostCompiler.up) := by
  intro a b h
  have hb : (FixedEncoding.enc Γ a).toList=(FixedEncoding.enc Γ b).toList :=
    List.map_injective_iff.mpr (Function.LeftInverse.injective BoolPostCompiler.down_up) h
  exact FixedEncoding.injective Γ (Subtype.ext hb)
lemma block_injective : Function.Injective block := encoding_injective Alphabet
lemma flatMap_injective_fixed {A B : Type} (f : A→List B) (w : ℕ) (hw : 0<w)
    (hl : ∀ a,(f a).length=w) (hi : Function.Injective f) : Function.Injective (List.flatMap f) := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons b bs => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => have hh:=congrArg List.length h;simp only [List.flatMap_nil,List.flatMap_cons,List.length_nil,List.length_append,hl] at hh;omega
    | cons b bs =>
      have h1 := List.append_inj_left h ((hl a).trans (hl b).symm)
      have h2 := List.append_inj_right h ((hl a).trans (hl b).symm)
      exact congrArg₂ List.cons (hi h1) (ih h2)
lemma width_pos : 0<width := Fintype.card_pos
lemma letter_injective : Function.Injective letter := by
  intro a b h
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h
  simpa only [letter,bitRow,ite_true,Option.some.injEq] using hh
lemma chunk_injective : Function.Injective chunk := by
  intro a b h
  have hi : Function.Injective (fun b=>block (letter b)) := by
    intro b c he
    exact letter_injective (block_injective he)
  have hh : (symbolBits a).flatMap (fun b=>block (letter b)) =
      (symbolBits b).flatMap (fun b=>block (letter b)) := h
  exact symbolBits_injective (flatMap_injective_fixed (fun b=>block (letter b)) width width_pos
    (fun b=>block_length (letter b)) hi hh)
lemma encoding_blank (Γ : Type) [Fintype Γ] [Inhabited Γ] :
    (FixedEncoding.enc Γ default).toList.map BoolPostCompiler.up=
      List.replicate (Fintype.card Γ) (0:Symbol) := by
  rw [FixedEncoding.blank]
  change (List.replicate (Fintype.card Γ) false).map _ = _
  rw [List.map_replicate]
  rfl
lemma block_blank : block default=List.replicate width 0 := encoding_blank Alphabet
lemma block_ne_zero (a : Alphabet) (ha : a≠default) : block a≠List.replicate width 0 := by
  intro he
  exact ha (block_injective (he.trans block_blank.symm))
lemma chunk_nonzero (a : Symbol) : ∃ s∈chunk a,s≠0 := by
  classical
  by_contra h
  push Not at h
  have h1 : ∀ s∈block (letter true),s=(0:Symbol) := by
    intro s hs
    exact h s (List.mem_flatMap.mpr ⟨true,by simp [symbolBits],hs⟩)
  have he : block (letter true)=List.replicate width 0 := by
    rw [←block_length (letter true)]
    exact List.eq_replicate_of_mem h1
  apply block_ne_zero (letter true) _ he
  intro h2
  have hh:=congrArg (fun x : Alphabet=>x.2 (Sum.inl 0)) h2
  change (some true : Option Bool)=none at hh
  exact Option.some_ne_none true hh
lemma chunkFn_word (a : Symbol) : List.ofFn (chunkFn a)=chunk a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,chunk_length]
  · intro i hi hj; simp only [List.getElem_ofFn,chunkFn]
lemma unchunk_chunkFn (a : Symbol) : unchunk (chunkFn a)=[a] := by
  rw [unchunk,chunkFn_word,Function.leftInverse_invFun chunk_injective]
lemma chunkFn_nonzero (a : Symbol) : chunkFn a≠fun _=>0 := by
  intro he
  have hh:=congrArg List.ofFn he
  rw [chunkFn_word,List.ofFn_const] at hh
  obtain ⟨s,hs,hn⟩:=chunk_nonzero a
  rw [hh] at hs
  exact hn (List.eq_of_mem_replicate hs)
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_PackedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

lemma singletonBlock_word (a : Symbol) : List.ofFn (singletonBlock a)=[a] := by simp [singletonBlock,List.ofFn_succ]
lemma pack_exec (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    Exec packCode ⟨some .start,(fun _=>0),Tape.mk₁ as⟩
      ⟨none,(fun _=>0),Tape.mk₁ (TreePost.packed as)⟩
      (1+LiteralBlockMap.budget 1 (18*width) as.length 0) := by
  have h:=LiteralBlockMap.computes 1 (fun b=>chunk (b 0)) header (by decide)
    (as.map singletonBlock) (18*width) ?_ ?_ ?_
  · simpa only [packCode,List.flatMap_map,singletonBlock_word,List.flatMap_singleton,List.flatMap_singleton',List.length_map,
      ←List.map_reverse,singletonBlock,←packed_eq] using h
  · intro b hb
    obtain ⟨a,ha',rfl⟩:=List.mem_map.mp hb
    intro he
    exact ha a ha' (congrFun he 0)
  · intro b _ a had
    exact chunk_alphabet _ _ had
  · intro b _
    exact (chunk_length _).le
lemma unpack_exec (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    Exec unpackCode ⟨some .start,(fun _=>0),Tape.mk₁ (as.reverse.flatMap chunk)⟩
      ⟨none,(fun _=>0),Tape.mk₁ as⟩
      (1+LiteralBlockMap.budget (18*width) 1 as.length 0) := by
  have h:=LiteralBlockMap.computes (18*width) unchunk [] (Nat.mul_pos (by decide) width_pos)
    (as.reverse.map chunkFn) 1 ?_ ?_ ?_
  · simpa only [unpackCode,List.flatMap_map,chunkFn_word,←List.map_reverse,List.reverse_reverse,
      unchunk_chunkFn,List.flatMap_singleton,List.flatMap_singleton',List.nil_append,List.length_map,List.length_reverse] using h
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    exact chunkFn_nonzero a
  · intro b hb a had
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn,List.mem_singleton] at had
    subst a
    exact ha c (List.mem_reverse.mp hc)
  · intro b hb
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp hb
    rw [unchunk_chunkFn];rfl
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
lemma eraseRight_step (xs L R : List Γ) (q : TM1.Stmt Γ Λ σ) (v : σ) :
    TM1.stepAux (eraseRight xs.length q) v (Tape.mk₂ L (xs++R))=
      TM1.stepAux q v (Tape.mk₂ (List.replicate xs.length default++L) R) := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.length_cons,eraseRight,TM1.stepAux,List.cons_append,mk₂_write,mk₂_right]
    rw [show Nat.rec q (fun _ tail=>TM1.Stmt.write (fun _ _=>default) (.move .right tail)) xs.length=eraseRight xs.length q from rfl,ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
lemma erase_exec (xs R : List Symbol) :
    Exec (eraseCode xs.length) ⟨some (),(),Tape.mk₁ (xs++R)⟩ ⟨none,(),Tape.mk₁ R⟩ 1 := by
  have h:=Exec.step (eraseCode xs.length) () () (Tape.mk₁ (xs++R))
  change Exec _ _ (TM1.stepAux (eraseRight xs.length .halt) () (Tape.mk₂ [] (xs++R))) 1 at h
  rw [eraseRight_step] at h
  have he : Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R=Tape.mk₁ R := by
    simp only [List.append_nil,Tape.mk₂,Tape.mk₁]
    rw [show (ListBlank.mk (List.replicate xs.length (0:Symbol)))=ListBlank.mk [] from blank_zero xs.length]
  change Exec _ _ (TM1.stepAux (.halt : TM1.Stmt Symbol Unit Unit) () (Tape.mk₂ (List.replicate xs.length (0:Symbol)++[]) R)) 1 at h
  simpa only [TM1.stepAux,he] using h
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_Wrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped

lemma packTime_mono {n m : ℕ} (h : n ≤ m) : packTime n ≤ packTime m := by
  unfold packTime LiteralBlockMap.budget;gcongr
lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime unpackTime LiteralBlockMap.budget;gcongr
lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)
lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk))) eraseTime := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _ (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono
      (by simp only [Nat.one_mul];rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as)) (unpackTime as.length) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _=>.done (Tape.mk₁ as)) _ _ h1 h2

lemma wrap_realizes {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0) (hout : (f as).All (fun bs=>∀ b∈bs,b≠6 ∧ b≠7)) :
    (wrap F).Realizes (Tape.mk₁ as) ((f as).map Tape.mk₁) (wrapTime F as) := by
  have h1 : (pack.seq (OnlineTree.physicalProgram F)).Realizes (Tape.mk₁ as)
      ((f as).map (fun bs=>Tape.mk₁ (TreePost.packed bs))) (packTime as.length+OnlineTree.physicalCost F as) :=
    Program.seq_realizes pack (OnlineTree.physicalProgram F) _ (.done (Tape.mk₁ (TreePost.packed as)))
      (fun _=>(f as).map (fun bs=>Tape.mk₁ (TreePost.packed bs))) _ _ (pack_realizes as ha) (OnlineTree.physical_realizes F as)
  exact Program.seq_realizes_map _ _ _ (f as) (fun bs=>Tape.mk₁ (TreePost.packed bs)) (fun bs=>.done (Tape.mk₁ bs))
    _ _ h1 ((hout.and (Experiment.all_worst (f as) List.length)).mono
      (fun bs hbs=>(post_realizes bs hbs.1).mono (postTime_mono hbs.2)))

lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide
lemma encodeRat_nonzero (q : ℚ) (a : Symbol) (ha : a∈encodeRat q) : a≠0 := by
  simp only [encodeRat,encodeInt,List.mem_append] at ha
  rcases ha with (ha|ha)|ha
  · split_ifs at ha with hn <;> simp only [List.mem_singleton] at ha <;> subst a <;> decide
  · exact encodeNat_nonzero _ _ ha
  · exact encodeNat_nonzero _ _ ha
lemma input_nonzero (G : GraphInput) (ε δ : ℚ) (a : Symbol) (ha : a∈encodeInput G ε δ) : a≠0 := by
  simp only [encodeInput,List.mem_append] at ha
  rcases ha with (((ha|ha)|ha)|ha)|ha
  · exact encodeNat_nonzero _ _ ha
  · exact encodeNat_nonzero _ _ ha
  · obtain ⟨e,_,he⟩:=List.mem_flatMap.mp ha
    rcases List.mem_append.mp he with he|he <;> exact encodeNat_nonzero _ _ he
  · exact encodeRat_nonzero _ _ ha
  · exact encodeRat_nonzero _ _ ha
lemma natWord_alphabet (n : ℕ) (a : Symbol) (ha : a∈LiteralCodec.natWord n) : a≠6 ∧ a≠7 := by
  simp only [LiteralCodec.natWord,LiteralCodec.fromBit,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide
lemma ratWord_alphabet (q : TreeFraction.Fraction) (a : Symbol) (ha : a∈LiteralCodec.ratWord q) : a≠6 ∧ a≠7 := by
  simp only [LiteralCodec.ratWord,List.mem_cons,List.mem_append] at ha
  rcases ha with (rfl|ha)|ha
  · decide
  · exact natWord_alphabet _ _ ha
  · exact natWord_alphabet _ _ ha
lemma algorithm_alphabet (as : List Symbol) :
    (LiteralAlgorithm.algorithm as).All (fun bs=>∀ b∈bs,b≠6 ∧ b≠7) := by
  rw [LiteralAlgorithm.algorithm,Experiment.all_map]
  exact (Experiment.all_true _).mono (fun q _=>ratWord_alphabet q)
lemma mainProgram_realizes (G : GraphInput) (ε δ : ℚ) :
    mainProgram.Realizes (Tape.mk₁ (encodeInput G ε δ))
      ((LiteralAlgorithm.algorithm (encodeInput G ε δ)).map Tape.mk₁)
      (wrapTime LiteralAlgorithm.algorithmRealizer (encodeInput G ε δ)) :=
  wrap_realizes _ _ (input_nonzero G ε δ) (algorithm_alphabet _)
end MatchingFPRAS.LiteralPhysical

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_PhysicalCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Polynomial PhysicalStream TreeTyped BitComplexity LiteralPacked

lemma polynomial_eval (p : Polynomial ℕ) : PolynomiallyBounded (fun x=>p.eval x) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simpa only [Polynomial.eval_add] using hp.add hq
  · intro n a
    simpa only [Polynomial.eval_monomial] using (PolynomiallyBounded.const a).mul (PolynomiallyBounded.id.pow n)
lemma polynomial_budget (w H : ℕ) {f g : ℕ→ℕ}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>LiteralBlockMap.budget w H (f x) (g x)) :=
  (hf.add (PolynomiallyBounded.const 1)).mul
    ((PolynomiallyBounded.const (3+w+H)).add ((PolynomiallyBounded.const 2).mul
      (hg.add (hf.mul (PolynomiallyBounded.const (H+w))))))
lemma polynomial_packTime {f : ℕ→ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun x=>packTime (f x)) :=
  ((PolynomiallyBounded.const 1).add (polynomial_budget 1 (18*width) hf (PolynomiallyBounded.const 0))).mul
    (PolynomiallyBounded.const (MachineCost.programCost packCode))
lemma polynomial_postTime {f : ℕ→ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun x=>postTime (f x)) :=
  (PolynomiallyBounded.const eraseTime).add
    (((PolynomiallyBounded.const 1).add (polynomial_budget (18*width) 1 hf (PolynomiallyBounded.const 0))).mul
      (PolynomiallyBounded.const (MachineCost.programCost unpackCode)))
lemma polynomial_factor {A B : Type} [Codec A] [Codec B] {f : A→Experiment B}
    (F : OnlineTree.Realizer f) {H n : ℕ→ℕ}
    (hH : PolynomiallyBounded H) (hn : PolynomiallyBounded n) :
    PolynomiallyBounded (fun x=>OnlineStack.Executes.factor F.program.code (H x) (n x)) := by
  let a:=OnlineStack.accesses F.program.code
  let o:=OnlineStack.overhead F.program.code
  exact ((PolynomiallyBounded.const o).mul ((PolynomiallyBounded.const 1).add
    ((PolynomiallyBounded.const (2*a)).mul ((hH.add (hn.mul (PolynomiallyBounded.const a))).add
      (PolynomiallyBounded.const 1))))).add (PolynomiallyBounded.const 1)

lemma mainTime_bound : ∃ C d : ℕ,0<C ∧ ∀ (G : GraphInput) (ε δ : ℚ),
    0<ε→ε<1→0≤δ→wrapTime LiteralAlgorithm.algorithmRealizer (encodeInput G ε δ)≤timeBound C d G ε δ := by
  obtain ⟨q,hq⟩:=LiteralAlgorithm.algorithm_bound
  let F:=LiteralAlgorithm.algorithmRealizer
  let bound:=fun x=>packTime x+q.eval x*OnlineStack.Executes.factor F.program.code (18*x+1) (q.eval x)+postTime (q.eval x)
  have hb : PolynomiallyBounded bound :=
    ((polynomial_packTime PolynomiallyBounded.id).add ((polynomial_eval q).mul
      (polynomial_factor F (((PolynomiallyBounded.const 18).mul PolynomiallyBounded.id).add
        (PolynomiallyBounded.const 1)) (polynomial_eval q)))).add (polynomial_postTime (polynomial_eval q))
  obtain ⟨C,d,hb⟩:=hb
  refine ⟨C+1,d,by omega,?_⟩
  intro G ε δ he he1 hd
  let as:=encodeInput G ε δ
  let x:=as.length+⌈ε⁻¹⌉₊+Nat.clog 2 ⌈δ⁻¹⌉₊+1
  have hx : 1≤x := by dsimp only [x];omega
  have hl : as.length≤x := by dsimp only [x];omega
  have hc := hq G ε δ he he1 hd x hx hl (by dsimp only [x];omega) (by dsimp only [x];omega)
  have hcost : F.cost as≤q.eval x := by dsimp only [F,as];omega
  have hout : (LiteralAlgorithm.algorithm as).worst weight≤q.eval x := by dsimp only [as];omega
  have hword : (LiteralAlgorithm.algorithm as).worst List.length≤q.eval x :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono (fun bs hbs=>
      (list_length_le_weight bs).trans (hbs.trans hout)))
  have hweight : weight as≤18*x+1 := by rw [LiteralCodec.weight_word];omega
  have hwrap : wrapTime F as≤bound x := by
    unfold wrapTime OnlineTree.physicalCost
    exact Nat.add_le_add (Nat.add_le_add (packTime_mono hl)
      (Nat.mul_le_mul hcost (OnlineStack.Executes.factor_mono _ _ _ _ hweight hcost))) (postTime_mono hword)
  apply hwrap.trans ((hb x hx).trans ?_)
  change C*x^d≤(C+1)*x^d
  exact Nat.mul_le_mul_right _ (by omega)
end MatchingFPRAS.LiteralPhysical

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_PhysicalProgramSeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma run_tape (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).tape=
      (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).tape := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  rw [machine,restrictedMachine_run]
  exact (congrArg Cfg.tape (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))).symm
lemma run_halted (P : Program) (input : List Symbol) (n : ℕ) (b : Bits n)
    (h : (execute P.table n (P.initial (Tape.mk₁ input)) (extend b)).state=none) :
    (MatchingFPRAS.run P.machine input b).state=none := by
  let : Inhabited {q //q∈P.states}:=⟨⟨P.entry,P.entry_mem⟩⟩
  have he:=congrArg Cfg.state (execute_lift P.table P.states P.supported n
    ⟨some default,Tape.mk₁ input⟩ (extend b))
  have hs : (execute (restrict P.table P.states P.supported) n
      ⟨some default,Tape.mk₁ input⟩ (extend b)).state=none := by
    exact Option.map_eq_none_iff.mp (he.symm.trans h)
  rw [machine,restrictedMachine_run]
  change ((execute (restrict P.table P.states P.supported) n
    ⟨some default,Tape.mk₁ input⟩ (extend b)).state.map enumeration)=none
  rw [hs,Option.map_none]
lemma Realizes.run_all {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (R : Tape Symbol→Prop) (hf : f.All R)
    (n : ℕ) (hn : N≤n) (b : Bits n) :
    (MatchingFPRAS.run P.machine input b).state=none ∧
      R (MatchingFPRAS.run P.machine input b).tape := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  have hex:=hp.padded_execution (fun _=>rfl) n (hc.trans hn) (extend b)
  have ht : (MatchingFPRAS.run P.machine input b).tape=(p.run (extend b)).1 := by
    rw [run_tape,hex];rfl
  refine ⟨run_halted P input n b (by rw [hex];rfl),?_⟩
  rw [ht]
  exact p.all_run R (Experiment.all_of_mean_eq hm R hf) (extend b)
lemma Realizes.run_mean {P : Program} {input : List Symbol} {f : Experiment (Tape Symbol)} {N : ℕ}
    (hP : P.Realizes (Tape.mk₁ input) f N) (w : Tape Symbol→ℚ)
    (n : ℕ) (hn : N≤n) :
    average (fun b : Bits n=>w (MatchingFPRAS.run P.machine input b).tape)=f.mean w := by
  obtain ⟨p,hp,hm,hc⟩:=hP
  simp_rw [run_tape]
  exact (hp.fair_law (fun _=>rfl) n (hc.trans hn) (fun c=>w c.tape)).trans (hm w)
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_MainLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralAlgorithm
open scoped Classical

lemma properTape_of_word (G : GraphInput) (as : List Symbol) (h : Proper G as) : ProperTape G (Tape.mk₁ as) := by
  obtain ⟨q,hq,rfl,hz⟩:=h
  exact ⟨q,hq,by simp [Tape.mk₁,Tape.mk₂],hz⟩
lemma accurateTape_of_word (G : GraphInput) (ε : ℚ) (as : List Symbol) (h : AccurateWord G ε as) :
    AccurateTape G ε (Tape.mk₁ as) := by
  obtain ⟨q,rfl,hq⟩:=h
  exact ⟨q,by simp [Tape.mk₁,Tape.mk₂],hq⟩
lemma mainProgram_all (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) (b : Bits n) :
    (MatchingFPRAS.run mainProgram.machine (encodeInput G ε δ) b).state=none ∧
      ProperTape G (MatchingFPRAS.run mainProgram.machine (encodeInput G ε δ) b).tape := by
  apply (mainProgram_realizes G ε δ).run_all _ _ n hn b
  rw [Experiment.all_map]
  exact (algorithm_proper G ε δ he he1 hd).mono (properTape_of_word G)
lemma mainProgram_outputs (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) :
    (∀ b : Bits n,∃ q : ℚ,0≤q ∧ Outputs mainProgram.machine (encodeInput G ε δ) b q) ∧
    (Z G=0→∀ b : Bits n,Outputs mainProgram.machine (encodeInput G ε δ) b 0) := by
  constructor
  · intro b
    obtain ⟨hh,q,hq,ht,_⟩:=mainProgram_all G ε δ he he1 hd n hn b
    exact ⟨q,hq,hh,ht⟩
  · intro hz b
    obtain ⟨hh,q,_hq,ht,hzq⟩:=mainProgram_all G ε δ he he1 hd n hn b
    rw [hzq hz] at ht
    exact ⟨hh,ht⟩
lemma average_good (A : RandomMachine) (G : GraphInput) (ε δ : ℚ) (n : ℕ)
    (hh : ∀ b : Bits n,(MatchingFPRAS.run A (encodeInput G ε δ) b).state=none) :
    average (fun b : Bits n=>if AccurateTape G ε (MatchingFPRAS.run A (encodeInput G ε δ) b).tape then 1 else 0)=
      ((goodTapes A G ε δ n).card:ℚ)/(2:ℚ)^n := by
  have he (b : Bits n) : AccurateTape G ε (MatchingFPRAS.run A (encodeInput G ε δ) b).tape ↔
      ∃ q : ℚ,Outputs A (encodeInput G ε δ) b q ∧ (1-ε)*(Z G:ℚ)≤q ∧ q≤(1+ε)*(Z G:ℚ) := by
    constructor
    · rintro ⟨q,ht,hq⟩;exact ⟨q,⟨hh b,ht⟩,hq⟩
    · rintro ⟨q,⟨_,ht⟩,hq⟩;exact ⟨q,ht,hq⟩
  simp_rw [he]
  simp only [average,goodTapes,Finset.sum_boole]
lemma mainProgram_success (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ)
    (n : ℕ) (hn : wrapTime algorithmRealizer (encodeInput G ε δ)≤n) :
    1-δ≤((goodTapes mainProgram.machine G ε δ n).card:ℚ)/(2:ℚ)^n := by
  have hs : 1-δ≤(algorithm (encodeInput G ε δ)).mean
      (fun as=>if AccurateTape G ε (Tape.mk₁ as) then 1 else 0) := by
    apply (algorithm_success G ε δ he he1 hd).trans (Experiment.mean_mono _ _ _ ?_)
    exact (Experiment.all_true _).mono (by
      intro as _
      by_cases h : AccurateWord G ε as
      · simp only [ite_eq_left h,ite_eq_left (accurateTape_of_word G ε as h),le_refl]
      · simp only [ite_eq_right h];split_ifs <;> norm_num)
  have hm:=(mainProgram_realizes G ε δ).run_mean (fun T=>if AccurateTape G ε T then 1 else 0) n hn
  rw [Experiment.mean_map] at hm
  rw [←hm,average_good mainProgram.machine G ε δ n
    (fun b=>(mainProgram_all G ε δ he he1 hd.le n hn b).1)] at hs
  exact hs
end MatchingFPRAS.LiteralPhysical

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_FiniteSampler2
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.PatternCode.instFintype _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.instFintypePM _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace LongComponent

variable {p : PM inc × PM inc} (S : LongComponent p)

noncomputable instance instFintype_1 : Fintype (LongComponent p) := Fintype.ofFinite _

end LongComponent

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace PatternCode

variable (x : PatternCode inc)

variable [Fintype E]

noncomputable instance finiteSampler2PatternCodeFintype : Fintype (PatternCode inc) := Fintype.ofFinite _

end PatternCode

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

theorem thm_main_oai : MainStatement := by
  obtain ⟨C,d,hC,hbound⟩:=LiteralPhysical.mainTime_bound
  refine ⟨LiteralPhysical.mainProgram.machine,C,d,hC,?_⟩
  intro G ε δ he he1 hd _hd1
  dsimp only
  have hn:=hbound G ε δ he he1 hd.le
  obtain ⟨hp,hz⟩:=LiteralPhysical.mainProgram_outputs G ε δ he he1 hd.le
    (timeBound C d G ε δ) hn
  exact ⟨hp,hz,LiteralPhysical.mainProgram_success G ε δ he he1 hd
    (timeBound C d G ε δ) hn⟩
end MatchingFPRAS

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.thm_main_oai := @OAI.MatchingFPRAS.thm_main_oai

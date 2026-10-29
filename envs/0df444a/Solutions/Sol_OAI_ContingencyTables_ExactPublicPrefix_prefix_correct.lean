-- Prove2me | solution 1 for OAI.ContingencyTables.ExactPublicPrefix.prefix_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:58:38.227859+00:00
-- url     : https://prove2.me/submissions/71d6a473-1792-46c8-89f3-2887dd0d51e2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_GuardMachineBase
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_StackCompilerCost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_BoolPostCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_SupportedCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_FixedEncoding
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_StackWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
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
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisSemantics
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural coordinate encodings of dense axis moves -/

namespace ContingencyTables.DensePrograms
open ProfilePrograms GridBoundary
open scoped Classical

lemma listExchange_increment {q : ℕ} (v : Fin q → ℕ) (i : Fin q) :
    listExchange (List.ofFn v,(i.val,q))=
      List.ofFn (Function.update v i (v i+1)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjq : j<q := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using hj
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjq,dite_true,
      Option.getD_some,ite_eq_right (Nat.ne_of_lt hjq),Nat.sub_zero]
    by_cases hji : (⟨j,hjq⟩ : Fin q)=i
    · subst i
      simp only [Function.update_self,ite_true, if_true]
    · have hne : j≠i.val := fun h => hji (Fin.ext h)
      simp only [hne,ite_false,Nat.add_zero,Function.update_of_ne hji]

lemma listExchange_decrement {q : ℕ} (v : Fin q → ℕ) (i : Fin q) :
    listExchange (List.ofFn v,(q,i.val))=
      List.ofFn (Function.update v i (v i-1)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjq : j<q := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using hj
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjq,dite_true,
      Option.getD_some,ite_eq_right (Nat.ne_of_lt hjq),Nat.add_zero]
    by_cases hji : (⟨j,hjq⟩ : Fin q)=i
    · subst i
      simp only [Function.update_self,ite_true, if_true]
    · have hne : j≠i.val := fun h => hji (Fin.ext h)
      simp only [hne,ite_false,Nat.sub_zero,Function.update_of_ne hji]

lemma gridNatCode_getD {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q) :
    (gridNatCode a).getD i.val 0=(corner a i).toNat := by
  simp only [gridNatCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
    dite_true,Option.getD_some,Fin.eta]

lemma gridNatCode_update {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q)
    (v : Set.Icc (0 : ℤ) ((K : ℤ)-1)) :
    gridNatCode (Function.update a i v)=
      List.ofFn (Function.update (fun j => (corner a j).toNat) i v.val.toNat) := by
  apply congrArg List.ofFn
  funext j
  by_cases hji : j=i
  · subst j
    simp only [Function.update_self,corner]
  · simp only [Function.update_of_ne hji,corner]

/-- The bounded list operation implements exactly the signed geometric
axis proposal, including both boundary rejections. -/
theorem axisListStep_eq {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q) (sign : Bool) :
    axisListStep (((K,gridNatCode a),i.val),sign)=
      (axisStep a i sign).map gridNatCode := by
  have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
  have hnonneg : 0 ≤ corner a i := (a i).property.1
  have hupper : corner a i≤(K : ℤ)-1 := (a i).property.2
  have hcast : ((corner a i).toNat : ℤ)=corner a i := Int.toNat_of_nonneg hnonneg
  cases sign with
  | false =>
    simp only [axisListStep,hlen,i.isLt,ite_true, if_true,Bool.false_eq_true,ite_false,
      gridNatCode_getD,axisStep]
    by_cases h : 0 ≤ corner a i-1
    · have hn : 0<(corner a i).toNat := by omega
      rw [ite_eq_left hn,dite_eq_left h,Option.map_some]
      let v : Set.Icc (0 : ℤ) ((K : ℤ)-1) := ⟨corner a i-1,h,by omega⟩
      have hc := gridNatCode_update a i v
      have he : v.val.toNat=(corner a i).toNat-1 := by dsimp only [v]; omega
      rw [he] at hc
      exact congrArg some ((listExchange_decrement (fun j => (corner a j).toNat) i).trans hc.symm)
    · have hn : ¬0<(corner a i).toNat := by omega
      rw [ite_eq_right hn,dite_eq_right h,Option.map_none]
  | true =>
    simp only [axisListStep,hlen,i.isLt,ite_true, if_true,gridNatCode_getD,axisStep]
    by_cases h : corner a i+1≤(K : ℤ)-1
    · have hn : (corner a i).toNat+1<K := by omega
      rw [ite_eq_left hn,dite_eq_left h,Option.map_some]
      let v : Set.Icc (0 : ℤ) ((K : ℤ)-1) := ⟨corner a i+1,by omega,h⟩
      have hc := gridNatCode_update a i v
      have he : v.val.toNat=(corner a i).toNat+1 := by dsimp only [v]; omega
      rw [he] at hc
      exact congrArg some ((listExchange_increment (fun j => (corner a j).toNat) i).trans hc.symm)
    · have hn : ¬(corner a i).toNat+1<K := by omega
      rw [ite_eq_right hn,dite_eq_right h,Option.map_none]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

lemma directionCode_first {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).1.val=v.val/2 := rfl

lemma directionCode_second {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).2=decide (v.val%2=1) := by
  have hf (b : Fin 2) : finTwoEquiv b=decide (b.val=1) := by
    fin_cases b <;> rfl
  exact hf _

/-- A binary index gives exactly the signed coordinate code used by
the finite dense-chain transition; unused indices still reject. -/
theorem axisWordStep_eq {q K k : ℕ} (a : Grid (I := Fin q) K) (bits : Fin k → Bool) :
    axisWordStep ((K,gridNatCode a),List.ofFn bits)=
      (axisCodeStep a (FairBits.binaryWordEquiv k bits)).map gridNatCode := by
  rw [axisWordStep,bitValue_eq_word]
  let v := FairBits.binaryWordEquiv k bits
  change axisListStep (((K,gridNatCode a),v.val/2),decide (v.val%2=1))=
    (axisCodeStep a v).map gridNatCode
  by_cases hv : v.val<q*2
  · let u : Fin (q*2) := ⟨v.val,hv⟩
    let dir := (directionCodeEquiv q).symm u
    have hfirst : dir.1.val=v.val/2 := directionCode_first u
    have hsecond : dir.2=decide (v.val%2=1) := directionCode_second u
    rw [←hfirst,←hsecond,axisListStep_eq]
    simp only [axisCodeStep,dite_eq_left hv]
    rfl
  · have hi : ¬v.val/2<q := by omega
    have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
    simp only [axisListStep,hlen,ite_eq_right hi,axisCodeStep,dite_eq_right hv,Option.map_none]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural arithmetic for the dense acceptance exponent

Each integral completion entry is represented by a difference of two
natural numbers. The rational floor in the geometric definition is then
an ordinary natural quotient, including zero denominators.
-/

namespace ContingencyTables.GridBoundary
open scoped BigOperators Classical

lemma floor_signed_quotient (positive negative denominator : ℕ) :
    ⌊((positive : ℚ)-negative)/denominator⌋₊ =
      (positive-negative)/denominator := by
  rw [Nat.floor_div_natCast,Nat.floor_sub_natCast,Nat.floor_natCast]

lemma componentExponent_eq (d s positive negative : ℕ) :
    componentExponent d s positive negative =
      ⌊(d : ℚ)^4*(-((positive : ℚ)-negative)/s-(d : ℚ)/(d : ℚ)^8)⌋₊ := by
  by_cases hd : d=0
  · simp [hd,componentExponent]
  by_cases hs : s=0
  · simp only [hs,componentExponent,Nat.zero_mul,Nat.div_zero,Nat.cast_zero,
      div_zero,zero_sub]
    symm
    apply Nat.floor_of_nonpos
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    exact neg_nonpos.mpr (by positivity)
  have hdq : (d : ℚ)≠0 := by exact_mod_cast hd
  have hsq : (s : ℚ)≠0 := by exact_mod_cast hs
  have he : (d : ℚ)^4*(-((positive : ℚ)-negative)/s-(d : ℚ)/(d : ℚ)^8)=
      (((d^4*d^8*negative : ℕ) : ℚ)-((d^4*(d^8*positive+d*s) : ℕ) : ℚ))/
        ((s*d^8 : ℕ) : ℚ) := by
    push_cast
    field_simp [hdq,hsq]
    ring
  rw [he,floor_signed_quotient]
  rfl

variable {I J : Type*} [Fintype I] [Fintype J]

lemma integerParts_sub (R : Option I → ℕ) (P : Option J → ℕ)
    (z : I×J → ℕ) (i : Option I) (j : Option J) :
    ((integerParts R P z i j).1 : ℤ)-(integerParts R P z i j).2=
      DenseAffine.integerTable R P z i j := by
  cases i <;> cases j
  all_goals simp only [integerParts,DenseAffine.integerTable,Nat.cast_zero,sub_zero,
    Nat.cast_sum,Nat.cast_add]
  ring

lemma integerParts_sub_rat (R : Option I → ℕ) (P : Option J → ℕ)
    (z : I×J → ℕ) (i : Option I) (j : Option J) :
    ((integerParts R P z i j).1 : ℚ)-(integerParts R P z i j).2=
      (DenseAffine.integerTable R P z i j : ℚ) := by
  exact_mod_cast integerParts_sub R P z i j

variable {q K : ℕ}

lemma arithmeticExponentAt_eq (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I×J ≃ Fin q) (a : Grid (I := Fin q) K)
    (g : Option (Option I×Option J)) :
    arithmeticExponentAt R P d e a g=
      ⌊(d : ℚ)^4*rationalComponent R P d e a g⌋₊ := by
  cases g with
  | none => simp [arithmeticExponentAt,rationalComponent]
  | some g =>
    simp only [arithmeticExponentAt,componentExponent_eq,integerParts_sub_rat,
      rationalComponent]

/-- A finite maximum of explicitly computable natural quotients is exactly
the exponent used in the dense Metropolis acceptance probability. -/
theorem denseExponent_eq_arithmetic (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I×J ≃ Fin q) (a : Grid (I := Fin q) K) :
    denseExponent R P d e a=
      Finset.univ.sup' Finset.univ_nonempty (arithmeticExponentAt R P d e a) := by
  have hm : Monotone (fun x : ℚ => ⌊(d : ℚ)^4*x⌋₊) := by
    intro x y hxy
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (by positivity))
  unfold denseExponent rationalPenalty
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => ⌊(d : ℚ)^4*x⌋₊) hm.map_sup]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro g _
  exact (arithmeticExponentAt_eq R P d e a g).symm

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list arithmetic for integral dense completion -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma rowTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (i : Fin m) :
    rowTotal (matrixCode z,i.val)=∑ j,z i j := by
  simp only [rowTotal,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn]

lemma columnTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) (j : Fin n) :
    columnTotal (matrixCode z,j.val)=∑ i,z i j := by
  simp only [columnTotal,matrixCode,List.map_ofFn,Function.comp_apply,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some,Fin.eta,List.sum_ofFn]

lemma matrixTotal_code {m n : ℕ} (z : Fin m → Fin n → ℕ) :
    matrixTotal (matrixCode z)=∑ i,∑ j,z i j := by
  simp only [matrixTotal,matrixCode,List.map_ofFn,Function.comp_apply,List.sum_ofFn]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma marginCode_getD {m : ℕ} (R : Option (Fin m) → ℕ) (i : Option (Fin m)) :
    (marginCode R).getD (optionIndex i) 0=R i := by
  cases i with
  | none => rfl
  | some i =>
    simp only [marginCode,optionIndex,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,
      List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]

theorem completionParts_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    completionParts (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))=
      GridBoundary.integerParts R P (fun p => z p.1 p.2) i j := by
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [completionParts,optionIndex,ite_true, if_true,marginCode,List.headD_cons,
        List.tail_cons,List.sum_ofFn,matrixTotal_code,GridBoundary.integerParts]
    | some j =>
      simp only [completionParts,optionIndex,ite_true, if_true,Nat.add_one_ne_zero,ite_false,
        Nat.add_sub_cancel,columnTotal_code,GridBoundary.integerParts]
      exact congrArg (fun a => (a,∑ i,z i j)) (marginCode_getD P (some j))
  | some i =>
    cases j with
    | none =>
      simp only [completionParts,optionIndex,Nat.add_one_ne_zero,ite_false,ite_true, if_true,
        Nat.add_sub_cancel,rowTotal_code,GridBoundary.integerParts]
      exact congrArg (fun a => (a,∑ j,z i j)) (marginCode_getD R (some i))
    | some j =>
      simp only [completionParts,optionIndex,Nat.add_one_ne_zero,ite_false,
        Nat.add_sub_cancel,matrixEntry_code,GridBoundary.integerParts]

/-- The difference of the computed pair is the exact signed completion entry. -/
theorem completionParts_signed {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    let p := completionParts
      (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))
    (p.1 : ℤ)-p.2=DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  dsimp only
  rw [completionParts_code]
  exact GridBoundary.integerParts_sub R P _ i j

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CompletionFibreEquiv
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entry-preserving completion equivalences

The finite dense draw is transported to the retained completion fibre by
an equivalence preserving every table entry.
-/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles RowColumnPenalties
open FirstPaperPhysicalMarginal FirstPaperProfiles PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

lemma fibreLargeEquiv_apply (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u,z u ≤ B u.1.val.1 u.1.val.2)
    (hres : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c)
    (hcap : ∀ i j,small i j=false →
      (∑ k,(r k-smallRow small (smallView small z false) k+rowLargeCount small k*L)) ≤ B i j)
    (Z : CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) z) (i : I) (j : J) :
    (fibreLargeEquiv small B r c L z hz hres hcap Z).val.val i j=
      if small i j then 0 else Z.val.val.1 i j := by
  change (if hs : small i j=true then (0 : Fin (B i j+1))
    else fibreAssignment Z ⟨(i,j),Bool.eq_false_iff.mpr hs⟩).val=_
  by_cases hs : small i j=true
  · simp only [hs,dite_eq_left,ite_true, if_true,Fin.val_zero]
  · simp only [hs]
    rfl

end ContingencyTables.PhysicalCompletionFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperComputedCatalog
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-cell ordering is computed from the encoded margins -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "small" => paperSmall r c

/-- The proof-level cell equivalence enumerates exactly the list made
by the polynomial catalog program, in the same order. -/
theorem computedCellEquiv_catalog :
    cellCatalog small (computedCellEquiv r c)=computedCatalog r c := by
  apply List.ext_getElem
  · simp only [cellCatalog,List.length_ofFn]
  · intro i hi hj
    simp only [cellCatalog,List.getElem_ofFn]
    exact catalogCell_coordinates r c ⟨i,hj⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma prepareProfileInput_eq (x : PaperStates r c) :
    prepareProfileInput ((List.ofFn r,List.ofFn c),stateCode r c (computedCellEquiv r c) x)=
      stateCodeData r c (computedCellEquiv r c) x := by
  unfold prepareProfileInput stateCodeData codeCheckData
  rw [computedCellEquiv_catalog]
  simp only [marginCatalog,marginThreshold_ofFn,computedCatalog]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary list exponent equals the geometric dense exponent -/

namespace ContingencyTables.DensePrograms
open scoped BigOperators Classical
open GridBoundary ProfilePrograms

variable {m n : ℕ}

lemma optionIndex_lt (i : Option (Fin m)) : optionIndex i < m + 1 := by
  cases i with
  | none => simp [optionIndex]
  | some i => simpa only [optionIndex,Nat.add_lt_add_iff_right] using i.isLt

lemma exists_optionIndex (a : ℕ) (ha : a < m + 1) :
    ∃ i : Option (Fin m),optionIndex i=a := by
  cases a with
  | zero => exact ⟨none,rfl⟩
  | succ a => exact ⟨some ⟨a,by omega⟩,rfl⟩

lemma exponentCell_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (z : Fin m → Fin n → ℕ) (i : Option (Fin m)) (j : Option (Fin n)) :
    exponentCell (exponentDataCode R P d z,(optionIndex i,optionIndex j))=
      componentExponent d (min (R i) (P j))
        (integerParts R P (fun p => z p.1 p.2) i j).1
        (integerParts R P (fun p => z p.1 p.2) i j).2 := by
  simp only [exponentCell,exponentCellData,exponentDataCode,componentValue,
    marginCode_getD,completionParts_code]

lemma mem_exponentCells_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (z : Fin m → Fin n → ℕ) (i : Option (Fin m)) (j : Option (Fin n)) :
    (optionIndex i,optionIndex j)∈exponentCells (exponentDataCode R P d z) := by
  apply (mem_cellPairs _ _ _ _).mpr
  simpa only [marginCode,List.length_cons,List.length_ofFn] using
    And.intro (optionIndex_lt i) (optionIndex_lt j)

/-- The list maximum contains every cell once; its initial zero accounts
for the extra zero component in the nonnegative rational penalty. -/
theorem fullExponent_code {q K : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (e : Fin m×Fin n ≃ Fin q)
    (a : Grid (I := Fin q) K) :
    fullExponent (exponentDataCode R P d (fun i j => cornerFree R P d e a (i,j)))=
      denseExponent R P d e a := by
  let z := fun i j => cornerFree R P d e a (i,j)
  let data := exponentDataCode R P d z
  rw [denseExponent_eq_arithmetic]
  apply le_antisymm
  · apply (listMaximum_le (exponentValues data) 0 _).mpr
    refine ⟨Nat.zero_le _,?_⟩
    intro b hb
    obtain ⟨ij,hij,rfl⟩ := List.mem_map.mp hb
    have hbound := (mem_cellPairs _ _ ij.1 ij.2).mp hij
    have hi : ij.1 < m + 1 := by
      simpa only [data,exponentDataCode,marginCode,List.length_cons,List.length_ofFn] using hbound.1
    have hj : ij.2 < n + 1 := by
      simpa only [data,exponentDataCode,marginCode,List.length_cons,List.length_ofFn] using hbound.2
    obtain ⟨i,hi⟩ := exists_optionIndex ij.1 hi
    obtain ⟨j,hj⟩ := exists_optionIndex ij.2 hj
    have he : ij=(optionIndex i,optionIndex j) := Prod.ext hi.symm hj.symm
    rw [he]
    change exponentCell (exponentDataCode R P d z,(optionIndex i,optionIndex j))≤_
    rw [exponentCell_code]
    exact Finset.le_sup' (arithmeticExponentAt R P d e a) (Finset.mem_univ (some (i,j)))
  · apply Finset.sup'_le
    intro g _
    cases g with
    | none => exact Nat.zero_le _
    | some ij =>
      have hmem : exponentCell (data,(optionIndex ij.1,optionIndex ij.2))∈exponentValues data :=
        List.mem_map.mpr ⟨(optionIndex ij.1,optionIndex ij.2),
          mem_exponentCells_code R P d z ij.1 ij.2,rfl⟩
      have hle := le_listMaximum_member (exponentValues data) 0 _ hmem
      rw [show data=exponentDataCode R P d z from rfl,exponentCell_code] at hle
      exact hle

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleCellProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

variable {m n q K : ℕ}

theorem gridCellValue_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q)
    (i : Fin m) (j : Fin n) :
    gridCellValue (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))=
      cornerFree R P d e a (i,j) := by
  have hR := marginCode_getD R (some i)
  have hP := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hR
  change (marginCode P).getD (j.val+1) 0=P (some j) at hP
  simp only [gridCellValue,gridCellWidth,shiftedCell,exponentCellData,exponentDataCode,
    hR,hP,matrixEntry_code,cornerFree,integerWidth]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a binary grid matrix to its integer bin corner -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial GridBoundary

variable {m n q K : ℕ}

private lemma scaleRow_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) (i : Fin m) :
    scaleRow (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat),i.val)=
      List.ofFn (fun j => cornerFree R P d e a (i,j)) := by
  have hcol : scaleColumns (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat))=List.range n := by
    simp only [scaleColumns,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold scaleRow
  rw [hcol]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j < n := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,scaleRowEntry]
    exact gridCellValue_code R P d a e i ⟨j,hjn⟩

/-- Every free entry is the integer width times the selected grid corner. -/
theorem scaleMatrix_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) :
    scaleMatrix (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat))=
      matrixCode (fun i j => cornerFree R P d e a (i,j)) := by
  have hrow : scaleRows (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat))=List.range m := by
    simp only [scaleRows,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold scaleMatrix matrixCode
  rw [hrow]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact scaleRow_code R P d a e ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGridExponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense exponent directly from a binary grid matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

theorem gridExponent_code {m n q K : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (a : Grid (I := Fin q) K)
    (e : Fin m×Fin n ≃ Fin q) :
    gridExponent (exponentDataCode R P d (fun i j => (corner a (e (i,j))).toNat))=
      denseExponent R P d e a := by
  unfold gridExponent scaledData
  rw [scaleMatrix_code]
  exact fullExponent_code R P d e a

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma sliceRow_ofFn {m n : ℕ} (f : Fin (m*n) → ℕ) (i : Fin m) :
    sliceRow ((n,List.ofFn f),i.val)=
      List.ofFn (fun j : Fin n => f (finProdFinEquiv (i,j))) := by
  have hbound : n ≤ m*n-i.val*n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul, Nat.add_comm] using h
  apply List.ext_getElem
  · simp only [sliceRow,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [sliceRow,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    change i.val*n+j=j+n*i.val
    ac_rfl

theorem unflattenGrid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (f : Fin (m*n) → ℕ) :
    unflattenGrid ((marginCode R,marginCode P),List.ofFn f)=
      matrixCode (fun i j => f (finProdFinEquiv (i,j))) := by
  have hrows : layoutRows ((marginCode R,marginCode P),List.ofFn f)=List.range m := by
    simp only [layoutRows,marginCode,List.tail_cons,List.length_ofFn]
  have hcols : (marginCode P).tail.length=n := by
    simp only [marginCode,List.tail_cons,List.length_ofFn]
  unfold unflattenGrid matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,layoutRow,hcols]
    exact sliceRow_ofFn f ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFlatExponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

theorem flatExponent_code {m n K : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (a : Grid (I := Fin (m*n)) K) :
    flatExponent (((marginCode R,marginCode P),gridNatCode a),d)=
      denseExponent R P d finProdFinEquiv a := by
  unfold flatExponent flatToGridData gridNatCode
  rw [unflattenGrid_code]
  exact gridExponent_code R P d a finProdFinEquiv

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary evaluation of the finite Metropolis coin -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

theorem dyadicWordAccept_ofFn (gap k : ℕ) (bits : Fin k → Bool) :
    dyadicWordAccept (List.ofFn bits,gap)=
      decide (FairBits.acceptDyadic gap k (FairBits.binaryWordEquiv k bits)) := by
  simp only [dyadicWordAccept,List.length_ofFn,bitValue_eq_word,FairBits.acceptDyadic]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary dense program realizes the exact finite transition -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped Classical

noncomputable section

theorem flatMetropolisStep_pair {m n d p k : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (proposal : Fin p → Bool) (coins : Fin k → Bool) :
    flatMetropolisStep ((((marginCode R,marginCode P),gridNatCode a),d),
      (List.ofFn proposal,List.ofFn coins)) =
      gridNatCode (match axisCodeStep a (binaryWordEquiv p proposal) with
        | none => a
        | some b => if acceptDyadic
            (denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a)
            k (binaryWordEquiv k coins) then b else a) := by
  have hc : flatStepCandidate ((((marginCode R,marginCode P),gridNatCode a),d),
      (List.ofFn proposal,List.ofFn coins)) =
      (axisCodeStep a (binaryWordEquiv p proposal)).map gridNatCode :=
    axisWordStep_eq a proposal
  unfold flatMetropolisStep
  rw [hc]
  cases h : axisCodeStep a (binaryWordEquiv p proposal) with
  | none => rfl
  | some b =>
    simp only [Option.map_some,Option.elim_some,flatAcceptCandidate,replaceFlat]
    simp only [flatExponent_code,dyadicWordAccept_ofFn,decide_eq_true_eq]
    split_ifs <;> rfl

lemma ofFn_split_take {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).take p=List.ofFn ((splitWordEquiv p k bits).1) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left (Nat.le_add_right p k)]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

lemma ofFn_split_drop {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).drop p=List.ofFn ((splitWordEquiv p k bits).2) := by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn,Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change p+i=p+i
    rfl

/-- Exact pointwise agreement, hence every finite-word law and mixing
bound for `denseBitStep` applies to the polynomial list implementation. -/
theorem flatWordStep_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : Fin (denseStepBits d) → Bool) :
    flatWordStep ((((marginCode R,marginCode P),gridNatCode a),d),List.ofFn bits)=
      gridNatCode (denseBitStep R P d finProdFinEquiv a bits) := by
  dsimp only [flatWordStep,proposalWidth]
  have ht := ofFn_split_take (p := Nat.clog 2 (8*d)) (k := 8*d^5) bits
  have hd := ofFn_split_drop (p := Nat.clog 2 (8*d)) (k := 8*d^5) bits
  have hp : ((List.ofFn bits).take (Nat.clog 2 (8*d)),
      (List.ofFn bits).drop (Nat.clog 2 (8*d))) =
      (List.ofFn (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1,
        List.ofFn (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2) := by
    apply Prod.ext
    · exact ht
    · exact hd
  have h := congrArg (fun z => flatMetropolisStep
    ((((marginCode R,marginCode P),gridNatCode a),d),z)) hp
  refine h.trans ((flatMetropolisStep_pair R P a
    (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1
    (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2).trans ?_)
  change gridNatCode (match axisCodeStep a (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1 with
    | none => a
    | some b => if acceptDyadic
        (denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a)
        (8*d^5) (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2 then b else a)=_
  unfold denseBitStep
  dsimp only
  cases axisCodeStep a (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1 with
  | none => rfl
  | some b =>
    dsimp only

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise agreement of the binary dense loop and the finite walk -/

namespace ContingencyTables.DensePrograms
open GridBoundary FirstSuccess
open scoped Classical

noncomputable section

lemma advance_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : Fin (denseStepBits d) → Bool) :
    advance (List.ofFn bits,(((marginCode R,marginCode P),gridNatCode a),d))=
      (((marginCode R,marginCode P),
        gridNatCode (denseBitStep R P d finProdFinEquiv a bits)),d) := by
  unfold advance replaceFlat
  rw [flatWordStep_code]

theorem walkWords_ofFn {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (steps : ℕ)
    (bits : Fin steps → Fin (denseStepBits d) → Bool) :
    walkWords ((((marginCode R,marginCode P),gridNatCode a),d),
      List.ofFn (fun i => List.ofFn (bits i)))=
      (((marginCode R,marginCode P),
        gridNatCode (wordWalk (denseBitStep R P d finProdFinEquiv) a steps bits)),d) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    unfold walkWords at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change advance (List.ofFn (bits (Fin.last steps)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun data bits => advance (bits,data)) (((marginCode R,marginCode P),gridNatCode a),d)) = _
    rw [ih (Fin.init bits)]
    exact advance_code R P _ _

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma wordChunk_ofFn {n k : ℕ} (bits : Fin (n*k) → Bool) (i : Fin n) :
    wordChunk ((k,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j))) := by
  have hbound : k ≤ n*k-i.val*k := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul,Nat.add_comm] using
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  apply List.ext_getElem
  · simp only [wordChunk,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [wordChunk,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change i.val*k+j=j+k*i.val
    ac_rfl

theorem wordChunks_ofFn {n k : ℕ} (hk : 0<k) (bits : Fin (n*k) → Bool) :
    wordChunks (k,List.ofFn bits)=
      List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j)))) := by
  have hrows : completeWordRows (k,List.ofFn bits)=List.range n := by
    simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ hk]
  unfold wordChunks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact wordChunk_ofFn bits ⟨i,hin⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial program for the complete flat-word dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms

lemma denseStepBits_pos {d : ℕ} (hd : 0<d) : 0<denseStepBits d := by
  have h := Nat.mul_pos (by decide : 0<8) (pow_pos hd 5)
  exact h.trans_le (Nat.le_add_left _ _)

noncomputable section
open scoped Classical

/-- The literal flat-bit program computes exactly the finite Boolean walk.
The polynomial runtime theorem above applies to every input word. -/
theorem flatWordWalk_code {m n d : ℕ} (hd : 0<d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (steps : ℕ)
    (bits : Fin (steps*denseStepBits d) → Bool) :
    flatWordWalk ((((marginCode R,marginCode P),gridNatCode a),d),List.ofFn bits)=
      (((marginCode R,marginCode P),
        gridNatCode (denseBooleanWalk R P d finProdFinEquiv a steps bits)),d) := by
  dsimp only [flatWordWalk]
  rw [wordChunks_ofFn (denseStepBits_pos hd) bits]
  exact walkWords_ofFn R P a steps (gridWordEquiv steps (denseStepBits d) bits)

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionTest
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial exact acceptance test for a free integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

theorem completionNonnegative_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    completionNonnegative (((marginCode R,marginCode P),matrixCode z),
      (optionIndex i,optionIndex j))=true ↔
      0≤DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  have h := completionParts_signed R P z i j
  simp only [completionNonnegative,decide_eq_true_eq]
  dsimp only at h
  omega

theorem completionValid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ) :
    completionValid ((marginCode R,marginCode P),matrixCode z)=true ↔
      ∀ i j,0≤DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  simp only [completionValid,List.all_eq_true]
  constructor
  · intro h i j
    apply (completionNonnegative_code R P z i j).mp
    apply h
    apply (mem_cellPairs _ _ _ _).mpr
    simpa only [marginCode,List.length_cons,List.length_ofFn] using
      And.intro (optionIndex_lt i) (optionIndex_lt j)
  · intro h ij hij
    obtain ⟨i,j⟩ := ij
    have hh := (mem_cellPairs _ _ i j).mp hij
    simp only [marginCode,List.length_cons,List.length_ofFn] at hh
    obtain ⟨a,ha⟩ := exists_optionIndex i hh.1
    obtain ⟨b,hb⟩ := exists_optionIndex j hh.2
    subst i
    subst j
    exact (completionNonnegative_code R P z a b).mpr (h a b)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletedMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction of the completed integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma completedEntry_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) (i : Option (Fin m)) (j : Option (Fin n)) :
    completedEntry (((marginCode R,marginCode P),matrixCode z),(optionIndex i,optionIndex j))=
      DenseAffine.naturalTable R P (fun ij => z ij.1 ij.2) i j := by
  have h := completionParts_signed R P z i j
  unfold completedEntry DenseAffine.naturalTable
  dsimp only at h
  rw [←h]
  omega

lemma optionIndex_finSucc {m : ℕ} (i : Fin (m+1)) : optionIndex (finSuccEquiv m i)=i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [finSuccEquiv_zero,optionIndex,Fin.val_zero]
  · simp only [finSuccEquiv_succ,optionIndex,Fin.val_succ]

private lemma completedRow_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) (i : Fin (m+1)) :
    completedRow (((marginCode R,marginCode P),matrixCode z),i.val)=
      List.ofFn (fun j : Fin (n+1) => DenseAffine.naturalTable R P
        (fun ij => z ij.1 ij.2) (finSuccEquiv m i) (finSuccEquiv n j)) := by
  have hc : completionColumns ((marginCode R,marginCode P),matrixCode z)=List.range (n+1) := by
    simp only [completionColumns,marginCode,List.length_cons,List.length_ofFn]
  unfold completedRow
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j < n+1 := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,completedRowEntry]
    simpa only [optionIndex_finSucc] using
      completedEntry_code R P z (finSuccEquiv m i) (finSuccEquiv n ⟨j,hjn⟩)

theorem completedMatrix_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (z : Fin m → Fin n → ℕ) :
    completedMatrix ((marginCode R,marginCode P),matrixCode z)=
      matrixCode (fun i : Fin (m+1) => fun j : Fin (n+1) =>
        DenseAffine.naturalTable R P (fun ij => z ij.1 ij.2) (finSuccEquiv m i) (finSuccEquiv n j)) := by
  have hr : completionRows ((marginCode R,marginCode P),matrixCode z)=List.range (m+1) := by
    simp only [completionRows,marginCode,List.length_cons,List.length_ofFn]
  unfold completedMatrix
  rw [hr]
  unfold matrixCode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m+1 := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact completedRow_code R P z ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem scaledWordValue_ofFn (M k : ℕ) (hM : 0<M) (bits : Fin k → Bool) :
    scaledWordValue (M,List.ofFn bits)=(FairBits.scaledBitInteger M k hM bits).val := by
  simp only [scaledWordValue,List.length_ofFn,bitValue_eq_word]
  rfl

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary offset program computes the geometric free matrix -/

namespace ContingencyTables.DensePrograms
open GridBoundary ProfilePrograms
open scoped Classical

noncomputable section
variable {m n q K : ℕ}

lemma gridCellWidth_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q)
    (i : Fin m) (j : Fin n) :
    gridCellWidth (exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))=
      integerWidth R P d (i,j) := by
  have hR := marginCode_getD R (some i)
  have hP := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hR
  change (marginCode P).getD (j.val+1) 0=P (some j) at hP
  simp only [gridCellWidth,shiftedCell,exponentCellData,exponentDataCode,hR,hP,integerWidth]

lemma offsetBits_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (z : Fin m → Fin n → ℕ) (words : Fin (m*n) → List Bool)
    (i : Fin m) (j : Fin n) :
    offsetBits ((exponentDataCode R P d z,List.ofFn words),(i.val,j.val))=
      words (finProdFinEquiv (i,j)) := by
  have hv : i.val*n+j.val=(finProdFinEquiv (i,j)).val := by
    change i.val*n+j.val=j.val+n*i.val
    ac_rfl
  simp only [offsetBits,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn,hv]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,(finProdFinEquiv (i,j)).isLt,
    dite_true,Option.getD_some,Fin.eta]

lemma offsetFreeEntry_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool)
    (i : Fin m) (j : Fin n) :
    offsetFreeEntry ((exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words),(i.val,j.val))=
      cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j))) := by
  simp only [offsetFreeEntry,gridCellValue_code,gridCellWidth_code,offsetBits_code]

private lemma offsetRow_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool) (i : Fin m) :
    offsetRow ((exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words),i.val)=
      List.ofFn (fun j => cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j)))) := by
  have hcols : scaleColumns (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat))=List.range n := by
    simp only [scaleColumns,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold offsetRow
  rw [hcols]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjn : j<n := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,offsetRowEntry]
    exact offsetFreeEntry_code R P d a words i ⟨j,hjn⟩

theorem offsetMatrix_code (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) (words : Fin (m*n) → List Bool) :
    offsetMatrix (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),List.ofFn words)=
      matrixCode (fun i j => cornerFree R P d finProdFinEquiv a (i,j)+
        scaledWordValue (integerWidth R P d (i,j),words (finProdFinEquiv (i,j)))) := by
  have hrows : scaleRows (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat))=List.range m := by
    simp only [scaleRows,exponentDataCode,marginCode,List.tail_cons,List.length_ofFn]
  unfold offsetMatrix matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact offsetRow_code R P d a words ⟨i,him⟩

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient program computes the full free part of a dense trial -/

namespace ContingencyTables.DensePrograms
open GridBoundary ProfilePrograms
open scoped Classical

noncomputable section

private lemma fin_transport_val {α : Sort*} {n : α → ℕ} {a b : α}
    (h : a=b) (x : Fin (n a)) : ((h ▸ x) : Fin (n b)).val=x.val := by
  cases h
  rfl

lemma drawOffsetWords_value {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {q : ℕ}
    (e : I×J ≃ Fin q) (w : I×J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ)
    (bits : OffsetWords e w h d) (p : I×J) :
    (drawOffsetWords e w hw h d bits p).val=
      scaledWordValue (w p,List.ofFn (bits (e p))) := by
  rw [scaledWordValue_ofFn _ _ (hw p)]
  simp only [drawOffsetWords,offsetCoordinateEquiv,Equiv.piCongrLeft'_symm_apply,
    fin_transport_val,FairBits.scaledBitInteger,FairBits.scaledInteger]
  congr 2
  exact congrArg w (e.symm_apply_apply p)

theorem offsetMatrix_trialFree {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hw : ∀ p,0 < integerWidth R P d p) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : OffsetWords finProdFinEquiv (integerWidth R P d) h d) :
    offsetMatrix (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),
        List.ofFn (fun i => List.ofFn (bits i)))=
      matrixCode (fun i j => trialFree R P d finProdFinEquiv
        (a,drawOffsetWords finProdFinEquiv (integerWidth R P d) hw h d bits) (i,j)) := by
  rw [offsetMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [trialFree,trialBoxEquiv_val,drawOffsetWords_value]
  simp only [cornerFree]
  exact Nat.add_comm _ _

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

open scoped BigOperators

lemma take_ofFn_sum {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum=∑ j : Fin i.val,width (Fin.castLE i.isLt.le j) := by
  rw [←Fin.ofFn_take_eq_take_ofFn i.isLt.le,List.sum_ofFn]
  rfl

theorem dependentChunk_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩)) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb : ((List.ofFn width).take i.val).sum+width i≤∑ j,width j := by
    by_cases hi : width i=0
    · rw [hi,Nat.add_zero,←List.sum_ofFn]
      exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
    · have hh := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
      rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at hh
      dsimp only at hh
      omega
  have hlen : width i≤(∑ j,width j)-((List.ofFn width).take i.val).sum :=
    Nat.le_sub_of_add_le (by omega)
  apply List.ext_getElem
  · simp only [dependentChunk,chunkStart,List.length_take,List.length_drop,List.length_ofFn,hw,
      min_eq_left hlen]
  · intro j hj _
    simp only [dependentChunk,chunkStart,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    simp only [finSigmaFinEquiv_apply,take_ofFn_sum]

theorem dependentChunks_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) :
    dependentChunks (List.ofFn width,List.ofFn bits)=
      List.ofFn (fun i => List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩))) := by
  unfold dependentChunks chunkIndices
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hiq : i < q := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact dependentChunk_ofFn width bits ⟨i,hiq⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

lemma cellPairs_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    cellPairs (List.ofFn r,List.ofFn c)=List.ofFn (fun v : Fin (m*n) =>
      (((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1.val,
        ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).2.val)) := by
  apply List.ext_getElem
  · simp only [cellPairs,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    simp only [cellPairs,List.getElem_map,List.getElem_range,List.getElem_ofFn,pairAt,List.length_ofFn]
    rfl

noncomputable section
open scoped Classical

lemma offsetLength_code {m n q K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) (a : Grid (I := Fin q) K) (e : Fin m×Fin n ≃ Fin q) (i : Fin m) (j : Fin n) :
    offsetLength ((exponentDataCode R P d
      (fun i j => (corner a (e (i,j))).toNat),h),(i.val,j.val))=
      offsetBitLength (integerWidth R P d (i,j)) h d := by
  change Nat.clog 2 (gridCellWidth (exponentDataCode R P d
    (fun i j => (corner a (e (i,j))).toNat),(i.val,j.val))+1)+4*(h+d)=_
  rw [gridCellWidth_code]
  rfl

theorem offsetLengths_code {m n K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d h : ℕ) (a : Grid (I := Fin (m*n)) K) :
    offsetLengths (exponentDataCode R P d
      (fun i j => (corner a (finProdFinEquiv (i,j))).toNat),h)=
      List.ofFn (fun v : Fin (m*n) => offsetBitLength
        (integerWidth R P d (finProdFinEquiv.symm v)) h d) := by
  unfold offsetLengths freeCells
  simp only [exponentDataCode,marginCode,List.tail_cons]
  rw [cellPairs_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact offsetLength_code R P d h a finProdFinEquiv
    (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FirstSuccessProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial first-success selection for a supplied list of trial words -/

namespace ContingencyTables.FirstSuccessProgram
open MatchingFPRAS.TreeTyped

variable {A B W : Type} [Codec A] [Codec B] [Codec W] [Inhabited B]

noncomputable section
open scoped Classical

omit [Codec A] [Codec B] [Inhabited B] in
theorem retry_ofFn {k n : ℕ} (f : A×List Bool → Option B)
    (a : A) (fallback : B) (bits : Fin n → Fin k → Bool) :
    retry f ((a,fallback),List.ofFn (fun i => List.ofFn (bits i)))=
      FirstSuccess.wordRetry (fun word => f (a,List.ofFn word)) fallback n bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [retry,List.ofFn_succ,List.map_cons,FirstSuccess.wordRetry]
    cases h : f (a,List.ofFn (bits 0)) with
    | none =>
      simp only [firstSome,Option.getD_none]
      exact ih (Fin.tail bits)
    | some b => simp only [firstSome,Option.getD_some]

theorem wordRetry_map {α β : Type*} {k : ℕ} (f : (Fin k → Bool) → Option α)
    (g : α → β) (fallback : α) (n : ℕ) (bits : Fin n → Fin k → Bool) :
    FirstSuccess.wordRetry (fun word => (f word).map g) (g fallback) n bits=
      g (FirstSuccess.wordRetry f fallback n bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FirstSuccess.wordRetry]
    cases f (bits 0) with
    | none => simpa only [Option.map_none,Option.getD_none] using ih (Fin.tail bits)
    | some x => rfl

end
end ContingencyTables.FirstSuccessProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete trial program uses the manuscript's finite-bit experiment -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

lemma flatToGridData_code {m n K : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (d : ℕ) (a : Grid (I := Fin (m*n)) K) :
    flatToGridData (((marginCode R,marginCode P),gridNatCode a),d)=
      exponentDataCode R P d (fun i j => (corner a (finProdFinEquiv (i,j))).toNat) := by
  unfold flatToGridData gridNatCode
  rw [unflattenGrid_code]
  rfl

lemma trialGrid_code {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialGrid (trialInput R P h a (List.ofFn bits))=
      exponentDataCode R P d (fun i j =>
        (corner (denseBooleanWalk R P d finProdFinEquiv a (d^50*(h+1)^2)
          (trialWordEquiv R P d finProdFinEquiv h bits).1) (finProdFinEquiv (i,j))).toNat) := by
  dsimp only [trialGrid,trialInput,trialWalkBits]
  have ht := ofFn_split_take (p := (d^50*(h+1)^2)*denseStepBits d)
    (k := ∑ j : Fin (m*n),offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d) bits
  have he := congrArg (fun w => flatToGridData
    (flatWordWalk ((((marginCode R,marginCode P),gridNatCode a),d),w))) ht
  refine he.trans ?_
  rw [flatWordWalk_code hd]
  exact flatToGridData_code R P d _

lemma trialOffsets_code {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialOffsets (trialInput R P h a (List.ofFn bits))=
      List.ofFn (fun j => List.ofFn ((trialWordEquiv R P d finProdFinEquiv h bits).2 j)) := by
  unfold trialOffsets
  rw [trialGrid_code hd,offsetLengths_code]
  dsimp only [trialInput,trialWalkBits]
  have ht := ofFn_split_drop (p := (d^50*(h+1)^2)*denseStepBits d)
    (k := ∑ j : Fin (m*n),offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d) bits
  have he := congrArg (fun w => dependentChunks
    (List.ofFn (fun j : Fin (m*n) => offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d),w)) ht
  refine he.trans ?_
  rw [dependentChunks_ofFn]
  rfl

theorem trialCompletion_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    trialCompletion (trialInput R P h a (List.ofFn bits))=
      ((marginCode R,marginCode P),matrixCode (fun i j => trialFree R P d finProdFinEquiv
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a bits) (i,j))) := by
  have hd0 : 0 < d := by omega
  unfold trialCompletion
  rw [trialGrid_code hd0,trialOffsets_code hd0]
  apply Prod.ext
  · rfl
  · exact offsetMatrix_trialFree R P (integerWidth_pos R P d hd hR hP) h _ _

lemma acceptCompletion_trialFree {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : ∑ i,R i=∑ j,P j) (t : DenseTrial R P d (m*n)) :
    acceptCompletion ((marginCode R,marginCode P),
      matrixCode (fun i j => trialFree R P d finProdFinEquiv t (i,j)))=
      (trialSuccess R P d finProdFinEquiv htotal t).map tableOutput := by
  have hv := completionValid_code R P (fun i j => trialFree R P d finProdFinEquiv t (i,j))
  by_cases ht : TrialAccepted R P d finProdFinEquiv t
  · have hc := hv.mpr ht
    simp only [acceptCompletion,hc,ite_true, if_true,trialSuccess,dite_eq_left ht,Option.map_some]
    rw [completedMatrix_code]
    rfl
  · have hc : completionValid ((marginCode R,marginCode P),
        matrixCode (fun i j => trialFree R P d finProdFinEquiv t (i,j)))≠true := by
      intro h
      exact ht (hv.mp h)
    simp only [acceptCompletion,hc,Bool.false_eq_true,ite_false,trialSuccess,dite_eq_right ht,Option.map_none]

/-- The physical binary program returns exactly the successful table of the
declared finite Boolean experiment, with the same rejection event. -/
theorem denseTrialCode_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (bits : Fin (denseTrialBits R P d finProdFinEquiv h) → Bool) :
    denseTrialCode (trialInput R P h a (List.ofFn bits))=
      (trialSuccess R P d finProdFinEquiv htotal
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a bits)).map tableOutput := by
  unfold denseTrialCode
  rw [trialCompletion_code R P hd hR hP]
  exact acceptCompletion_trialFree R P htotal _

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded binary draw is exactly the analyzed Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped BigOperators Classical

noncomputable section

lemma trialWidth_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) :
    trialWidth ((((marginCode R,marginCode P),gridNatCode a),d),h)=
      denseTrialBits R P d finProdFinEquiv h := by
  unfold trialWidth
  rw [flatToGridData_code,offsetLengths_code,List.sum_ofFn]
  rfl

lemma denseTrialBits_pos {m n d : ℕ} (hd : 0 < d)
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (h : ℕ) :
    0 < denseTrialBits R P d finProdFinEquiv h := by
  have hw := denseStepBits_pos hd
  have ht : 0 < (d^50*(h+1)^2)*denseStepBits d := by positivity
  unfold denseTrialBits
  omega

/-- This identifies every output, including the all-rejections fallback,
with the actual finite Boolean sampler whose total-variation bound is proved. -/
theorem denseDrawCode_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (denseDrawBits R P d finProdFinEquiv h) → Bool) :
    denseDrawCode (drawInput R P h a fallback (List.ofFn bits))=
      tableOutput (denseBooleanDraw R P d hd hR hP finProdFinEquiv htotal h a fallback bits) := by
  have hd0 : 0 < d := by omega
  unfold denseDrawCode drawChunks drawInput
  dsimp only [Prod.fst,Prod.snd]
  rw [trialWidth_code]
  have hc := wordChunks_ofFn (n := d^4*(h+1)) (denseTrialBits_pos hd0 R P h) bits
  let params : DenseDrawParameters := ((((marginCode R,marginCode P),gridNatCode a),d),h)
  have he := congrArg (fun ws => FirstSuccessProgram.retry denseTrialCode
    ((params,tableOutput fallback),ws)) hc
  refine he.trans ?_
  rw [FirstSuccessProgram.retry_ofFn]
  have ht : (fun word => denseTrialCode
      (((((marginCode R,marginCode P),gridNatCode a),d),h),List.ofFn word))=
      fun word => (trialSuccess R P d finProdFinEquiv htotal
        (denseBooleanTrial R P d hd hR hP finProdFinEquiv h a word)).map tableOutput := by
    funext word
    exact denseTrialCode_eq R P hd hR hP htotal h a word
  rw [ht,FirstSuccessProgram.wordRetry_map]
  rfl

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSwapProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column permutations for dense input normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

variable {A : Type} [Codec A] [Inhabited A]

open scoped Classical

lemma swapZeroIndex_val {n : ℕ} (p i : Fin (n+1)) :
    swapZeroIndex (p.val,i.val)=(Equiv.swap 0 p i).val := by
  by_cases hi : i=0
  · subst i
    rw [Equiv.swap_apply_left]
    simp only [swapZeroIndex,Fin.val_zero,ite_true, if_true]
  · have hi0 : i.val≠0 := fun h => hi (Fin.ext h)
    by_cases hp : i=p
    · subst i
      rw [Equiv.swap_apply_right]
      simp only [swapZeroIndex,hi0,ite_false,ite_true, if_true,Fin.val_zero]
    · have hip : i.val≠p.val := fun h => hp (Fin.ext h)
      rw [Equiv.swap_apply_of_ne_of_ne hi hp]
      simp only [swapZeroIndex,hi0,hip,ite_false]

omit [Codec A] in
theorem swapZeroList_ofFn {n : ℕ} (p : Fin (n+1)) (f : Fin (n+1) → A) :
    swapZeroList (p.val,List.ofFn f)=List.ofFn (fun i => f (Equiv.swap 0 p i)) := by
  apply List.ext_getElem
  · simp only [swapZeroList,swapZeroIndices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i < n+1 := by
      simpa only [swapZeroList,swapZeroIndices,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [swapZeroList,swapZeroIndices,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      swapZeroEntry]
    rw [swapZeroIndex_val p ⟨i,hin⟩]
    rw [List.getD_eq_getElem (List.ofFn f) default (by simpa only [List.length_ofFn] using (Equiv.swap 0 p ⟨i,hin⟩).isLt)]
    simp only [List.getElem_ofFn,Fin.eta]

theorem swapMatrix_code {m n : ℕ} (i : Fin (m+1)) (j : Fin (n+1))
    (X : Fin (m+1) → Fin (n+1) → ℕ) :
    swapMatrix ((i.val,j.val),matrixCode X)=
      matrixCode (fun a b => X (Equiv.swap 0 i a) (Equiv.swap 0 j b)) := by
  unfold swapMatrix matrixCode
  rw [swapZeroList_ofFn]
  unfold swapMatrixColumns
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  exact swapZeroList_ofFn j _

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

lemma marginCode_ofFn {m : ℕ} (R : Option (Fin m) → ℕ) :
    marginCode R=List.ofFn (fun i : Fin (m+1) => R (finSuccEquiv m i)) := by
  rw [List.ofFn_succ]
  simp only [marginCode,finSuccEquiv_zero,finSuccEquiv_succ]

lemma marginPosition_val {m : ℕ} (R : Option (Fin m) → ℕ) :
    (marginPosition R).val=maximumIndex (marginCode R) := by
  rw [marginCode_ofFn]
  rfl

lemma marginCode_swap {m : ℕ} (R : Option (Fin m) → ℕ) (p : Fin (m+1)) :
    swapZeroList (p.val,marginCode R)=marginCode (fun i => R (indexPermutation p i)) := by
  rw [marginCode_ofFn,swapZeroList_ofFn,marginCode_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [indexPermutation,Equiv.trans_apply,Equiv.symm_apply_apply]

lemma indexPermutation_finSucc {m : ℕ} (p i : Fin (m+1)) :
    indexPermutation p (finSuccEquiv m i)=finSuccEquiv m (Equiv.swap 0 p i) := by
  change finSuccEquiv m (Equiv.swap 0 p ((finSuccEquiv m).symm (finSuccEquiv m i)))=_
  rw [Equiv.symm_apply_apply]

lemma indexPermutation_symm_finSucc {m : ℕ} (p i : Fin (m+1)) :
    (indexPermutation p).symm (finSuccEquiv m i)=finSuccEquiv m (Equiv.swap 0 p i) := by
  change finSuccEquiv m (Equiv.swap 0 p ((finSuccEquiv m).symm (finSuccEquiv m i)))=_
  rw [Equiv.symm_apply_apply]

lemma tableOutput_swap {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (p : Fin (m+1)) (q : Fin (n+1)) (X : Table R P) :
    swapMatrix ((p.val,q.val),tableOutput X)=
      tableOutput (tableReindex (indexPermutation p) (indexPermutation q) R P X) := by
  unfold tableOutput
  rw [swapMatrix_code]
  apply congrArg matrixCode
  funext i j
  change X.val (finSuccEquiv m (Equiv.swap 0 p i)) (finSuccEquiv n (Equiv.swap 0 q j))=
    X.val (indexPermutation p (finSuccEquiv m i)) (indexPermutation q (finSuccEquiv n j))
  rw [indexPermutation_finSucc,indexPermutation_finSucc]

lemma tableOutput_inverse_swap {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (p : Fin (m+1)) (q : Fin (n+1))
    (X : Table (fun i => R (indexPermutation p i)) (fun j => P (indexPermutation q j))) :
    swapMatrix ((p.val,q.val),tableOutput X)=
      tableOutput ((tableReindex (indexPermutation p) (indexPermutation q) R P).symm X) := by
  unfold tableOutput
  rw [swapMatrix_code]
  apply congrArg matrixCode
  funext i j
  change X.val (finSuccEquiv m (Equiv.swap 0 p i)) (finSuccEquiv n (Equiv.swap 0 q j))=
    X.val ((indexPermutation p).symm (finSuccEquiv m i)) ((indexPermutation q).symm (finSuccEquiv n j))
  rw [indexPermutation_symm_finSucc,indexPermutation_symm_finSucc]

lemma drawIndices_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) (bits : List Bool) :
    drawIndices (drawInput R P h a fallback bits)=((marginPosition R).val,(marginPosition P).val) := by
  simp only [drawIndices,drawInput,marginIndices,marginPosition_val]

lemma permuteDrawData_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (h : ℕ) (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P) (bits : List Bool) :
    permuteDrawData (((marginPosition R).val,(marginPosition P).val),
      drawInput R P h a fallback bits)=
      drawInput (normalizedMargin R) (normalizedMargin P) h a
        (tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P fallback) bits := by
  unfold permuteDrawData swapFlatData swapMargins drawInput
  rw [marginCode_swap,marginCode_swap,tableOutput_swap]
  rfl

/-- The computed maximum and both physical permutations agree with the
finite table-valued experiment on every Boolean input. -/
theorem normalizedDenseCode_eq {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (fallback : Table R P)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) :
    normalizedDenseCode (drawInput R P h a fallback (List.ofFn bits))=
      tableOutput (normalizedBooleanDraw R P hd hR hP htotal h a fallback bits) := by
  unfold normalizedDenseCode normalizedDraw preparedDraw
  rw [drawIndices_code,permuteDrawData_code]
  let E : Table R P ≃ Table (normalizedMargin R) (normalizedMargin P) :=
    tableReindex (indexPermutation (marginPosition R)) (indexPermutation (marginPosition P)) R P
  let fb : Table (normalizedMargin R) (normalizedMargin P) := E fallback
  have ht : (∑ i,normalizedMargin R i)=∑ j,normalizedMargin P j := by
    rw [normalizedMargin_total,normalizedMargin_total]
    exact htotal
  have hs := denseDrawCode_eq (normalizedMargin R) (normalizedMargin P) hd
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP) ht h a fb bits
  refine (congrArg (fun X => swapMatrix (((marginPosition R).val,(marginPosition P).val),X)) hs).trans ?_
  exact tableOutput_inverse_swap R P _ _ _

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyTableMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed binary list program constructing the greedy table -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

lemma listSplitRow_ofFn {n : ℕ} (a : ℕ) (cs : Fin n → ℕ) :
    listSplitRow a (List.ofFn cs)=
      ((splitRow a cs).unused,
        (List.ofFn (splitRow a cs).assigned,List.ofFn (splitRow a cs).remaining)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ,listSplitRow,splitRow,ih,Fin.cons_zero,Fin.cons_succ]

/-- The compiled list program computes the same feasible matrix used
by the probability analysis. -/
theorem listMatrix_ofFn {m n : ℕ} (rs : Fin m → ℕ) (cs : Fin n → ℕ) :
    listMatrix (List.ofFn rs) (List.ofFn cs)=
      List.ofFn (fun i => List.ofFn (matrix rs cs i)) := by
  induction m generalizing cs with
  | zero => rfl
  | succ m ih =>
    simp only [List.ofFn_succ,listMatrix,listSplitRow_ofFn,ih,matrix,Fin.cons_zero,
      Fin.cons_succ]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of dense sampling with computed initialization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

lemma zeroGrid_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) :
    zeroGrid (marginCode R,marginCode P)=gridNatCode (canonicalOrigin (m*n) d hd) := by
  apply List.ext_getElem
  · simp only [zeroGrid,ProfilePrograms.cellPairs,List.length_map,List.length_range,
      marginCode,List.tail_cons,List.length_ofFn,gridNatCode]
  · intro i hi hj
    simp only [zeroGrid,List.getElem_map,gridNatCode,List.getElem_ofFn,corner,
      canonicalOrigin,Int.toNat_zero]

lemma canonicalFallback_output {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (htotal : (∑ i,R i)=∑ j,P j) :
    tableOutput (canonicalFallback R P htotal)=
      GreedyFeasibleTable.listMatrix (marginCode R) (marginCode P) := by
  rw [marginCode_ofFn,marginCode_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  unfold tableOutput canonicalFallback
  change matrixCode (fun i j =>
    GreedyFeasibleTable.matrix (fun i => R (finSuccEquiv m i))
      (fun j => P (finSuccEquiv n j))
      ((finSuccEquiv m).symm (finSuccEquiv m i))
      ((finSuccEquiv n).symm (finSuccEquiv n j)))=_
  simp only [Equiv.symm_apply_apply,matrixCode]

lemma canonicalInput_code {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ) (bits : List Bool) :
    canonicalInput (((marginCode R,marginCode P),(d,h)),bits)=
      drawInput R P h (canonicalOrigin (m*n) d hd) (canonicalFallback R P htotal) bits := by
  unfold canonicalInput drawInput
  rw [zeroGrid_code R P hd,canonicalFallback_output]

/-- No caller-supplied grid or feasible fallback is needed by the
binary dense program. Every output is the analyzed table-valued draw. -/
theorem canonicalDenseDraw_eq {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ)
    (bits : Fin (normalizedDrawBits R P d h) → Bool) :
    canonicalDenseDraw (((marginCode R,marginCode P),(d,h)),List.ofFn bits)=
      tableOutput (normalizedBooleanDraw R P hd hR hP htotal h
        (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal) bits) := by
  unfold canonicalDenseDraw
  rw [canonicalInput_code R P (by omega) htotal]
  exact normalizedDenseCode_eq R P hd hR hP htotal h _ _ bits

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReservedWord
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

open GridBoundary
open scoped BigOperators Classical
noncomputable section

theorem canonicalBitCount_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ) :
    canonicalBitCount ((marginCode R,marginCode P),(d,h))=normalizedDrawBits R P d h := by
  unfold canonicalBitCount preparedCanonicalParameters
  rw [canonicalInput_code R P hd htotal]
  unfold preparedDraw
  rw [drawIndices_code,permuteDrawData_code]
  change (d^4*(h+1))*trialWidth
    ((((marginCode (normalizedMargin R),marginCode (normalizedMargin P)),
      gridNatCode (canonicalOrigin (m*n) d hd)),d),h)=_
  rw [trialWidth_code]
  rfl

lemma take_ofFn_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k=List.ofFn (prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,prefixWord,Fin.castLE]

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGridWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

lemma gridStateCount_eq (z : GridEnumerationData) : gridStateCount z=z.2^z.1.length := by
  simp [gridStateCount,clippedGridPower,clippedGridPowerInput,BinaryPowerPrograms.power_eq]

private lemma map_range_eq_ofFn {A : Type*} (f : ℕ → A) (N : ℕ) :
    (List.range N).map f=List.ofFn (fun i : Fin N => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range N) f).symm

lemma gridCoordinates_eq (z : GridEnumerationData) (x : ℕ) :
    gridCoordinates (z,x)=List.ofFn
      (fun i : Fin z.1.length => x/z.2^i.val % z.2) := by
  rw [gridCoordinates,gridCoordinateIndices,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [gridCoordinate,clippedGridPower,clippedGridPowerInput,
    BinaryPowerPrograms.power_eq]

lemma gridEnumeration_code (q K : ℕ) (a : Fin (K^q)) :
    gridNatCode (gridEnumeration q K a)=
      List.ofFn (fun i : Fin q => a.val/K^i.val % K) := by
  apply congrArg List.ofFn
  funext i
  rfl

/-- Every box state occurs once in this explicit, mixed-radix list. -/
theorem gridWords_eq (z : GridEnumerationData) :
    gridWords z=List.ofFn (fun i => gridNatCode (gridEnumeration z.1.length z.2 i)) := by
  unfold gridWords
  rw [gridStateCount_eq,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [gridCoordinates_eq,gridEnumeration_code]

lemma gridWords_eq_length (xs : List Bool) (K q : ℕ) (hq : xs.length=q) :
    gridWords (xs,K)=List.ofFn (fun i => gridNatCode (gridEnumeration q K i)) := by
  subst q
  exact gridWords_eq (xs,K)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

lemma gridWords_finFunctions (xs : List Bool) (N q : ℕ) (hq : xs.length=q) :
    gridWords (xs,N+1)=List.ofFn (fun k : Fin ((N+1)^q) =>
      List.ofFn (fun i : Fin q => ((finFunctionFinEquiv.symm k) i).val)) := by
  rw [gridWords_eq_length xs (N+1) q hq]
  rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_AdaptiveStream
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma run_bind (p : Experiment α) (q : α → Experiment β) (b : Stream) :
    (p.bind q).run b=
      let r:=p.run b
      let s:=(q r.1).run (shift r.2 b)
      (s.1,r.2+s.2) := by
  induction p generalizing b with
  | done a => simp [bind,run]
  | read p ih =>
    simp only [bind,run,ih]
    have hs (n : ℕ) : shift n (shift 1 b)=shift (1+n) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]
  | delay n p ih =>
    simp only [bind,run,ih]
    have hs (m : ℕ) : shift m (shift n b)=shift (n+m) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]

lemma run_map (f : α → β) (p : Experiment α) (b : Stream) :
    (p.map f).run b=(f (p.run b).1,(p.run b).2) := by simp [map,run_bind,run]

lemma run_word (n : ℕ) (b : Stream) :
    (word n).run b=((fun i : Fin n=>b i),n) := by
  induction n generalizing b with
  | zero => exact Prod.ext (funext (fun i=>Fin.elim0 i)) rfl
  | succ n ih =>
    simp only [word,run,run_map,ih,shift]
    congr 1
    · funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · rfl
      · simp only [Fin.cons_succ,Fin.val_succ]; congr 1; omega
    · omega

lemma mean_word (n : ℕ) (f : Bits n → ℚ) : (word n).mean f=average f := by
  rw [←average_run (word n) f n (by rw [cost_word])]
  congr 1
  funext b
  rw [run_word]
  congr 1
  funext i
  simp [extend,i.isLt]

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalPost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_CoinTM1
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
        simp only [PhysicalPost.tick,pending,table,aux,h,ite_true, if_true]) hk]
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
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_SafeTrace
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinStack
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProcess
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

lemma bind (h : Implements M out c p) (q : α → Experiment β)
    (out' : β → Cfg Γ Q) (hq : ∀ a,Implements M out' (out a) (q a)) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read c f h ih => exact .read c _ ih
  | delay c d n p hs hr ih => exact .delay c d n _ hs ih

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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PhysicalAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineStackCompiler
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Online
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_ExperimentSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineWord
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

lemma mean_prepend (n : ℕ) (acc : List Bool) (f : List Bool → ℚ) :
    (prepend n acc).mean f=(Experiment.word n).mean (fun w=>f ((List.ofFn w).reverse++acc)) := by
  induction n generalizing acc with
  | zero => simp [prepend,Experiment.word,Experiment.mean]
  | succ n ih =>
    simp only [prepend,Experiment.word,Experiment.mean,Experiment.mean_map,ih]
    congr 2 <;> congr 1 <;> funext w <;>
      simp [List.ofFn_succ,List.reverse_cons,List.append_assoc]

lemma ofFn_reverse (n : ℕ) (w : Bits n) :
    List.ofFn (reverseBits n w)=(List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [reverseBits,Equiv.coe_fn_mk,List.getElem_ofFn,List.getElem_reverse,Fin.rev,List.length_ofFn]
    congr 1
    apply Fin.ext
    change n-(i+1)=n-1-i
    omega
lemma average_reverse (n : ℕ) (f : List Bool → ℚ) :
    average (fun w : Bits n=>f (List.ofFn w).reverse)=average (fun w : Bits n=>f (List.ofFn w)) := by
  unfold average
  congr 1
  exact Fintype.sum_equiv (reverseBits n) _ _ (fun w=>by rw [ofFn_reverse])
lemma mean_prepend_nil (n : ℕ) (f : List Bool → ℚ) :
    (prepend n []).mean f=average (fun w : Bits n=>f (List.ofFn w)) := by
  rw [mean_prepend,Experiment.mean_word]
  simp only [List.append_nil]
  exact average_reverse n f

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B]

omit [TreeTyped.Codec A] [TreeTyped.Codec B] in

theorem experiment_mean (n : A → ℕ) (f : A×List Bool → B) (a : A) (g : B → ℚ) :
    (experiment n f a).mean g=
      average (fun bits : Bits (n a) => g (f (a,List.ofFn bits))) := by
  unfold experiment source
  rw [Experiment.mean_map,OnlineWord.mean_prepend_nil]

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalSequential
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TapeTools
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Physical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreePostRealization
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlinePhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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
    simpa only [inputStacks,encodeEnv,env,ite_true, if_true,weight,TreeFunction.size] using h

lemma cfg_packed {A : Type} [Codec A] (P : OnlineProc.Proc (K Reg)) (a : A) (l : Option P.Label) :
    upCfg (OnlineStack.cfg (⟨l,none,inputStacks a⟩ : StoreCfg P))=
      ⟨l.map (fun u=>(Sum.inl (TM1to1.Λ'.normal (TM2to1.Λ'.normal u)),none)),Tape.mk₁ (packed a)⟩ := by
  simp only [upCfg,OnlineStack.cfg,OnlineStack.stackCfg,input_height,CoinTM1.trCfg,
    TM1to1.trCfg,TM1to1.trTape,TM1to1.trTape',Tape.mk₁,Tape.mk₂,Tape.mk'_left,Tape.mk'_right₀,
    ListBlank.flatMap_mk,List.flatMap_nil,Option.map_map]
  rw [Tape.map_mk']
  rfl

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgramMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost.Program
open Turing PhysicalStream

lemma Realizes.mono {P : Program} {input : Tape Symbol} {f : Experiment (Tape Symbol)} {N S : ℕ}
    (h : P.Realizes input f N) (hn : N≤S) : P.Realizes input f S := by
  obtain ⟨p,hp,hm,hc⟩:=h
  exact ⟨p,hp,hm,hc.trans hn⟩
end MatchingFPRAS.PhysicalPost.Program

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_BlockMap
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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
        simp only [inputStacks,encodeEnv,env,ite_true, if_true,hs]
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeEncodingInjective
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedInverse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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
  simpa only [letter,bitRow,ite_true, if_true,Option.some.injEq] using hh
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
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)

lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
      (MachineCost.programCost (LiteralTape.eraseCode header.length)) := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _
      (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono (by simp only [Nat.one_mul]; rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as))
      ((1+LiteralBlockMap.budget (18*width) 1 as.length 0)*MachineCost.programCost unpackCode) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _ => .done (Tape.mk₁ as)) _ _ h1 h2

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma parse_natWords (ns : List ℕ) : parse (ns.flatMap encodeNat)=ns := by
  simpa only [parse,List.append_nil] using natWords_fold ns []

lemma encodeMargins_natWords {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Algorithms.encodeMargins r c=
      (m::n::(List.ofFn r++List.ofFn c)).flatMap encodeNat := by
  simp only [Algorithms.encodeMargins,List.flatMap_cons,List.flatMap_append]
  simp only [List.ofFn_comp',List.flatMap_def,List.append_assoc]

lemma marginLists_spec (m n : ℕ) (rs cs tail : List ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    marginLists (m::n::(rs++cs++tail))=(rs,cs) := by
  simp only [marginLists,List.headD_cons,List.tail_cons]
  rw [←hr,←hc]
  simp only [List.append_assoc,List.take_left,List.drop_left]

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixEncoding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public matrix encoding uniquely identifies a fixed-shape table -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS MatchingFPRAS.LiteralParse Turing

lemma encodeMatrix_flat {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    encodeMatrix X=((List.ofFn fun i => List.ofFn (X i)).flatten).flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  simp only [GreedyFeasibleTable.printMatrix,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

lemma matrix_flat_injective (m n : ℕ) (X Y : Fin m → Fin n → ℕ)
    (h : (List.ofFn (fun i => List.ofFn (X i))).flatten=
      (List.ofFn (fun i => List.ofFn (Y i))).flatten) : X=Y := by
  have hr : List.ofFn (fun i => List.ofFn (X i))=List.ofFn (fun i => List.ofFn (Y i)) :=
    List.eq_iff_flatten_eq.mpr ⟨h,by
      simp only [List.map_ofFn]
      congr 1
      funext i
      exact (List.length_ofFn).trans (List.length_ofFn.symm)⟩
  have hf := List.ofFn_injective hr
  funext i
  exact List.ofFn_injective (congrFun hf i)

lemma blankMatrix_injective {m n : ℕ} (X Y : Fin m → Fin n → ℕ)
    (h : ListBlank.mk (encodeMatrix X)=ListBlank.mk (encodeMatrix Y)) : X=Y := by
  have hp := congrArg blankNumbers h
  change parse (encodeMatrix X)=parse (encodeMatrix Y) at hp
  rw [encodeMatrix_flat,encodeMatrix_flat,GreedyFeasibleTable.parse_natWords,
    GreedyFeasibleTable.parse_natWords] at hp
  exact matrix_flat_injective m n X Y hp

end ContingencyTables.Algorithms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineRetryPrefix
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite execution prefixes of the unbounded exact-rejection loop -/

namespace ContingencyTables.OnlineRetryPrefix
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.PhysicalStream
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.OnlineControl Turing

variable {R Λ α : Type} [DecidableEq R]

lemma done (M : Λ → Instr R Λ) (out : α → Option Λ×Env R) (a : α) :
    At M out (out a).1 (out a).2 (.done a) := .done a

lemma halt (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l : Λ) (h : M l=.halt) (a : α) (ha : (out a).1=none) :
    At M out (some l) (out a).2 (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  have hd:=done M out a
  simpa only [At,code,h,TM2.stepAux,OnlineControl.cfg,ha,Option.map_none] using hd

lemma nilBranch (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (hi : E i=.nil) (p : Experiment α)
    (hp : At M out (some a) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_false,OnlineControl.cfg,Option.map_some] using hp

lemma consBranch (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (x y : Data) (hi : E i=.cons x y) (p : Experiment α)
    (hp : At M out (some b) E p) :
    At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_true,OnlineControl.cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l next : Λ) (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b => ⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b => ⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh:=hq'.relabel (code M) (coins M) (fun u => Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _ => rfl) (fun _ => rfl)
  apply Executes.step _ _ _ _ rfl
  have hb:=hh.bind p (fun a => OnlineControl.cfg M (out a).1 (out a).2) (fun b => by
    simpa only [At,OnlineControl.cfg,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Option Λ×Env R)
    (l next : Λ) (P : RegisterProc.Proc (K R))
    (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧
      q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _ => p)),
    call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit => F)
      r hr (fun _ => p) (fun _ => hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _ => p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _ => p) p.cost (fun _ => le_rfl)
    simp only [Experiment.cost]
    omega

end ContingencyTables.OnlineRetryPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed online machine for repeat-until-success -/

namespace ContingencyTables.OnlineIntegerRetry
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeMachine
open MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeTyped (Codec)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.PhysicalStream

lemma prepare_exec (x s : Data) :
    RegisterProc.Exec prepareProc (encodeEnv (env x .nil s))
      (encodeEnv (env x .nil (.cons x s))) (5*TreeFunction.size x+8) := by
  exact ((copy01 x .nil s).seq (cons12 x x s)).mono (by simp only [size_nil]; omega)

lemma retry_exec (x y s : Data) :
    RegisterProc.Exec retryProc (encodeEnv (env y .nil (.cons x s)))
      (encodeEnv (env x .nil s)) (6*TreeFunction.size x+TreeFunction.size y+11) := by
  exact ((split12 y .nil x s).seq ((copy10 y x s).seq (clear1 x x s))).mono
    (by simp only [size_nil]; omega)

lemma finish_exec (x y s : Data) :
    RegisterProc.Exec finishProc (encodeEnv (env y (bit true) (.cons x s)))
      (encodeEnv (env y .nil s)) (3*TreeFunction.size x+12) := by
  exact ((clear1 y (bit true) (.cons x s)).seq
    ((split12 y .nil x s).seq (clear1 y x s))).mono (by
      simp only [bit,ite_true, if_true,size_cons,size_nil]
      omega)

variable {A B : Type} [Codec A] [Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)} (F : OnlineTree.Realizer f)

lemma prefix_step (a : A) (s : Data) (rest : Experiment (Option B))
    (hrest : OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) rest) :
    ∃ q,OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) q ∧
      (∀ g : Option B → ℚ,q.mean g=
        ((f a).bind (fun b => b.elim rest (fun b => .done (some b)))).mean g) ∧
      q.cost ≤ rest.cost+stepCost F a := by
  classical
  let M:=instructions F
  let out : Option B → Option Label×Env Reg := output a s
  obtain ⟨u,hu,hum,huc⟩:=F.correct a (.cons (TreeTyped.encode a) s)
  have next (b : Option B) : ∃ q,
      OnlineRetryPrefix.At M out (some .decode)
        (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) q ∧
      (∀ g : Option B → ℚ,q.mean g=(b.elim rest (fun b => .done (some b))).mean g) ∧
      q.cost ≤ rest.cost+6*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+27 := by
    cases b with
    | none =>
      obtain ⟨v,hv,hvm,hvc⟩:=OnlineRetryPrefix.deterministicCall M out .retry .prepare
        retryProc rfl _ _ _ (retry_exec (TreeTyped.encode a) (TreeTyped.encode (default : B)) s) rest hrest
      have ht:=OnlineRetryPrefix.nilBranch M out .test .retry .finish 1 rfl
        (env (TreeTyped.encode (default : B)) (bit false) (.cons (TreeTyped.encode a) s)) rfl v hv
      obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .decode .test
        (split 1 0 (by decide)) rfl _ _ _
        (split10 (bit false) (TreeTyped.encode (default : B)) .nil (.cons (TreeTyped.encode a) s))
        (.delay 1 v) ht
      refine ⟨q,hq,?_,?_⟩
      · intro g
        exact (hqm g).trans (hvm g)
      · simp only [Experiment.cost,bit,Bool.false_eq_true,ite_false,size_nil] at hqc
        omega
    | some b =>
      have hh:=OnlineRetryPrefix.halt M out .halt rfl (some b) rfl
      obtain ⟨v,hv,hvm,hvc⟩:=OnlineRetryPrefix.deterministicCall M out .finish .halt
        finishProc rfl _ _ _ (finish_exec (TreeTyped.encode a) (TreeTyped.encode b) s)
        (.delay 1 (.done (some b))) hh
      have ht:=OnlineRetryPrefix.consBranch M out .test .retry .finish 1 rfl
        (env (TreeTyped.encode b) (bit true) (.cons (TreeTyped.encode a) s)) .nil .nil rfl v hv
      obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .decode .test
        (split 1 0 (by decide)) rfl _ _ _
        (split10 (bit true) (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) (.delay 1 v) ht
      refine ⟨q,hq,?_,?_⟩
      · intro g
        exact (hqm g).trans (hvm g)
      · simp only [Experiment.cost,bit,ite_true, if_true,size_cons,size_nil] at hqc hvc
        omega
  choose v hv hvm hvc using next
  have ht:=OnlineRetryPrefix.call M out .trial .decode F.program rfl
    (env (TreeTyped.encode a) .nil (.cons (TreeTyped.encode a) s))
    (fun b => env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) u hu v hv
  obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .prepare .trial
    prepareProc rfl _ _ _ (prepare_exec (TreeTyped.encode a) s) (.delay 1 (u.bind v)) ht
  refine ⟨q,hq,?_,?_⟩
  · intro g
    rw [hqm,Experiment.mean,Experiment.mean_bind]
    simp_rw [hvm]
    rw [Experiment.mean_bind]
    exact hum _
  · have hb:=Experiment.cost_bind_le u v
      (rest.cost+6*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+27) hvc
    simp only [Experiment.cost] at hqc
    unfold stepCost
    omega

/-- All finite prefix laws belong to the same fixed looping program.
Failure leaves the original input at the live retry entry. -/
theorem prefix_correct (a : A) (s : Data) (N : ℕ) :
    ∃ q,OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) q ∧
      (∀ g : Option B → ℚ,q.mean g=(prefixExperiment (f := f) a N).mean g) ∧
      q.cost ≤ N*stepCost F a := by
  induction N with
  | zero => exact ⟨.done none,.done none,fun _ => rfl,by simp [Experiment.cost]⟩
  | succ N ih =>
    obtain ⟨p,hp,hpm,hpc⟩:=ih
    obtain ⟨q,hq,hqm,hqc⟩:=prefix_step F a s p hp
    refine ⟨q,hq,?_,?_⟩
    · intro g
      rw [hqm,prefixExperiment,Experiment.mean_bind,Experiment.mean_bind]
      congr 1
      funext b
      cases b <;> simp only [Option.elim_none,Option.elim_some,hpm]
    · rw [Nat.succ_mul]
      omega

end ContingencyTables.OnlineIntegerRetry

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlinePartialCall
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Calling the actual retry loop without pretending it has halted -/

namespace ContingencyTables.OnlinePartialCall
open MatchingFPRAS MatchingFPRAS.TreeData
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.OnlineStack MatchingFPRAS.OnlineControl
open MatchingFPRAS.PhysicalStream Turing

variable {R Λ α : Type} [DecidableEq R]

/-- A finite prefix of a called procedure can end at a live internal label.
Only actual halts return to the continuation label. -/
theorem partial_call (M : Λ → Instr R Λ) (l : Λ)
    (hcall : ∃ P next, M l = .call P next) (E : Env R)
    (out : α → TM2.Cfg (fun _ : K R => Bool) (procedure (M l)).Label RegisterProc.Store)
    (p : Experiment α)
    (hp : Executes (procedure (M l)).code (procedure (M l)).coin out
      ⟨some default,none,encodeEnv E⟩ p) :
    Executes (code M) (coins M) (fun a => callCfg M l (out a))
      (OnlineControl.cfg M (some l) E) (.delay 1 p) := by
  have hh := hp.relabel (code M) (coins M) (embed M l)
    ((successor (M l)).map Sum.inl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨P,next,h⟩ := hcall
  apply Executes.step _ _ _ _ rfl
  simpa only [OnlineControl.cfg,code,h,TM2.stepAux,callCfg,StackComposition.mapCfg_some,embed] using hh

lemma halt (M : Λ → Instr R Λ) (out : α → Config M)
    (l : Λ) (h : M l=.halt) (a : α) (E : Env R) (ha : out a=OnlineControl.cfg M none E) :
    At M out (some l) E (.delay 1 (.done a)) := by
  apply Executes.step _ _ _ _ rfl
  simp only [code,h,TM2.stepAux]
  change Executes (code M) (coins M) out (OnlineControl.cfg M none E) (.done a)
  rw [←ha]
  exact .done a

lemma nilBranch (M : Λ → Instr R Λ) (out : α → Config M)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (hi : E i=.nil) (p : Experiment α)
    (hp : At M out (some a) E p) : At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_false,OnlineControl.cfg,Option.map_some] using hp

lemma consBranch (M : Λ → Instr R Λ) (out : α → Config M)
    (l a b : Λ) (i : R) (h : M l=.branch i a b)
    (E : Env R) (x y : Data) (hi : E i=.cons x y) (p : Experiment α)
    (hp : At M out (some b) E p) : At M out (some l) E (.delay 1 p) := by
  apply Executes.step _ _ _ _ rfl
  simpa only [At,code,h,TM2.stepAux,encodeEnv,hi,encode,List.head?_cons,
    Option.getD_some,Bool.cond_true,OnlineControl.cfg,Option.map_some] using hp

lemma call {β : Type} (M : Λ → Instr R Λ) (out : α → Config M)
    (l next : Λ) (P : OnlineProc.Proc (K R)) (h : M l=.call P next)
    (E : Env R) (F : β → Env R) (q : Experiment β)
    (hq : Executes P.code P.coin (fun b => ⟨none,none,encodeEnv (F b)⟩)
      ⟨some default,none,encodeEnv E⟩ q)
    (p : β → Experiment α) (hp : ∀ b,At M out (some next) (F b) (p b)) :
    At M out (some l) E (.delay 1 (q.bind p)) := by
  have hq' : Executes (procedure (M l)).code (procedure (M l)).coin
      (fun b => ⟨none,none,encodeEnv (F b)⟩) ⟨some default,none,encodeEnv E⟩ q := by
    rw [show procedure (M l)=P by rw [h]; rfl]
    exact hq
  have hh:=hq'.relabel (code M) (coins M) (fun u => Sum.inr ⟨l,u⟩)
    ((successor (M l)).map Sum.inl) (fun _ => rfl) (fun _ => rfl)
  apply Executes.step _ _ _ _ rfl
  have hb:=hh.bind p out (fun b => by
    simpa only [At,OnlineControl.cfg,StackComposition.mapCfg_none,h,successor,Option.map_some] using hp b)
  simpa only [code,h,TM2.stepAux,StackComposition.mapCfg_some] using hb

lemma deterministicCall (M : Λ → Instr R Λ) (out : α → Config M)
    (l next : Λ) (P : RegisterProc.Proc (K R))
    (h : M l=.call (OnlineProc.deterministic P) next)
    (E F : Env R) (n : ℕ) (he : RegisterProc.Exec P (encodeEnv E) (encodeEnv F) n)
    (p : Experiment α) (hp : At M out (some next) F p) :
    ∃ q,At M out (some l) E q ∧ (∀ f : α → ℚ,q.mean f=p.mean f) ∧
      q.cost ≤ n+1+p.cost := by
  obtain ⟨k,hk,he⟩:=he
  obtain ⟨r,hr,hm,hc⟩:=Executes.of_run P.code k _ _ _ he
  refine ⟨.delay 1 (r.bind (fun _ => p)),
    call M out l next (OnlineProc.deterministic P) h E (fun _ : Unit => F)
      r hr (fun _ => p) (fun _ => hp),?_,?_⟩
  · intro f
    simpa only [Experiment.mean,Experiment.mean_bind] using hm (fun _ => p.mean f)
  · have hh:=Experiment.cost_bind_le r (fun _ => p) p.cost (fun _ => le_rfl)
    simp only [Experiment.cost]
    omega

end ContingencyTables.OnlinePartialCall

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The greedy initializer on the public binary tape -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS Turing
open scoped BigOperators

private lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

lemma encodeMargins_nonzero {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    ∀ a∈Algorithms.encodeMargins r c,a≠0 := by
  rw [encodeMargins_natWords]
  intro a ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  exact encodeNat_nonzero n a ha

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_StateSuccessEntries
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The successful state-to-table map removes precisely the large padding -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma originalStateSuccessEquiv_symm_entry (r : I → ℕ) (c : J → ℕ)
    (a : SuccessfulStateJoint r c) (i : I) (j : J) :
    ((originalStateSuccessEquiv r c).symm a).val i j=
      a.val.2.val.val.1 i j-
        largePadding (paperLarge r c) ((dimensionAllowance (I := I) (J := J))^12) i j := by
  change (unpadSuccessfulJoint r c ((successStateEquiv r c).symm a)).val i j=_
  rw [unpadSuccessfulJoint_val]
  apply congrArg (fun t : ℕ => t-_)
  exact congrArg (fun t => t.val.1 i j)
    (balancedJointFromState_projection r c a.val a.property.1)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileEntries
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial profile is read directly from the original table -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma tableState_first (X : Table r c) (i : Fin m) (j : Fin n)
    (hs : paperSmall r c i j=true) :
    physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X)
      (⟨(i,j),hs⟩,false)=X.val i j := by
  let a := originalStateSuccessEquiv r c X
  have he := originalStateSuccessEquiv_symm_entry r c a i j
  rw [Equiv.symm_apply_apply] at he
  have hp : largePadding (paperLarge r c) (d^12) i j=0 := by
    simp only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,hs,
      Bool.true_eq_false,ite_false]
  rw [hp,Nat.sub_zero] at he
  exact (a.val.2.property.2.2.1 i j hs).1.symm.trans he.symm

lemma tableState_second (X : Table r c) (a : Cells (paperSmall r c)) :
    physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X)
      (a,true)=d^20-X.val a.val.1 a.val.2 := by
  have hb := (originalStateSuccessEquiv r c X).property.1
  have hsum := (balanced_iff_cellSums (paperSmall r c) (stateCapacity r c)
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X))
    (fun a => (physicalProfile_feasible r c (tableState r c X)).bounded (a,true))).mp hb a
  have he := tableState_first r c X a.val.1 a.val.2 a.property
  have hcap := stateCapacity_small r c a.val.1 a.val.2 a.property
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells (paperSmall r c))=a :=
    Subtype.ext (Prod.eta a.val)
  rw [heta] at he
  rw [he,hcap] at hsum
  omega

lemma tableState_code (e : Fin q ≃ Cells (paperSmall r c)) (X : Table r c) :
    stateCode r c e (tableState r c X)=
      (List.ofFn (fun i => X.val (e i).val.1 (e i).val.2),
        List.ofFn (fun i => d^20-X.val (e i).val.1 (e i).val.2)) := by
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact tableState_first r c X _ _ (e i).property
  · apply congrArg List.ofFn
    funext i
    exact tableState_second r c X (e i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the initial profile directly from the greedy table -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts SmallContextCoordinates FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma originalViews_code (e : Fin q ≃ Cells (paperSmall r c)) (X : Table r c) :
    originalViews ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      stateCode r c e (tableState r c X) := by
  rw [tableState_code]
  have he : originalFirstView ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      List.ofFn (fun i => X.val (e i).val.1 (e i).val.2) := by
    simp only [originalFirstView,cellCatalog,List.map_ofFn]
    congr 1
    funext i
    exact matrixEntry_code X.val (e i).val.1 (e i).val.2
  unfold originalViews
  rw [he,complementValues_ofFn]

lemma initialViews_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialViews (List.ofFn r,List.ofFn c)=stateCode r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialViews initialViewInput
  rw [GreedyFeasibleTable.listMatrix_ofFn]
  have hc : marginCatalog (List.ofFn r,List.ofFn c)=cellCatalog (paperSmall r c) (computedCellEquiv r c) := by
    rw [computedCellEquiv_catalog]
    unfold marginCatalog
    rw [marginThreshold_ofFn]
    rfl
  rw [hc,marginThreshold_ofFn]
  exact originalViews_code r c (computedCellEquiv r c) (GreedyFeasibleTable.table r c htotal)

lemma initialCheck_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialCheck (List.ofFn r,List.ofFn c)=stateCodeData r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialCheck
  rw [initialViews_code r c htotal,prepareProfileInput_eq]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedResidualProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing padded residual margins from the stored small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

open scoped BigOperators

lemma largeCount_ofFn {n : ℕ} (U : ℕ) (r : Fin n → ℕ) :
    largeCount (U,List.ofFn r)=∑ i,if U ≤ r i then 1 else 0 := by
  simp only [largeCount,List.map_ofFn,List.sum_ofFn,Function.comp_apply,largeFlag]

lemma paddedMarginAt_eq (row : Bool) (z : PaddingData) (i : ℕ) :
    paddedMarginAt row (z,i)=
      (marginList row z.1).getD i 0-lineSum row (lineArgument row (z.1,i))+
        (if z.1.2≤(marginList row z.1).getD i 0
          then largeCount (z.1.2,marginList (!row) z.1)*z.2 else 0) := by
  unfold paddedMarginAt largeFlag
  dsimp only
  split_ifs <;> simp only [one_mul,zero_mul,add_zero]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma largePaddedMargins_eq (row : Bool) (z : PaddingData) :
    largePaddedMargins row z=
      (largeIndices (z.1.2,marginList row z.1)).map (fun i => paddedMarginAt row (z,i)) := by
  change (largeIndices (z.1.2,marginList row z.1)).map
    (fun i => (paddedMargins row z).getD i 0)=_
  apply List.map_congr_left
  intro i hi
  have hi' := (mem_largeIndices _ _ _).mp hi
  rw [List.getD_eq_getElem (l := paddedMargins row z) (n := i) (d := 0)
    (by simpa only [paddedMargins,List.length_map,List.length_range] using hi'.1)]
  simp only [paddedMargins,List.getElem_map,List.getElem_range]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedResidualSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The residual program computes the literal padded margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PaddedCompletions SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

lemma rowLargeCount_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) (i : Fin m) :
    rowLargeCount (firstPaperSmall r c U) i=
      if U ≤ r i then largeCount (U,List.ofFn c) else 0 := by
  rw [largeCount_ofFn]
  unfold rowLargeCount
  have he (j : Fin n) : (if firstPaperSmall r c U i j then 0 else 1)=
      if U ≤ r i then (if U ≤ c j then 1 else 0) else 0 := by
    simp only [firstPaperSmall,decide_eq_true_eq]
    split_ifs <;> omega
  simp_rw [he]
  split_ifs <;> simp

lemma columnLargeCount_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) (j : Fin n) :
    columnLargeCount (firstPaperSmall r c U) j=
      if U ≤ c j then largeCount (U,List.ofFn r) else 0 := by
  rw [largeCount_ofFn]
  unfold columnLargeCount
  have he (i : Fin m) : (if firstPaperSmall r c U i j then 0 else 1)=
      if U ≤ c j then (if U ≤ r i then 1 else 0) else 0 := by
    simp only [firstPaperSmall,decide_eq_true_eq]
    split_ifs <;> omega
  simp_rw [he]
  split_ifs <;> simp

theorem paddedRowAt_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : SmallProfile (firstPaperSmall r c U)) (i : Fin m) :
    paddedMarginAt true
      (((((cellCatalog (firstPaperSmall r c U) e,viewList (firstPaperSmall r c U) e z false),
        (List.ofFn r,List.ofFn c)),U),L),i.val)=
      r i-smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false) i+
        rowLargeCount (firstPaperSmall r c U) i*L := by
  rw [paddedMarginAt_eq]
  simp only [marginList,ite_true, if_true,Bool.not_true,Bool.false_eq_true,ite_false,lineArgument,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta]
  rw [storedRowSum_eq,rowLargeCount_code]
  split_ifs <;> simp only [zero_mul]

theorem paddedColumnAt_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (B : Fin m → Fin n → ℕ) (hB : ∀ a : Cells (firstPaperSmall r c U),B a.val.1 a.val.2=U)
    (z : SmallProfile (firstPaperSmall r c U)) (j : Fin n) :
    paddedMarginAt false
      (((((cellCatalog (firstPaperSmall r c U) e,complementValues (U,viewList (firstPaperSmall r c U) e z true)),
        (List.ofFn r,List.ofFn c)),U),L),j.val)=
      c j-smallColumn (firstPaperSmall r c U) B (smallView (firstPaperSmall r c U) z true) j+
        columnLargeCount (firstPaperSmall r c U) j*L := by
  rw [paddedMarginAt_eq]
  simp only [marginList,ite_true, if_true,Bool.not_false,Bool.false_eq_true,ite_false,lineArgument,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some,Fin.eta]
  rw [complementedColumnSum_eq _ _ B _ U hB,columnLargeCount_code]
  split_ifs <;> simp only [zero_mul]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact indexing of the computed large residual margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PaddedCompletions SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

lemma largeIndexEquiv_val (r : Fin m → ℕ) (U : ℕ)
    (i : Fin (largeIndices (U,List.ofFn r)).length) :
    (largeIndexEquiv r U i).val.val=(largeIndices (U,List.ofFn r))[i.val] := rfl

lemma largePaddedMargins_ofFn (row : Bool) (z : PaddingData) :
    largePaddedMargins row z=List.ofFn
      (fun i : Fin (largeIndices (z.1.2,marginList row z.1)).length =>
        paddedMarginAt row (z,(largeIndices (z.1.2,marginList row z.1))[i.val])) := by
  rw [largePaddedMargins_eq]
  exact (List.ofFn_getElem_eq_map _ _).symm

theorem largePaddedRows_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : SmallProfile (firstPaperSmall r c U)) :
    largePaddedMargins true
      (((((cellCatalog (firstPaperSmall r c U) e,viewList (firstPaperSmall r c U) e z false),
        (List.ofFn r,List.ofFn c)),U),L))=
      List.ofFn (fun i : Fin (largeIndices (U,List.ofFn r)).length =>
        r (largeIndexEquiv r U i).val-
          smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false)
            (largeIndexEquiv r U i).val+
          rowLargeCount (firstPaperSmall r c U) (largeIndexEquiv r U i).val*L) := by
  rw [largePaddedMargins_ofFn]
  apply congrArg List.ofFn
  funext i
  exact paddedRowAt_code r c U L e z (largeIndexEquiv r U i).val

theorem largePaddedColumns_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (B : Fin m → Fin n → ℕ) (hB : ∀ a : Cells (firstPaperSmall r c U),B a.val.1 a.val.2=U)
    (z : SmallProfile (firstPaperSmall r c U)) :
    largePaddedMargins false
      (((((cellCatalog (firstPaperSmall r c U) e,
        complementValues (U,viewList (firstPaperSmall r c U) e z true)),
        (List.ofFn r,List.ofFn c)),U),L))=
      List.ofFn (fun j : Fin (largeIndices (U,List.ofFn c)).length =>
        c (largeIndexEquiv c U j).val-
          smallColumn (firstPaperSmall r c U) B (smallView (firstPaperSmall r c U) z true)
            (largeIndexEquiv c U j).val+
          columnLargeCount (firstPaperSmall r c U) (largeIndexEquiv c U j).val*L) := by
  rw [largePaddedMargins_ofFn]
  apply congrArg List.ofFn
  funext j
  exact paddedColumnAt_code r c U L e B hB z (largeIndexEquiv c U j).val

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginReference
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed reference coordinates for the large completion rectangle -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles PaddedCompletions CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

lemma optionIndex_marginCode (k : ℕ) (hk : 0 < k) (f : Fin k → ℕ) :
    marginCode (fun i => f (optionIndexEquiv k hk i))=List.ofFn f := by
  cases k with
  | zero => omega
  | succ k =>
    rw [marginCode_ofFn]
    apply congrArg List.ofFn
    funext i
    exact congrArg f ((finSuccEquiv k).symm_apply_apply i)

lemma largeOption_marginCode (r : Fin m → ℕ) (U : ℕ)
    (hr : 0 < (largeIndices (U,List.ofFn r)).length) (f : LargeRows r U → ℕ) :
    marginCode (fun i => f (largeOptionEquiv r U hr i))=
      List.ofFn (fun i => f (largeIndexEquiv r U i)) :=
  optionIndex_marginCode _ hr (fun i => f (largeIndexEquiv r U i))

theorem listedRows_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (B : Fin m → Fin n → ℕ) (hr : 0 < (largeIndices (U,List.ofFn r)).length)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    marginCode (listedRows r c U L B hr z)=largePaddedMargins true
      (((((cellCatalog (firstPaperSmall r c U) e,
        viewList (firstPaperSmall r c U) e (physicalProfile _ B r c L z) false),
        (List.ofFn r,List.ofFn c)),U),L)) := by
  unfold listedRows
  rw [largeOption_marginCode r U hr
    (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val),
    largePaddedRows_code]
  rfl

theorem listedColumns_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (B : Fin m → Fin n → ℕ) (hc : 0 < (largeIndices (U,List.ofFn c)).length)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (hB : ∀ a : Cells (firstPaperSmall r c U),B a.val.1 a.val.2=U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    marginCode (listedColumns r c U L B hc z)=largePaddedMargins false
      (((((cellCatalog (firstPaperSmall r c U) e,
        complementValues (U,viewList (firstPaperSmall r c U) e (physicalProfile _ B r c L z) true)),
        (List.ofFn r,List.ofFn c)),U),L)) := by
  unfold listedColumns
  rw [largeOption_marginCode c U hc
    (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val),
    largePaddedColumns_code r c U L e B hB]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedDenseProgramSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary residual call implements the actual completion draw -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates FirstPaperProfiles CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (e : Fin q ≃ Cells (paperSmall r c))

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

theorem residualParameters_code (h : ℕ) (z : PaperStates r c) :
    residualParameters ((stateCodeData r c e z,d^12),(d,h))=
      ((marginCode (R z),marginCode (P z)),(d,h)) := by
  apply Prod.ext
  · apply Prod.ext
    · exact (listedRows_code r c (d^20) (d^12) (stateCapacity r c) hr e z).symm
    · exact (listedColumns_code r c (d^20) (d^12) (stateCapacity r c) hc e
        (fun a => stateCapacity_small r c _ _ a.property) z).symm
  · rfl

/-- On every word, the polynomial binary call returns precisely the
matrix of a genuine completion, in the computed large-rectangle order. -/
theorem residualDenseDraw_code (h : ℕ) (z : PaperStates r c)
    (bits : Fin (listedDrawBits r c hr hc h z) → Bool) :
    residualDenseDraw (((stateCodeData r c e z,d^12),(d,h)),List.ofFn bits)=
      tableOutput (paperListedEquiv r c hr hc z (listedDenseDraw r c hr hc h z bits)) := by
  unfold residualDenseDraw
  rw [residualParameters_code]
  have he := canonicalDenseDraw_eq (R z) (P z) (listed_dimension_fourteen r c hr hc)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc z)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc z)
    (listed_paper_totals r c hr hc z) h bits
  refine he.trans ?_
  simp only [listedDenseDraw,Equiv.apply_symm_apply]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedReservedDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed word for all computed residual completion draws -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

theorem listedPaddedDraw_code (e : Fin q ≃ Cells (paperSmall r c))
    (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) (bits : Fin (25*(d+b+h+1)^62) → Bool) :
    reservedResidualDraw (((stateCodeData r c e z,d^12),(d,h)),List.ofFn bits)=
      tableOutput (paperListedEquiv r c hr hc z (listedPaddedDraw r c hr hc b h hb z bits)) := by
  have he := residualDenseDraw_code r c hr hc e h z
    (prefixWord (listedDrawBits_le r c hr hc b h hb z) bits)
  unfold residualDenseDraw at he
  rw [residualParameters_code r c hr hc e] at he
  unfold reservedResidualDraw reservedCanonicalDraw
  rw [residualParameters_code r c hr hc e]
  rw [canonicalBitCount_code (R z) (P z)
    (by have := listed_dimension_fourteen r c hr hc; omega) (listed_paper_totals r c hr hc z),
    take_ofFn_prefix (listedDrawBits_le r c hr hc b h hb z)]
  dsimp only [listedPaddedDraw]
  exact he

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TranslationDecisionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms CompletionTranslation
open scoped BigOperators

lemma starParts_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    ((starParts ((marginCode R,marginCode P),(optionIndex i,optionIndex j))).1:ℤ)-
      (starParts ((marginCode R,marginCode P),(optionIndex i,optionIndex j))).2=
      CompletionTranslation.star (fun i => (R i:ℤ)) (fun j => (P j:ℤ)) i j := by
  cases i <;> cases j <;>
    simp [starParts,completionParts,optionIndex,marginCode,List.sum_ofFn,
      matrixTotal,rowTotal,columnTotal,matrixEntry,CompletionTranslation.star]

lemma translationParts_code {m n : ℕ}
    (R₀ R₁ : Option (Fin m) → ℕ) (P₀ P₁ : Option (Fin n) → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    let p := translationParts (((marginCode R₀,marginCode P₀),(marginCode R₁,marginCode P₁)),
      (optionIndex i,optionIndex j))
    (p.1:ℤ)-p.2=between R₀ R₁ P₀ P₁ i j := by
  have h₀ := starParts_code R₀ P₀ i j
  have h₁ := starParts_code R₁ P₁ i j
  dsimp only [translationParts]
  simp only [Nat.cast_add]
  rw [show between R₀ R₁ P₀ P₁ i j=
    CompletionTranslation.star (fun i => (R₁ i:ℤ)) (fun j => (P₁ j:ℤ)) i j-
    CompletionTranslation.star (fun i => (R₀ i:ℤ)) (fun j => (P₀ j:ℤ)) i j by
      cases i <;> cases j <;> simp only [between,CompletionTranslation.star,Finset.sum_sub_distrib] <;> omega]
  omega

lemma tableOutput_entry {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (X : Table R P) (i : Option (Fin m)) (j : Option (Fin n)) :
    matrixEntry (tableOutput X,(optionIndex i,optionIndex j))=X.val i j := by
  have hi : optionIndex i=((finSuccEquiv m).symm i).val := by
    cases i <;> simp only [optionIndex,finSuccEquiv_symm_none,finSuccEquiv_symm_some,
      Fin.val_zero,Fin.val_succ]
  have hj : optionIndex j=((finSuccEquiv n).symm j).val := by
    cases j <;> simp only [optionIndex,finSuccEquiv_symm_none,finSuccEquiv_symm_some,
      Fin.val_zero,Fin.val_succ]
  rw [hi,hj]
  unfold tableOutput
  rw [matrixEntry_code]
  simp only [Equiv.apply_symm_apply]

/-- Each binary comparison is the literal translated nonnegativity
condition in the Markov-chain acceptance decision. -/
theorem translatedCell_code {m n : ℕ}
    (R₀ R₁ : Option (Fin m) → ℕ) (P₀ P₁ : Option (Fin n) → ℕ)
    (X : Table R₀ P₀) (i : Option (Fin m)) (j : Option (Fin n)) :
    translatedCell ((((marginCode R₀,marginCode P₀),(marginCode R₁,marginCode P₁)),
      tableOutput X),(optionIndex i,optionIndex j))=true ↔
      0 ≤ (X.val i j:ℤ)+between R₀ R₁ P₀ P₁ i j := by
  have hp := translationParts_code R₀ R₁ P₀ P₁ i j
  dsimp only at hp
  simp only [translatedCell,decide_eq_true_eq,tableOutput_entry]
  omega

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TranslationDecisionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the full translated-nonnegativity test -/

namespace ContingencyTables.DensePrograms
open ProfilePrograms CompletionTranslation
open scoped BigOperators

theorem translationValid_code {m n : ℕ}
    (R₀ R₁ : Option (Fin m) → ℕ) (P₀ P₁ : Option (Fin n) → ℕ)
    (X : Table R₀ P₀) :
    translationValid (((marginCode R₀,marginCode P₀),(marginCode R₁,marginCode P₁)),
      tableOutput X)=true ↔
      ∀ i j,0 ≤ (X.val i j:ℤ)+between R₀ R₁ P₀ P₁ i j := by
  rw [translationValid,List.all_eq_true]
  constructor
  · intro h i j
    apply (translatedCell_code R₀ R₁ P₀ P₁ X i j).mp
    apply h (optionIndex i,optionIndex j)
    apply (mem_cellPairs _ _ _ _).mpr
    simpa only [marginCode,List.length_cons,List.length_ofFn] using
      And.intro (optionIndex_lt i) (optionIndex_lt j)
  · intro h a ha
    have hab := (mem_cellPairs _ _ _ _).mp ha
    have hi : a.1 < m+1 := by
      simpa only [marginCode,List.length_cons,List.length_ofFn] using hab.1
    have hj : a.2 < n+1 := by
      simpa only [marginCode,List.length_cons,List.length_ofFn] using hab.2
    have he := (translatedCell_code R₀ R₁ P₀ P₁ X
      (finSuccEquiv m ⟨a.1,hi⟩) (finSuccEquiv n ⟨a.2,hj⟩)).mpr (h _ _)
    simpa only [optionIndex_finSucc] using he

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma capView_eq (q U : ℕ) (xs : List ℕ) (hq : xs.length=q)
    (hU : ∀ a∈xs,a≤U) : capView ((q,U),xs)=xs := by
  unfold capView
  rw [←hq,List.take_length]
  calc
    xs.map (fun a => min a U)=xs.map id := List.map_congr_left (fun a ha => min_eq_left (hU a ha))
    _ = xs := List.map_id xs

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

open FairBits GridBoundary
open scoped Classical
noncomputable section

lemma splitProfileWord_ofFn {s f : ℕ} (bits : Fin (s+f) → Bool) :
    splitProfileWord (s,List.ofFn bits)=
      (List.ofFn (splitWordEquiv s f bits).1,List.ofFn (splitWordEquiv s f bits).2) :=
  Prod.ext (ofFn_split_take bits) (ofFn_split_drop bits)

lemma profileWalkWords_ofFn {n s f : ℕ} (hw : 0 < s+f)
    (bits : Fin (n*(s+f)+f) → Bool) :
    profileWalkWords (((n,s),f),List.ofFn bits)=List.ofFn (fun i : Fin n =>
      let word := gridWordEquiv n (s+f) (splitWordEquiv (n*(s+f)) f bits).1 i
      (List.ofFn (splitWordEquiv s f word).1,List.ofFn (splitWordEquiv s f word).2)) := by
  unfold profileWalkWords profileWalkChunks
  dsimp only [profileWordWidth,profileWalkWidth]
  rw [ofFn_split_take,wordChunks_ofFn hw,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact splitProfileWord_ofFn _

lemma profileTerminalWord_ofFn {n s f : ℕ} (bits : Fin (n*(s+f)+f) → Bool) :
    profileTerminalWord (((n,s),f),List.ofFn bits)=
      List.ofFn (splitWordEquiv (n*(s+f)) f bits).2 := ofFn_split_drop bits

end
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the binary outer transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical

noncomputable section

private lemma apply_decision {X Y : Type*} (encode : X → Y) (x y : X)
    (test : Bool) (accept : Prop) [Decidable accept] (h : test=true ↔ accept) :
    (if test then encode y else encode x)=encode (if accept then y else x) := by
  by_cases hp : accept
  · rw [ite_eq_left hp,ite_eq_left (h.mpr hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun ht => hp (h.mp ht))]

private lemma completionDecision_some_formula {X I J : Type*} [Fintype I] [Fintype J]
    (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) (A : Table (R x) (P x)) :
    completionDecision R P x (some y) A=
      if ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j then y else x := rfl

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))

theorem codeProposal_encoded (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (bits : Fin (smallProposalBits (I := Fin m) (J := Fin n)) → Bool) :
    codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)=
      (decodedCodeProposal r c e x bits).map (stateCode r c e) := by
  cases hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn bits) with
  | none => simp only [decodedCodeProposal,hp,Option.bind_none,Option.map_none]
  | some v =>
    have hv : v∈codeNeighbors (stateCodeData r c e x) := List.mem_of_getElem? hp
    obtain ⟨y,hy⟩ := codeNeighbors_decode_total r c e htotal x v hv
    have he := (decodeStateCode_eq_some_iff r c e v y).mp hy
    simp only [decodedCodeProposal,hp,Option.bind_some,hy,Option.map_some,he]

variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

lemma stepCandidate_encoded (x y : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool)
    (hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn proposal)=some (stateCode r c e y)) :
    stepCandidateParameters (encodedStepInput r c e b h x proposal completion)=
      ((stateCodeData r c e y,d^12),(d,h)) := by
  simp only [stepCandidateParameters,stepCandidate,stepCandidateViews,stepProposal,encodedStepInput,hp,
    Option.getD_some]
  rfl

lemma stepTranslation_encoded (x y : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool)
    (hp : codeNeighborProposal (stateCodeData r c e x,List.ofFn proposal)=some (stateCode r c e y)) :
    stepTranslation (encodedStepInput r c e b h x proposal completion)=
      (((marginCode (R x),marginCode (P x)),(marginCode (R y),marginCode (P y))),
        tableOutput (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))) := by
  unfold stepTranslation stepOldMargins stepNewMargins stepCompletion
  rw [stepCandidate_encoded r c e b h x y proposal completion hp]
  dsimp only [encodedStepInput]
  rw [residualParameters_code, residualParameters_code,listedPaddedDraw_code]

theorem profileStep_encoded (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (proposal : Fin s → Bool) (completion : Fin f → Bool) :
    profileStep (encodedStepInput r c e b h x proposal completion)=
      stateCode r c e (completionDecision R P x (decodedCodeProposal r c e x proposal)
        (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))) := by
  have hp := codeProposal_encoded r c e htotal x proposal
  cases hd : decodedCodeProposal r c e x proposal with
  | none =>
    rw [hd,Option.map_none] at hp
    unfold profileStep
    have hcand : stepCandidateViews (encodedStepInput r c e b h x proposal completion)=stateCode r c e x := by
      simp only [stepCandidateViews,stepProposal,encodedStepInput,hp,Option.getD_none]
      rfl
    rw [hcand]
    split_ifs <;> rfl
  | some y =>
    rw [hd,Option.map_some] at hp
    have ht := stepTranslation_encoded r c e hr hc b h hb x y proposal completion hp
    have hv := translationValid_code (R x) (R y) (P x) (P y)
      (paperListedEquiv r c hr hc x (listedPaddedDraw r c hr hc b h hb x completion))
    unfold profileStep
    rw [ht]
    have hcand : stepCandidateViews (encodedStepInput r c e b h x proposal completion)=stateCode r c e y := by
      simp only [stepCandidateViews,stepProposal,encodedStepInput,hp,Option.getD_some]
    rw [hcand]
    rw [completionDecision_some_formula]
    exact apply_decision (stateCode r c e) x y _ _ hv


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedBooleanStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed binary outer step has the proved mixing kernel -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open ResidualMixture FirstSuccess FairBits CompletionTranslation SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] FirstSuccess.mapLaw completionStepLaw

theorem profileStep_listedBitStep (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (bits : Fin (s+f) → Bool) :
    profileStep (encodedStepInput r c e b h x (splitWordEquiv s f bits).1 (splitWordEquiv s f bits).2)=
      stateCode r c e (listedBitStep r c e hr hc b h hb x bits) := by
  rw [profileStep_encoded r c e hr hc b h hb htotal]
  rw [listed_completionDecision r c hr hc]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded binary loop preserves the physical profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open SmallContextCoordinates FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma capViews_stateCode (x y : PaperStates r c) :
    capViews (stateCodeData r c e x,stateCode r c e y)=stateCode r c e y := by
  have hb (side : Bool) :
      capView ((q,d^20),viewList (paperSmall r c) e
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) y) side)=
      viewList (paperSmall r c) e
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) y) side := by
    apply capView_eq
    · simp only [viewList,List.length_ofFn]
    · intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact stateCode_bounded r c y (e i) side
  simpa only [capViews,stateCodeData,codeCheckData,cellCatalog,List.length_ofFn,stateCode,profileCode]
    using Prod.ext (hb false) (hb true)

variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

theorem advanceProfile_encoded (htotal : (∑ i,r i)=∑ j,c j)
    (initial x : PaperStates r c) (bits : Fin (s+f) → Bool) :
    advanceProfile ((List.ofFn (splitWordEquiv s f bits).1,List.ofFn (splitWordEquiv s f bits).2),
      encodedConfiguration r c e h initial x)=
      encodedConfiguration r c e h initial (listedBitStep r c e hr hc b h hb x bits) := by
  apply Prod.ext
  · rfl
  · change capViews (stateCodeData r c e initial,
      profileStep (encodedStepInput r c e b h x
        (splitWordEquiv s f bits).1 (splitWordEquiv s f bits).2))=_
    rw [profileStep_listedBitStep r c e hr hc b h hb htotal]
    exact capViews_stateCode r c e initial _

theorem profileWalk_ofFn (htotal : (∑ i,r i)=∑ j,c j)
    (initial x : PaperStates r c) (steps : ℕ) (bits : Fin steps → Fin (s+f) → Bool) :
    profileWalk (encodedConfiguration r c e h initial x,
      List.ofFn (fun i => (List.ofFn (splitWordEquiv s f (bits i)).1,
        List.ofFn (splitWordEquiv s f (bits i)).2)))=
      encodedConfiguration r c e h initial
        (wordWalk (listedBitStep r c e hr hc b h hb) x steps bits) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    unfold profileWalk at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change advanceProfile ((List.ofFn (splitWordEquiv s f (bits (Fin.last steps))).1,
      List.ofFn (splitWordEquiv s f (bits (Fin.last steps))).2),
      (List.ofFn (fun i => (List.ofFn (splitWordEquiv s f ((Fin.init bits) i)).1,
        List.ofFn (splitWordEquiv s f ((Fin.init bits) i)).2))).foldl
          (fun state word => advanceProfile (word,state))
          (encodedConfiguration r c e h initial x))=_
    rw [ih (Fin.init bits)]
    exact advanceProfile_encoded r c e hr hc b h hb htotal initial _ _

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterMatrixSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal entries and acceptance of the original-table output program -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma paddingTest_matrixCode {m n : ℕ} (L : ℕ) (X : Fin m → Fin n → ℕ) :
    paddingTest (L,matrixCode X)=true ↔ ∀ i j,L≤X i j := by
  simp only [paddingTest,matrixCode,List.all_eq_true]
  constructor
  · intro h i j
    exact of_decide_eq_true (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩) _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  · intro h row hrow a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact decide_eq_true (h i j)

lemma paddingTest_tableOutput {m n : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ) (L : ℕ) (X : Table R P) :
    paddingTest (L,tableOutput X)=true ↔ ∀ i j,L≤X.val i j := by
  rw [tableOutput,paddingTest_matrixCode]
  constructor
  · intro h i j
    simpa only [Equiv.apply_symm_apply] using
      h ((finSuccEquiv m).symm i) ((finSuccEquiv n).symm j)
  · intro h i j
    exact h _ _

private lemma map_range_ofFn {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

lemma outputMatrix_code {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (data : OuterTableData) :
    outputMatrix ((List.ofFn r,List.ofFn c),data)=
      matrixCode (fun i : Fin m => fun j : Fin n => outputEntry (data,(i.val,j.val))) := by
  simp only [outputMatrix,outputRows,outputColumns,outputShape,completionRows,completionColumns,
    outputRow,outputRowEntry,List.length_ofFn]
  rw [map_range_ofFn]
  apply congrArg List.ofFn
  funext i
  exact map_range_ofFn _ _

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open scoped Classical

noncomputable section
variable {m n q : ℕ}

lemma optionIndexEquiv_val (k : ℕ) (hk : 0<k) (i : Option (Fin (k-1))) :
    (optionIndexEquiv k hk i).val=optionIndex i := by
  cases k with
  | zero => omega
  | succ k =>
    change ((finSuccEquiv k).symm i).val=optionIndex i
    cases i <;> simp only [DensePrograms.finSuccEquiv_symm_none,
      _root_.finSuccEquiv_symm_some,optionIndex,Fin.val_zero,Fin.val_succ]

lemma largeOption_index (r : Fin m → ℕ) (U : ℕ)
    (hr : 0<(largeIndices (U,List.ofFn r)).length)
    (i : Option (Fin ((largeIndices (U,List.ofFn r)).length-1))) :
    (largeIndices (U,List.ofFn r)).idxOf (largeOptionEquiv r U hr i).val.val=optionIndex i := by
  change (largeIndices (U,List.ofFn r)).idxOf
    (largeIndexEquiv r U (optionIndexEquiv _ hr i)).val.val=_
  rw [largeIndexEquiv_val,(largeIndices_nodup U (List.ofFn r)).idxOf_getElem]
  exact optionIndexEquiv_val _ hr i

lemma outputEntry_small (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)
    (z : SmallProfile small) (rows columns : List ℕ) (U L : ℕ) (X : MatrixCode)
    (i : Fin m) (j : Fin n) (hs : small i j=true) :
    outputEntry ((((cellCatalog small e,profileCode small e z),(rows,columns)),((U,L),X)),
      (i.val,j.val))=smallView small z false i j := by
  have hm := (mem_cellCatalog small e (i,j)).mpr hs
  exact (ite_eq_left (List.idxOf_lt_length_iff.mpr hm)).trans (lookupView_eq small e z false i j)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ReferenceCompletionEntries
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal matrix entries of the completion coordinate equivalences -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open FirstPaperProfiles SmallContextCoordinates SmallContextFibres
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem referenceFibreEquiv_entry (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j)
    (A : CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z))
    (i : Option {i : LargeRows r U // i≠i₀}) (j : Option {j : LargeColumns c U // j≠j₀}) :
    (referenceFibreEquiv r c U L B i₀ j₀ z hcap A).val i j=
      A.val.val.1 ((Equiv.optionSubtypeNe i₀ i).val) ((Equiv.optionSubtypeNe j₀ j).val) := by
  change (fibreLargeEquiv (firstPaperSmall r c U) B r c L
    (physicalProfile _ B r c L z) (naturalProfile_bounded z.val.val)
    (physical_original_residuals _ B r c L z hcap) hcap A).val.val
      (Equiv.optionSubtypeNe i₀ i).val (Equiv.optionSubtypeNe j₀ j).val=_
  have he := fibreLargeEquiv_apply (firstPaperSmall r c U) B r c L
    (physicalProfile _ B r c L z) (naturalProfile_bounded z.val.val)
    (physical_original_residuals _ B r c L z hcap) hcap A
    (Equiv.optionSubtypeNe i₀ i).val (Equiv.optionSubtypeNe j₀ j).val
  have hs : firstPaperSmall r c U (Equiv.optionSubtypeNe i₀ i).val
      (Equiv.optionSubtypeNe j₀ j).val=false :=
    (firstPaperSmall_false_iff r c U _ _).mpr
      ⟨(Equiv.optionSubtypeNe i₀ i).property,(Equiv.optionSubtypeNe j₀ j).property⟩
  simpa only [hs,Bool.false_eq_true,ite_false,rectangleCompletionEquiv,rectangleRestrict] using he

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedOutputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable output entries for actual retained completion fibres -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstPaperProfiles PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] referenceFibreEquiv listedFibreEquiv
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "L" => d^12

lemma paperListedEquiv_entry (x : PaperStates r c) (A : PaperFibre r c x)
    (i : Option (Fin ((largeIndices (U,List.ofFn r)).length-1)))
    (j : Option (Fin ((largeIndices (U,List.ofFn c)).length-1))) :
    (paperListedEquiv r c hr hc x A).val i j=
      A.val.val.1 (largeOptionEquiv r U hr i).val (largeOptionEquiv c U hc j).val := by
  rw [listedFibreEquiv_entry,referenceFibreEquiv_entry]
  simp only [listedReferenceIndex,Equiv.trans_apply,Equiv.apply_symm_apply]

lemma listedPaddingTest (x : PaperStates r c) (A : PaperFibre r c x) :
    paddingTest (L,tableOutput (paperListedEquiv r c hr hc x A))=true ↔
      ∀ i j,paperSmall r c i j=false → L≤A.val.val.1 i j := by
  rw [paddingTest_tableOutput]
  simp_rw [paperListedEquiv_entry]
  constructor
  · intro h i j hij
    obtain ⟨hi,hj⟩ := (firstPaperSmall_false_iff r c U i j).mp hij
    obtain ⟨a,ha⟩ := (largeOptionEquiv r U hr).surjective ⟨i,hi⟩
    obtain ⟨b,hb⟩ := (largeOptionEquiv c U hc).surjective ⟨j,hj⟩
    simpa only [ha,hb] using h a b
  · intro h i j
    exact h _ _ ((firstPaperSmall_false_iff r c U _ _).mpr
      ⟨(largeOptionEquiv r U hr i).property,(largeOptionEquiv c U hc j).property⟩)

lemma actualOutputData_eq (x : PaperStates r c) (A : PaperFibre r c x) :
    actualOutputData r c e hr hc x A=
      (((cellCatalog (paperSmall r c) e,stateCode r c e x),
        (largeIndices (U,List.ofFn r),largeIndices (U,List.ofFn c))),
        ((U,L),tableOutput (paperListedEquiv r c hr hc x A))) := rfl

lemma actualOutputEntry_large (x : PaperStates r c) (A : PaperFibre r c x)
    (i : Option (Fin ((largeIndices (U,List.ofFn r)).length-1)))
    (j : Option (Fin ((largeIndices (U,List.ofFn c)).length-1))) :
    outputEntry (actualOutputData r c e hr hc x A,
      ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val))=
        A.val.val.1 (largeOptionEquiv r U hr i).val (largeOptionEquiv c U hc j).val-L := by
  have hs : paperSmall r c (largeOptionEquiv r U hr i).val (largeOptionEquiv c U hc j).val=false :=
    (firstPaperSmall_false_iff r c U _ _).mpr
      ⟨(largeOptionEquiv r U hr i).property,(largeOptionEquiv c U hc j).property⟩
  have hnot := (mem_cellCatalog (paperSmall r c) e
    ((largeOptionEquiv r U hr i).val,(largeOptionEquiv c U hc j).val)).not.mpr
      (by simp only [hs,Bool.false_eq_true,not_false_eq_true])
  have hpos := List.idxOf_eq_length hnot
  have hbad : ¬outputCellPosition (actualOutputData r c e hr hc x A,
      ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val))<
      (actualOutputData r c e hr hc x A).1.1.1.length := by
    change ¬(cellCatalog (paperSmall r c) e).idxOf
      ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val)<
      (cellCatalog (paperSmall r c) e).length
    rw [hpos]
    exact Nat.lt_irrefl _
  have hlarge : outputEntry (actualOutputData r c e hr hc x A,
      ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val))=
      outputLargeEntry (actualOutputData r c e hr hc x A,
        ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val)) := ite_eq_right hbad
  rw [hlarge]
  change _root_.OAI.ContingencyTables.DensePrograms.matrixEntry (tableOutput (paperListedEquiv r c hr hc x A),
    ((largeIndices (U,List.ofFn r)).idxOf (largeOptionEquiv r U hr i).val.val,
      (largeIndices (U,List.ofFn c)).idxOf (largeOptionEquiv c U hc j).val.val))-L=_
  rw [largeOption_index,largeOption_index,tableOutput_entry,paperListedEquiv_entry]

lemma actualOutputEntry_small (x : PaperStates r c) (A : PaperFibre r c x)
    (i : Fin m) (j : Fin n) (hs : paperSmall r c i j=true) :
    outputEntry (actualOutputData r c e hr hc x A,(i.val,j.val))=A.val.val.1 i j := by
  rw [actualOutputData_eq]
  have he := outputEntry_small (paperSmall r c) e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c L x)
    (largeIndices (U,List.ofFn r)) (largeIndices (U,List.ofFn c)) U L
    (tableOutput (paperListedEquiv r c hr hc x A)) i j hs
  exact he.trans (by
    simpa only [smallView,hs,dite_true] using (A.property.2.2.1 i j hs).1.symm)

lemma actualOutputEntry (x : PaperStates r c) (A : PaperFibre r c x)
    (i : Fin m) (j : Fin n) :
    outputEntry (actualOutputData r c e hr hc x A,(i.val,j.val))=
      A.val.val.1 i j-largePadding (paperLarge r c) L i j := by
  cases hs : paperSmall r c i j with
  | true =>
    simpa only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,hs,
      Bool.true_eq_false,ite_false,Nat.sub_zero] using
      actualOutputEntry_small r c e hr hc x A i j hs
  | false =>
    obtain ⟨hi,hj⟩ := (firstPaperSmall_false_iff r c U i j).mp hs
    obtain ⟨a,ha⟩ := (largeOptionEquiv r U hr).surjective ⟨i,hi⟩
    obtain ⟨b,hb⟩ := (largeOptionEquiv c U hc).surjective ⟨j,hj⟩
    simpa only [ha,hb,paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,
      hs,ite_true, if_true] using actualOutputEntry_large r c e hr hc x A a b

lemma balancedTest_stateCode (x : PaperStates r c) :
    balancedTest (stateCode r c e x,U)=true ↔
      Balanced (paperSmall r c) (stateCapacity r c)
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c L x) := by
  rw [stateCode,profileCode,viewList,viewList,balancedTest_ofFn,
    balanced_iff_cellSums (paperSmall r c) (stateCapacity r c) _
      (fun a => (physicalProfile_feasible r c x).bounded (a,true))]
  constructor
  · intro h a
    simpa only [Equiv.apply_symm_apply,stateCapacity_small r c _ _ a.property] using h (e.symm a)
  · intro h i
    simpa only [stateCapacity_small r c _ _ (e i).property] using h (e i)

lemma actualOutputSuccess (x : PaperStates r c) (A : PaperFibre r c x) :
    outerSuccess (actualOutputData r c e hr hc x A)=true ↔
      StateJointSuccess r c ⟨x,A⟩ := by
  rw [actualOutputData_eq]
  change (balancedTest (stateCode r c e x,U) &&
    paddingTest (L,tableOutput (paperListedEquiv r c hr hc x A)))=true ↔ _
  rw [Bool.and_eq_true,balancedTest_stateCode,listedPaddingTest]
  rfl

lemma actualOutputMatrix (a : SuccessfulStateJoint r c) :
    outputMatrix (prepareOutput ((stateCodeData r c e a.val.1,L),
      tableOutput (paperListedEquiv r c hr hc a.val.1 a.val.2)))=
        matrixCode ((originalStateSuccessEquiv r c).symm a).val := by
  change outputMatrix ((List.ofFn r,List.ofFn c),
    actualOutputData r c e hr hc a.val.1 a.val.2)=_
  rw [outputMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [actualOutputEntry,originalStateSuccessEquiv_symm_entry]

lemma actualOuterTrial (x : PaperStates r c) (A : PaperFibre r c x) :
    outerTrial ((stateCodeData r c e x,L),tableOutput (paperListedEquiv r c hr hc x A))=
      (stateTrial r c ⟨x,A⟩).map (fun T => matrixCode T.val) := by
  by_cases h : StateJointSuccess r c ⟨x,A⟩
  · have hp := (actualOutputSuccess r c e hr hc x A).mpr h
    calc
      _ = some (outputMatrix (prepareOutput ((stateCodeData r c e x,L),
          tableOutput (paperListedEquiv r c hr hc x A)))) := ite_eq_left hp
      _ = some (matrixCode ((originalStateSuccessEquiv r c).symm ⟨⟨x,A⟩,h⟩).val) :=
        congrArg some (actualOutputMatrix r c e hr hc ⟨⟨x,A⟩,h⟩)
      _ = _ := by
        simp only [stateTrial,FirstSuccess.partialEquivDraw,dite_eq_left h,Option.map_some]
  · have hp : outerSuccess (actualOutputData r c e hr hc x A)≠true :=
      fun hp => h ((actualOutputSuccess r c e hr hc x A).mp hp)
    calc
      _ = none := ite_eq_right hp
      _ = _ := by
        simp only [stateTrial,FirstSuccess.partialEquivDraw,dite_eq_right h,Option.map_none]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The polynomial outer trial implements the finite-word experiment -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstSuccess FairBits CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

lemma currentParameters_encoded (initial x : PaperStates r c) :
    currentParameters (encodedConfiguration r c e h initial x)=
      ((stateCodeData r c e x,d^12),(d,h)) := rfl

theorem profileTrial_ofFn (htotal : (∑ i,r i)=∑ j,c j)
    (initial x : PaperStates r c) (steps : ℕ)
    (bits : Fin steps → Fin (s+f) → Bool) (terminal : Fin f → Bool) :
    profileTrial ((encodedConfiguration r c e h initial x,
      List.ofFn (fun i => (List.ofFn (splitWordEquiv s f (bits i)).1,
        List.ofFn (splitWordEquiv s f (bits i)).2))),List.ofFn terminal)=
      (stateTrial r c ⟨wordWalk (listedBitStep r c e hr hc b h hb) x steps bits,
        listedPaddedDraw r c hr hc b h hb _ terminal⟩).map (fun T => matrixCode T.val) := by
  unfold profileTrial trialOutputInput ProfilePrograms.trialCompletion trialParameters trialState
  rw [profileWalk_ofFn r c e hr hc b h hb htotal,currentParameters_encoded]
  rw [listedPaddedDraw_code r c hr hc e b h hb]
  exact actualOuterTrial r c e hr hc _ _

theorem packedProfileTrial_code (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (steps : ℕ) (bits : Fin (steps*(s+f)+f) → Bool) :
    packedProfileTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn bits)=
      (stateTrial r c (listedJointDraw r c e hr hc b h hb x steps bits)).map
        (fun T => matrixCode T.val) := by
  have hf : 0<f := by positivity
  unfold packedProfileTrial prepareProfileTrial profileTrialWords
  rw [profileWalkWords_ofFn (by omega),profileTerminalWord_ofFn]
  exact profileTrial_ofFn r c e hr hc b h hb htotal x x steps _ _

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRetrySemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executable retry program realizes the proved outer distribution -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres CompletionCounts
open FirstSuccess FairBits SmallContextCoordinates FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

theorem profileRetry_code (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c)
    (steps attempts : ℕ) (fallback : Table r c)
    (bits : Fin (attempts*(steps*(s+f)+f)) → Bool) :
    profileRetry (((encodedConfiguration r c e h x x,((steps,s),f)),matrixCode fallback.val),
      List.ofFn bits)=
      matrixCode (listedOuterDraw r c e hr hc b h hb x steps attempts fallback bits).val := by
  have hf : 0<f := by positivity
  have hwidth : 0 < steps*(s+f)+f := by omega
  unfold profileRetry profileRetryWords
  dsimp only [profileTrialWidth]
  rw [wordChunks_ofFn hwidth,FirstSuccessProgram.retry_ofFn]
  have he : (fun word : Fin (steps*(s+f)+f) → Bool =>
      packedProfileTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn word))=
      (fun word => (stateTrial r c (listedJointDraw r c e hr hc b h hb x steps word)).map
        (fun T => matrixCode T.val)) := by
    funext word
    exact packedProfileTrial_code r c e hr hc b h hb htotal x steps word
  rw [he,FirstSuccessProgram.wordRetry_map]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed schedule and initializer equal the proved sampler data -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] profileRetry listedOuterDraw tableState
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma parameterTrials_ofFn (k : ℕ) :
    parameterTrials ((List.ofFn r,List.ofFn c),k)=outerTrials d k := by
  rw [parameterTrials,parameterDimension_ofFn]
  rfl

lemma parameterWordCount_ofFn (k : ℕ) :
    parameterWordCount ((List.ofFn r,List.ofFn c),k)=finiteSamplerBits r c k := by
  rw [parameterWordCount,parameterTrials_ofFn,parameterSteps_ofFn,parameterProposalWidth_ofFn,
    parameterCompletionWidth_ofFn]

lemma initialConfiguration_code (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    initialConfiguration ((List.ofFn r,List.ofFn c),k)=
      encodedConfiguration r c (computedCellEquiv r c) (outerAccuracy d b k)
        (tableState r c (GreedyFeasibleTable.table r c htotal))
        (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialConfiguration
  rw [initialCheck_code r c htotal,marginPadding_ofFn,parameterDimension_ofFn,
    parameterAccuracy_ofFn,initialViews_code r c htotal]
  rfl

lemma samplingSchedule_ofFn (k : ℕ) :
    samplingSchedule ((List.ofFn r,List.ofFn c),k)=
      ((outerSteps d b k,smallProposalBits (I := Fin m) (J := Fin n)),
        25*(d+b+outerAccuracy d b k+1)^62) := by
  rw [samplingSchedule,parameterSteps_ofFn,parameterProposalWidth_ofFn,parameterCompletionWidth_ofFn]

/-- Equality of the actual list program with the listed finite-word draw.
The current theorem is for the nonempty large-rectangle branch. -/
theorem samplingMatrix_code
    (hr : 0<(largeIndices (d^20,List.ofFn r)).length)
    (hc : 0<(largeIndices (d^20,List.ofFn c)).length)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    samplingMatrix (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (listedOuterDraw r c (computedCellEquiv r c) hr hc b (outerAccuracy d b k)
        (smallBinaryLength_parameters r c).1 (tableState r c (GreedyFeasibleTable.table r c htotal))
        (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits).val := by
  have hdraw := profileRetry_code r c (computedCellEquiv r c) hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 htotal
    (tableState r c (GreedyFeasibleTable.table r c htotal))
    (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits
  unfold samplingMatrix samplingRetryParameters
  rw [initialConfiguration_code r c htotal,samplingSchedule_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  have hcode : matrixCode (GreedyFeasibleTable.table r c htotal).val=
      List.ofFn (fun i => List.ofFn (GreedyFeasibleTable.matrix r c i)) := rfl
  rw [hcode] at hdraw
  dsimp only at hdraw ⊢
  exact hdraw

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical execution of the computed public profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.LiteralCodec Turing

lemma printMatrix_alphabet (rows : DensePrograms.MatrixCode) :
    ∀ a∈GreedyFeasibleTable.printMatrix rows,a≠6 ∧ a≠7 := by
  intro a ha
  obtain ⟨row,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PackedMatrixInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Packed physical output still identifies its contingency table -/

namespace ContingencyTables.PackedMatrixInjective
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

lemma deterministic_unique (P : Program) (input X Y : Tape Symbol) (n m : ℕ)
    (hX : P.Realizes input (.done X) n) (hY : P.Realizes input (.done Y) m) : X=Y := by
  obtain ⟨p,hp,hpm,_⟩ := hX
  obtain ⟨q,hq,hqm,_⟩ := hY
  have ha : p.All (fun T => T=X) := Experiment.all_of_mean_eq hpm _ rfl
  have hb : q.All (fun T => T=Y) := Experiment.all_of_mean_eq hqm _ rfl
  have he := hp.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_right _ _) (fun _ => false)
  have hf := hq.padded_execution (fun _ => rfl) (p.cost+q.cost) (Nat.le_add_left _ _) (fun _ => false)
  rw [Experiment.all_run p _ ha] at he
  rw [Experiment.all_run q _ hb] at hf
  exact congrArg Cfg.tape (he.symm.trans hf)

lemma table_injective {m n : ℕ} {r : Fin m → ℕ} {c : Fin n → ℕ} (X Y : Table r c)
    (h : Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val)))=
      Tape.mk₁ (TreePost.packed (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val)))) : X=Y := by
  have hx := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode X.val))
    (ProfilePrograms.printMatrix_alphabet _)
  have hy := LiteralProgram.post_realizes (GreedyFeasibleTable.printMatrix (DensePrograms.matrixCode Y.val))
    (ProfilePrograms.printMatrix_alphabet _)
  rw [←h] at hy
  have ht := deterministic_unique LiteralProgram.post _ _ _ _ _ hx hy
  have he := congrArg Tape.right₀ ht
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀,DensePrograms.matrixCode,GreedyFeasibleTable.printMatrix_ofFn] at he
  exact Subtype.ext (Algorithms.blankMatrix_injective X.val Y.val he)

end ContingencyTables.PackedMatrixInjective

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word semantics of the all-small profile walk -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] stateCode unitNext capViews codeNeighborProposal
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma unitNext_encoded (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (bits : Fin s → Bool) :
    unitNext (encodedConfiguration r c e h initial x,List.ofFn bits)=
      stateCode r c e (unitCodeBitStep r c e x bits) := by
  have hp := codeProposal_encoded r c e htotal x bits
  simp only [unitNext,unitCandidateInput,currentParameters_encoded,stepCandidateViews,stepProposal]
  change capViews (stateCodeData r c e initial,
    (codeNeighborProposal (stateCodeData r c e x,List.ofFn bits)).getD (stateCode r c e x))=_
  rw [hp]
  cases he : decodedCodeProposal r c e x bits with
  | none =>
    simp only [Option.map_none,Option.getD_none,unitCodeBitStep,he]
    exact capViews_stateCode r c e initial x
  | some y =>
    simp only [Option.map_some,Option.getD_some,unitCodeBitStep,he]
    exact capViews_stateCode r c e initial y

lemma unitAdvance_encoded (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (bits : Fin s → Bool) :
    unitAdvance (List.ofFn bits,encodedConfiguration r c e h initial x)=
      encodedConfiguration r c e h initial (unitCodeBitStep r c e x bits) := by
  apply Prod.ext
  · rfl
  ·
    have hn := unitNext_encoded r c e htotal h initial x bits
    simpa only [unitAdvance,encodedConfiguration] using hn

lemma unitProfileWalk_ofFn (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ)
    (initial x : PaperStates r c) (steps : ℕ) (bits : Fin steps → Fin s → Bool) :
    unitProfileWalk (encodedConfiguration r c e h initial x,List.ofFn (fun i => List.ofFn (bits i)))=
      encodedConfiguration r c e h initial (wordWalk (unitCodeBitStep r c e) x steps bits) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    unfold unitProfileWalk at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change unitAdvance (List.ofFn (bits (Fin.last steps)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun state word => unitAdvance (word,state))
        (encodedConfiguration r c e h initial x))=_
    rw [ih (Fin.init bits)]
    exact unitAdvance_encoded r c e htotal h initial _ _

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOutputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing the original table when every cell is small -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open FirstPaperProfiles PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "L" => d^12

lemma unitOutputEntry (hsmall : ∀ i j,paperSmall r c i j=true)
    (x : PaperStates r c) (i : Fin m) (j : Fin n) :
    outputEntry (unitOutputData r c e x,(i.val,j.val))=
      (allSmallFibre r c hsmall x).val.val.1 i j := by
  have he := outputEntry_small (paperSmall r c) e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c L x)
    (largeIndices (U,List.ofFn r)) (largeIndices (U,List.ofFn c)) U L [] i j (hsmall i j)
  apply he.trans
  simpa only [smallView,hsmall i j,dite_true] using
    ((allSmallFibre r c hsmall x).property.2.2.1 i j (hsmall i j)).1.symm

lemma unitOutputSuccess (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) :
    outerSuccess (unitOutputData r c e x)=true ↔
      StateJointSuccess r c ⟨x,allSmallFibre r c hsmall x⟩ := by
  change (balancedTest (stateCode r c e x,U) && paddingTest (L,[]))=true ↔ _
  simp only [paddingTest,List.all_nil,Bool.and_true]
  rw [balancedTest_stateCode]
  constructor
  · intro h
    refine ⟨h,?_⟩
    intro i j hij
    rw [hsmall i j] at hij
    contradiction
  · exact And.left

lemma unitOutputMatrix (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c)
    (hx : StateJointSuccess r c ⟨x,allSmallFibre r c hsmall x⟩) :
    outputMatrix (prepareOutput ((stateCodeData r c e x,L),[]))=
      matrixCode ((originalStateSuccessEquiv r c).symm ⟨⟨x,allSmallFibre r c hsmall x⟩,hx⟩).val := by
  change outputMatrix ((List.ofFn r,List.ofFn c),unitOutputData r c e x)=_
  rw [outputMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [unitOutputEntry r c e hsmall,originalStateSuccessEquiv_symm_entry]
  simp only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,hsmall i j,
    Bool.true_eq_false,ite_false,Nat.sub_zero]

lemma unitOuterTrial (hsmall : ∀ i j,paperSmall r c i j=true) (x : PaperStates r c) :
    outerTrial ((stateCodeData r c e x,L),[])=
      (stateTrial r c ⟨x,allSmallFibre r c hsmall x⟩).map (fun T => matrixCode T.val) := by
  by_cases h : StateJointSuccess r c ⟨x,allSmallFibre r c hsmall x⟩
  · have hp := (unitOutputSuccess r c e hsmall x).mpr h
    calc
      _ = some (outputMatrix (prepareOutput ((stateCodeData r c e x,L),[]))) := ite_eq_left hp
      _ = some (matrixCode ((originalStateSuccessEquiv r c).symm
          ⟨⟨x,allSmallFibre r c hsmall x⟩,h⟩).val) :=
        congrArg some (unitOutputMatrix r c e hsmall x h)
      _ = _ := by
        simp only [stateTrial,FirstSuccess.partialEquivDraw,dite_eq_left h,Option.map_some]
  · have hp : outerSuccess (unitOutputData r c e x)≠true :=
      fun hp => h ((unitOutputSuccess r c e hsmall x).mp hp)
    calc
      _ = none := ite_eq_right hp
      _ = _ := by
        simp only [stateTrial,FirstSuccess.partialEquivDraw,dite_eq_right h,Option.map_none]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-small executable trials realize the uniform finite-word law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms FirstPaperPhysicalMarginal CompletionCounts
open FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] unitProfileRetry unitCodeOuterDraw
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma smallProposalBits_pos : 0 < s := by
  apply Nat.clog_pos (by decide)
  have hd : 1≤dimensionAllowance (I := Fin m) (J := Fin n) := by unfold dimensionAllowance; omega
  have hs := Nat.pow_le_pow_left hd 2
  omega

lemma unitPackedTrial_ofFn (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ) (x : PaperStates r c)
    (steps f : ℕ) (bits : Fin (steps*s) → Bool) :
    unitPackedTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn bits)=
      (stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x steps bits)).map
        (fun T => matrixCode T.val) := by
  unfold unitPackedTrial unitPackedState unitPackedWords
  rw [wordChunks_ofFn (smallProposalBits_pos (m := m) (n := n))]
  rw [unitProfileWalk_ofFn r c e htotal,currentParameters_encoded]
  exact unitOuterTrial r c e hsmall _

lemma unitProfileRetry_code (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (h : ℕ) (x : PaperStates r c)
    (steps attempts f : ℕ) (hsteps : 0 < steps) (fallback : Table r c)
    (bits : Fin (attempts*(steps*s)) → Bool) :
    unitProfileRetry (((encodedConfiguration r c e h x x,((steps,s),f)),matrixCode fallback.val),
      List.ofFn bits)=
      matrixCode (unitCodeOuterDraw r c e (allSmallFibre r c hsmall) x steps attempts fallback bits).val := by
  have hwidth : 0 < steps*s := Nat.mul_pos hsteps (smallProposalBits_pos (m := m) (n := n))
  unfold unitProfileRetry unitRetryWords
  dsimp only [unitRetryWidth]
  rw [wordChunks_ofFn hwidth,FirstSuccessProgram.retry_ofFn]
  have he : (fun word : Fin (steps*s) → Bool =>
      unitPackedTrial ((encodedConfiguration r c e h x x,((steps,s),f)),List.ofFn word))=
      (fun word => (stateTrial r c (unitCodeJointDraw r c e (allSmallFibre r c hsmall) x steps word)).map
        (fun T => matrixCode T.val)) := by
    funext word
    exact unitPackedTrial_ofFn r c e hsmall htotal h x steps f word
  rw [he,FirstSuccessProgram.wordRetry_map]
  unfold unitCodeOuterDraw
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executable program chooses the correct rectangle branch -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] unitProfileRetry unitCodeOuterDraw
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma parameterUnitWords_ofFn (k : ℕ) :
    parameterUnitWords ((List.ofFn r,List.ofFn c),k)=outerTrials d k*(outerSteps d b k*s) := by
  rw [parameterUnitWords,parameterTrials_ofFn,parameterSteps_ofFn,parameterProposalWidth_ofFn]

lemma scheduled_steps_pos (k : ℕ) : 0<outerSteps d b k := by
  have hd : 0<d := by unfold dimensionAllowance; omega
  have hb := (smallBinaryLength_parameters r c).2.1
  unfold outerSteps
  exact Nat.mul_pos (pow_pos hd _) (pow_pos (by omega) _)

/-- The all-small branch uses a prefix of the same public fixed-length word. -/
lemma unitSamplingMatrix_code (hsmall : ∀ i j,paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (bits : Fin (finiteSamplerBits r c k) → Bool) :
    unitSamplingMatrix (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c hsmall)
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
        (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits)).val := by
  have hdraw := unitProfileRetry_code r c (computedCellEquiv r c) hsmall htotal
    (outerAccuracy d b k) (tableState r c (GreedyFeasibleTable.table r c htotal))
    (outerSteps d b k) (outerTrials d k) (25*(d+b+outerAccuracy d b k+1)^62)
    (scheduled_steps_pos r c k) (GreedyFeasibleTable.table r c htotal)
    (prefixWord (unitCodeBits_le r c k) bits)
  unfold unitSamplingMatrix unitSamplingInput unitSamplingBits samplingRetryParameters
  rw [parameterUnitWords_ofFn,take_ofFn_prefix (unitCodeBits_le r c k),
    initialConfiguration_code r c htotal,samplingSchedule_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  have hcode : matrixCode (GreedyFeasibleTable.table r c htotal).val=
      List.ofFn (fun i => List.ofFn (GreedyFeasibleTable.matrix r c i)) := rfl
  rw [hcode] at hdraw
  simpa only [Table] using hdraw

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingAccuracy
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the single computed sampler for arbitrary margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem samplingMatrixAll_code (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    samplingMatrixAll (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (scheduledTableDraw r c htotal k bits).val := by
  unfold samplingMatrixAll scheduledTableDraw
  by_cases h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true
  · rw [ite_eq_left h,dite_eq_left h]
    exact samplingMatrix_code r c ((hasLargeRectangle_spec r c k).mp h).1
      ((hasLargeRectangle_spec r c k).mp h).2 htotal k bits
  · rw [ite_eq_right h,dite_eq_right h]
    exact unitSamplingMatrix_code r c (allSmall_of_no_large r c k h) htotal k bits

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCheck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column checks for original-table candidates -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma originalColumnTotals_code {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : Fin m → Fin n → ℕ) :
    originalColumnTotals ((List.ofFn r,List.ofFn c),matrixCode X)=
      List.ofFn (fun j => ∑ i,X i j) := by
  unfold originalColumnTotals
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j<n := by simpa using hj'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact columnTotal_code X ⟨j,hjn⟩

lemma originalTableTest_code {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : Fin m → Fin n → ℕ) :
    originalTableTest ((List.ofFn r,List.ofFn c),matrixCode X)=true ↔ HasMargins X r c := by
  unfold originalTableTest
  rw [originalColumnTotals_code]
  simp only [Bool.and_eq_true,decide_eq_true_eq,matrixCode,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  constructor
  · rintro ⟨hr,hc⟩
    exact ⟨congrFun (List.ofFn_injective hr),congrFun (List.ofFn_injective hc)⟩
  · rintro ⟨hr,hc⟩
    exact ⟨congrArg List.ofFn (by funext i; exact hr i),congrArg List.ofFn (by funext j; exact hc j)⟩

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableBox
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original-table box and its unique feasible entries -/

namespace ContingencyTables.OriginalTableBox
open DensePrograms ProfilePrograms
open scoped BigOperators Classical
noncomputable section

lemma freeMatrix_code {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (z : Box m n N) :
    originalFreeMatrix ((List.ofFn r,List.ofFn c),List.ofFn (fun i => (z i).val))=
      matrixCode (matrix z) := by
  exact unflattenGrid_code (fun i : Option (Fin m) => i.elim 0 r)
    (fun j : Option (Fin n) => j.elim 0 c) (fun i => (z i).val)

lemma candidate_code {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (z : Box m n N) :
    originalCandidate ((List.ofFn r,List.ofFn c),List.ofFn (fun i => (z i).val))=
      (decode r c z).map (fun T => matrixCode T.val) := by
  unfold originalCandidate
  rw [freeMatrix_code]
  unfold decode
  by_cases h : HasMargins (matrix z) r c
  · rw [ite_eq_left ((originalTableTest_code r c (matrix z)).mpr h),dite_eq_left h]
    rfl
  · rw [ite_eq_right (fun ht => h ((originalTableTest_code r c (matrix z)).mp ht)),dite_eq_right h]
    rfl

lemma candidates_code {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    originalCandidates (List.ofFn r,List.ofFn c)=
      List.ofFn (fun k : Index m n (∑ i,r i) =>
        (tableAt r c k).map (fun T => matrixCode T.val)) := by
  have hl : ((zeroGrid (0::List.ofFn r,0::List.ofFn c)).map
      (fun _ => false)).length=m*n := by
    simp only [zeroGrid,List.tail_cons,List.length_map,cellPairs,
      List.length_range,List.length_ofFn]
  unfold originalCandidates originalEnumerationData completionEnumerationData
  simp only [originalLayoutMargins,List.sum_cons,zero_add,List.sum_ofFn]
  rw [gridWords_finFunctions _ (∑ i,r i) (m*n) hl,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  exact candidate_code r c (finFunctionFinEquiv.symm k)

end
end ContingencyTables.OriginalTableBox

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactMatrixLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasibility of every decoded candidate in the exact branch -/

namespace ContingencyTables.ExactMatrixTrial
open ProfilePrograms DensePrograms OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

/-- Even a malformed index returns the fixed feasible fallback. -/
lemma lookup_feasible (fallback : Table r c) (i : ℕ) :
    ∃ X : Table r c,
      lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),i)=
        matrixCode X.val := by
  rw [lookup,candidates_code]
  by_cases hi : i<((∑ j,r j)+1)^(m*n)
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some]
    cases hx : tableAt r c (⟨i,hi⟩ : Index m n (∑ j,r j)) with
    | none => exact ⟨fallback,rfl⟩
    | some X => exact ⟨X,rfl⟩
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_false,Option.getD_none]
    exact ⟨fallback,rfl⟩

end
end ContingencyTables.ExactMatrixTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactSamplingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact sampler's precision from its margin-only input -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.LiteralParse
open scoped BigOperators

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma exactPrecision_ofFn : exactPrecision (List.ofFn r,List.ofFn c)=correctionPrecision r c := by
  rw [exactPrecision,marginDimension_ofFn,marginBinaryLength_ofFn]
  rfl

lemma exactSamplingParameters_ofFn :
    exactSamplingParameters (List.ofFn r,List.ofFn c)=
      ((List.ofFn r,List.ofFn c),2*correctionPrecision r c) := by
  rw [exactSamplingParameters,exactPrecision_ofFn]

lemma exactBranchDenominator_ofFn :
    exactBranchDenominator (List.ofFn r,List.ofFn c)=2^(correctionPrecision r c) := by
  rw [exactBranchDenominator,BinaryPowerPrograms.power_eq,exactPrecision_ofFn]

lemma exactResidualInput_ofFn :
    exactResidualInput (List.ofFn r,List.ofFn c)=
      (((List.ofFn r,List.ofFn c),2*correctionPrecision r c),2^(correctionPrecision r c)) := by
  rw [exactResidualInput,exactSamplingParameters_ofFn,exactBranchDenominator_ofFn]

lemma exactOrdinaryBits_ofFn :
    exactOrdinaryBits (List.ofFn r,List.ofFn c)=finiteSamplerBits r c (2*correctionPrecision r c) := by
  rw [exactOrdinaryBits,exactSamplingParameters_ofFn,parameterWordCount_ofFn]

lemma exactParsedMargins_spec :
    exactParsedMargins (Algorithms.encodeMargins r c)=(List.ofFn r,List.ofFn c) := by
  unfold exactParsedMargins parsedSampling samplingInput
  rw [GreedyFeasibleTable.encodeMargins_natWords,GreedyFeasibleTable.parse_natWords]
  have h := GreedyFeasibleTable.marginLists_spec m n (List.ofFn r) (List.ofFn c) []
    List.length_ofFn List.length_ofFn
  simpa only [List.append_nil] using h

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactResidualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete input to the exact matrix rejection loop -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms OriginalTableBox ResidualMixture FirstSuccess CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "D" => correctionPrecision r c

lemma exactMatrixInput_code (htotal : (∑ i,r i)=∑ j,c j) :
    exactMatrixInput (List.ofFn r,List.ofFn c)=
      ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode (GreedyFeasibleTable.table r c htotal).val),
        scheduledResidualCounts (((List.ofFn r,List.ofFn c),2*D),2^D)) := by
  unfold exactMatrixInput exactRareWeights
  rw [exactResidualInput_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactOrdinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite ordinary branch of the exact sampler -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.PhysicalStream
open scoped BigOperators

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma exactOrdinaryWord_code (htotal : (∑ i,r i)=∑ j,c j)
    (bits : Fin (finiteSamplerBits r c (2*correctionPrecision r c)) → Bool) :
    exactOrdinaryWord ((List.ofFn r,List.ofFn c),List.ofFn bits)=
      matrixCode (scheduledTableDraw r c htotal (2*correctionPrecision r c) bits).val := by
  rw [exactOrdinaryWord,exactSamplingParameters_ofFn,samplingMatrixAll_code r c htotal]

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite control graph for the ordinary and unbounded correction branches -/

namespace ContingencyTables.ExactCoreProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

/-- The failed endpoint is inside the actual retry subroutine. Its successful
endpoints have halted with the sampled matrix in the output register. -/
theorem prefix_correct (z : CompletionMargins) (s : Data) (N : ℕ) :
    ∃ p,Executes program.code program.coin (output z s)
      (OnlineTree.initial program (TreeTyped.encode z) s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(prefixExperiment z N).mean g := by
  let out := output z s
  have halted (X : MatrixCode) :
      OnlinePartialCall.At instructions out (some .halt) (env (TreeTyped.encode X) .nil s)
        (.delay 1 (.done (some X))) :=
    OnlinePartialCall.halt instructions out .halt rfl (some X) _ rfl
  have ordinary : ∃ p,OnlinePartialCall.At instructions out (some .ordinary)
      (env (TreeTyped.encode z) .nil s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=((exactOrdinary z).map some).mean g := by
    obtain ⟨u,hu,hum,_⟩ := exactOrdinaryRealizer.correct z s
    refine ⟨.delay 1 (u.bind (fun X => .delay 1 (.done (some X)))),?_,?_⟩
    · exact OnlinePartialCall.call instructions out .ordinary .halt exactOrdinaryRealizer.program
        rfl _ (fun X => env (TreeTyped.encode X) .nil s) u hu _ halted
    · intro g
      simp only [Experiment.mean,Experiment.mean_bind,Experiment.mean_map]
      exact hum _
  have rare : ∃ p,OnlinePartialCall.At instructions out (some .prepareRare)
      (env (TreeTyped.encode z) .nil s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(correctionPrefix z N).mean g := by
    obtain ⟨u,hu,hum,_⟩ := OnlineIntegerRetry.prefix_correct ExactMatrixTrial.trialRealizer
      (exactMatrixInput z) s N
    let v : Option MatrixCode → Experiment (Option MatrixCode) :=
      fun o => match o with | none => .done none | some X => .delay 1 (.done (some X))
    have hcall := OnlinePartialCall.partial_call instructions .retry
      ⟨_,.halt,rfl⟩ (env (TreeTyped.encode (exactMatrixInput z)) .nil s)
      (fun o => OnlineControl.cfg (OnlineIntegerRetry.instructions ExactMatrixTrial.trialRealizer)
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).1
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).2) u hu
    have hv : Executes (OnlineControl.code instructions) (OnlineControl.coins instructions) out
        (OnlineControl.cfg instructions (some .retry)
          (env (TreeTyped.encode (exactMatrixInput z)) .nil s))
        ((Experiment.delay 1 u).bind v) := by
      apply hcall.bind v out
      intro o
      cases o with
      | none => exact .done none
      | some X => exact halted X
    obtain ⟨p,hp,hpm,_⟩ := OnlinePartialCall.deterministicCall instructions out .prepareRare .retry
      exactMatrixInputRealizer.program rfl _ _ _ (exactMatrixInputRealizer.correct z s)
      ((Experiment.delay 1 u).bind v) hv
    refine ⟨p,hp,?_⟩
    intro g
    rw [hpm,Experiment.mean_bind]
    simp only [Experiment.mean]
    have he : (fun o => (v o).mean g)=g := by funext o; cases o <;> rfl
    rw [he,hum]
    rfl
  have branch (b : Bool) : ∃ p,OnlinePartialCall.At instructions out (some .choose)
      (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=
        (if b then correctionPrefix z N else (exactOrdinary z).map some).mean g := by
    cases b with
    | false =>
      obtain ⟨p,hp,hpm⟩ := ordinary
      obtain ⟨v,hv,hvm,_⟩ := OnlinePartialCall.deterministicCall instructions out
        .ordinaryInput .ordinary (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode false) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,fun g => hvm g |>.trans (hpm g)⟩
      exact OnlinePartialCall.nilBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _ rfl v hv
    | true =>
      obtain ⟨p,hp,hpm⟩ := rare
      obtain ⟨v,hv,hvm,_⟩ := OnlinePartialCall.deterministicCall instructions out
        .rareInput .prepareRare (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode true) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,fun g => hvm g |>.trans (hpm g)⟩
      exact OnlinePartialCall.consBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _
        .nil .nil rfl v hv
  choose v hv hvm using branch
  obtain ⟨u,hu,hum,_⟩ := rareBranchRealizer.correct z (.cons (TreeTyped.encode z) s)
  have hgate := OnlinePartialCall.call instructions out .gate .choose rareBranchRealizer.program
    rfl _ (fun b => env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) u hu v hv
  obtain ⟨p,hp,hpm,_⟩ := OnlinePartialCall.deterministicCall instructions out .prepare .gate
    OnlineIntegerRetry.prepareProc rfl _ _ _ (OnlineIntegerRetry.prepare_exec (TreeTyped.encode z) s)
    (.delay 1 (u.bind v)) hgate
  refine ⟨p,hp,?_⟩
  intro g
  rw [hpm]
  simp only [Experiment.mean,Experiment.mean_bind]
  simp_rw [hvm]
  rw [hum,prefixExperiment,Experiment.mean_bind]

end ContingencyTables.ExactCoreProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactTypedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing and printing around the same unbounded exact core -/

namespace ContingencyTables.ExactTypedProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

theorem printed_correct (z : CompletionMargins) (s : Data) (N : ℕ) :
    ∃ p,Executes printedProgram.code printedProgram.coin (printedOutput z s)
      (OnlineTree.initial printedProgram (TreeTyped.encode z) s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(ExactCoreProgram.prefixExperiment z N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactCoreProgram.prefix_correct z s N
  have hp' := hp.relabel printedProgram.code printedProgram.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  have next (o : Option MatrixCode) : ∃ q,
      Executes printedProgram.code printedProgram.coin (printedOutput z s)
        (StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactCoreProgram.output z s o)) q ∧
      ∀ g : Option MatrixCode → ℚ,q.mean g=g o := by
    cases o with
    | none => exact ⟨.done none,.done none,fun _ => rfl⟩
    | some X =>
      obtain ⟨n,_,hn⟩ := GreedyFeasibleTable.printMatrixRealizer.correct X s
      obtain ⟨q,hq,hqm,_⟩ := Executes.of_run GreedyFeasibleTable.printMatrixRealizer.program.code n
        (OnlineTree.initial (OnlineProc.deterministic GreedyFeasibleTable.printMatrixRealizer.program)
          (TreeTyped.encode X) s) none (encodeEnv (env
          (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) .nil s)) hn
      have hq' := hq.relabel printedProgram.code printedProgram.coin Sum.inr none
        (fun _ => rfl) (fun _ => rfl)
      refine ⟨q.bind (fun _ => .done (some X)),?_,?_⟩
      · exact hq'.bind _ _ (fun _ => .done (some X))
      · intro g
        simpa only [Experiment.mean_bind,Experiment.mean] using hqm (fun _ => g (some X))
  choose q hq hqm using next
  refine ⟨p.bind q,hp'.bind q _ hq,?_⟩
  intro g
  rw [Experiment.mean_bind]
  simp_rw [hqm]
  exact hpm g

theorem prefix_correct (as : List Symbol) (s : Data) (N : ℕ) :
    ∃ p,Executes program.code program.coin (output as s)
      (OnlineTree.initial program (TreeTyped.encode as) s) p ∧
      ∀ g : Option MatrixCode → ℚ,
        p.mean g=(ExactCoreProgram.prefixExperiment (exactParsedMargins as) N).mean g := by
  obtain ⟨p,hp,hpm⟩ := printed_correct (exactParsedMargins as) s N
  have hp' := hp.relabel program.code program.coin Sum.inr none (fun _ => rfl) (fun _ => rfl)
  obtain ⟨n,_,hn⟩ := exactParsedMarginsRealizer.correct as s
  obtain ⟨u,hu,hum,_⟩ := Executes.of_run exactParsedMarginsRealizer.program.code n
    (OnlineTree.initial (OnlineProc.deterministic exactParsedMarginsRealizer.program)
      (TreeTyped.encode as) s) none (encodeEnv (env (TreeTyped.encode (exactParsedMargins as)) .nil s)) hn
  have hu' := hu.relabel program.code program.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  refine ⟨u.bind (fun _ => p),hu'.bind _ _ (fun _ => hp'),?_⟩
  intro g
  rw [Experiment.mean_bind,hum]
  exact hpm g

end ContingencyTables.ExactTypedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPartialSequence
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequencing finite prefixes that can stop at a live configuration

A called prefix may have reached the continuation, or may still be inside
its first program. The construction stops exactly at that interface.
-/

namespace ContingencyTables.PhysicalPartialSequence
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing

variable {Γ Q R A : Type} [Inhabited Γ]

lemma mean_const (p : Experiment A) (v : ℚ) : p.mean (fun _ => v)=v := by
  induction p with
  | done => rfl
  | delay n p ih => exact ih
  | read p ih => simp only [Experiment.mean,ih]; ring

lemma halted_all {M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q} {out : A → Cfg Γ Q} {c : Cfg Γ Q}
    {p : Experiment A} (h : Implements M out c p) (hc : c.state=none) :
    p.All (fun a => out a=c) := by
  induction h with
  | done a => rfl
  | read c p h ih =>
    have he (b : Bool) : PhysicalPost.tick M c b=c := by simp [PhysicalPost.tick,hc]
    exact ⟨by simpa only [he] using ih false (by rw [he]; exact hc),
      by simpa only [he] using ih true (by rw [he]; exact hc)⟩
  | delay c d n p hs hr ih =>
    have he : d=c := by
      rw [←hs (fun _ => false)]
      rcases c with ⟨q,T⟩
      cases hc
      exact execute_halted M n T (fun _ => false)
    subst d
    exact ih hc

lemma early_all_eq (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c d : Cfg Γ Q) (n : ℕ)
    (h : ∀ b : Stream,execute M n c b=d) :
    (early M n c).All (fun x => x=d) := by
  classical
  rw [Experiment.all_indicator,PhysicalPost.early_mean]
  simp only [h,ite_true, if_true,average_const]

/-- Relabelling a physical prefix for sequential composition may shorten
its post-halt padding, and preserves the law of its endpoint configuration. -/
theorem left_prefix (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (N : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment (Cfg Γ Q),
      Implements (seq M N r₀) (leftCfg r₀) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean (fun a => f (out a))) ∧ q.cost≤p.cost := by
  induction h with
  | done a => exact ⟨.done (out a),.done (out a),fun _ => rfl,le_rfl⟩
  | read c p h ih =>
    by_cases hc : c.state=none
    · have hall := halted_all (Implements.read c p h) hc
      refine ⟨.done c,.done c,?_,Nat.zero_le _⟩
      intro f
      have hm := Experiment.mean_congr_all (.read p) (fun a => f (out a)) (fun _ => f c)
        (hall.mono (by intro a ha; rw [ha]))
      exact (hm.trans (mean_const _ _)).symm
    · obtain ⟨q,hq,hqm,hqc⟩ := ih false
      obtain ⟨r,hr,hrm,hrc⟩ := ih true
      let v : Bool → Experiment (Cfg Γ Q) := fun b => if b then r else q
      refine ⟨.read v,?_,?_,?_⟩
      · apply Implements.read
        intro b
        rcases c with ⟨state,T⟩
        cases state with
        | none => exact False.elim (hc rfl)
        | some s =>
          rw [tick_left]
          cases b
          · exact hq
          · exact hr
      · intro f
        simp only [Experiment.mean,v,Bool.false_eq_true,ite_false,ite_true, if_true,hqm,hrm]
      · simp only [Experiment.cost,v,Bool.false_eq_true,ite_false,ite_true, if_true]
        omega
  | delay c d n p hs hr ih =>
    obtain ⟨q,hq,hqm,hqc⟩ := ih
    let u := early M n c
    have hu := early_left M N r₀ n c
    have hall : u.All (fun x => x=d) := early_all_eq M c d n hs
    refine ⟨u.bind (fun _ => q),?_,?_,?_⟩
    · apply hu.bind_all (fun _ => q) (leftCfg r₀)
      exact hall.mono (by intro x hx; rw [hx]; exact hq)
    · intro f
      rw [Experiment.mean_bind,mean_const,hqm]
      rfl
    · exact (Experiment.cost_bind_le u (fun _ => q) q.cost (fun _ => le_rfl)).trans
        (Nat.add_le_add (early_cost M n c) hqc)

/-- When endpoint configurations identify their labels, sequential composition
also preserves the complete label law, not just the endpoint law. -/
theorem left_prefix_injective [Nonempty A] (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (N : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ R) (r₀ : R)
    (out : A → Cfg Γ Q) (hinj : Function.Injective out) (c : Cfg Γ Q) (p : Experiment A)
    (h : Implements M out c p) :
    ∃ q : Experiment A,
      Implements (seq M N r₀) (fun a => leftCfg r₀ (out a)) (leftCfg r₀ c) q ∧
      (∀ f,q.mean f=p.mean f) ∧ q.cost≤p.cost := by
  classical
  obtain ⟨q,hq,hqm,hqc⟩ := left_prefix M N r₀ out c p h
  let dec : Cfg Γ Q → A := Function.invFun out
  have hd (a : A) : dec (out a)=a := Function.leftInverse_invFun hinj a
  have hall : q.All (fun x => out (dec x)=x) := by
    apply Experiment.all_of_mean_eq (p := p.map out) (q := q)
    · intro f
      rw [Experiment.mean_map]
      exact hqm f
    · rw [Experiment.all_map]
      exact (Experiment.all_true p).mono (by intro a _; rw [hd])
  refine ⟨q.map dec,hq.map_all dec (fun a => leftCfg r₀ (out a))
    (hall.mono (by intro x hx; rw [hx])),?_,?_⟩
  · intro f
    rw [Experiment.mean_map,hqm]
    simp only [hd]
  · simpa only [Experiment.cost_map] using hqc

end ContingencyTables.PhysicalPartialSequence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPhysicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical execution of the parsed and printed exact sampler -/

namespace ContingencyTables.ExactPhysicalProgram
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms

attribute [local irreducible] ExactTypedProgram.program

lemma output_some (as : List Symbol) (X : MatrixCode) :
    output as (some X)=program.final (Tape.mk₁ (packed (GreedyFeasibleTable.printMatrix X))) := by
  change upCfg (OnlineStack.cfg
    (⟨none,none,inputStacks (GreedyFeasibleTable.printMatrix X)⟩ :
      OnlineTree.StoreCfg ExactTypedProgram.program))=_
  exact OnlineTree.cfg_packed ExactTypedProgram.program (GreedyFeasibleTable.printMatrix X) none

lemma output_none_live (as : List Symbol) : (output as none).state≠none := by
  change (some _ : Option program.State)≠none
  exact Option.some_ne_none _

/-- Every finite exact-sampling prefix runs on one fixed finite physical
transition table, including its live failure endpoint. -/
theorem prefix_correct (as : List Symbol) (N : ℕ) :
    ∃ q,Implements program.table (output as)
      (program.initial (Tape.mk₁ (packed as))) q ∧
      ∀ g : Option MatrixCode → ℚ,
        q.mean g=(ExactCoreProgram.prefixExperiment (ProfilePrograms.exactParsedMargins as) N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactTypedProgram.prefix_correct as .nil N
  obtain ⟨q,hq,hqm,_⟩ := hp.compile (weight as) (inputStacks_bound as)
  have hu := hq.up
  have hi := OnlineTree.cfg_packed ExactTypedProgram.program as (some default)
  change upCfg (OnlineStack.cfg (OnlineTree.initial ExactTypedProgram.program (encode as) .nil))=
    program.initial (Tape.mk₁ (packed as)) at hi
  rw [hi] at hu
  exact ⟨q,hu,fun g => (hqm g).trans (hpm g)⟩

end ContingencyTables.ExactPhysicalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrefixLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite prefixes of the fixed exact-sampling program -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS MatchingFPRAS.PhysicalStream
open ResidualMixture FirstSuccess CompletionCounts
attribute [local irreducible] scheduledTableDraw exactOrdinary exactOrdinaryWord
  exactSamplingParameters ExactCoreProgram.prefixExperiment correctionPrefix
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "D" => correctionPrecision r c

lemma exactOrdinary_mean (htotal : (∑ i,r i)=∑ j,c j) (g : MatrixCode → ℚ) :
    (exactOrdinary (List.ofFn r,List.ofFn c)).mean g=
      average (fun bits : Bits (finiteSamplerBits r c (2*D)) =>
        g (matrixCode (scheduledTableDraw r c htotal (2*D) bits).val)) := by
  rw [exactOrdinary,FiniteWordExecution.experiment_mean,exactOrdinaryBits_ofFn]
  simp_rw [exactOrdinaryWord_code r c htotal]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrefixFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasibility is preserved on both branches and every finite retry prefix -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.PhysicalStream
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] exactOrdinary correctionPrefix exactMatrixInput
  ExactCoreProgram.prefixExperiment scheduledTableDraw ExactIntegerOnline.trial
  scheduledResidualCounts originalCandidates

lemma exactOrdinary_feasible (htotal : (∑ i,r i)=∑ j,c j) :
    (exactOrdinary (List.ofFn r,List.ofFn c)).All (FeasibleCode r c) := by
  rw [Experiment.all_indicator,exactOrdinary_mean r c htotal]
  have he (bits : Bits (finiteSamplerBits r c (2*correctionPrecision r c))) :
      (if FeasibleCode r c (matrixCode (scheduledTableDraw r c htotal
        (2*correctionPrecision r c) bits).val) then (0:ℚ) else 1)=0 :=
    ite_eq_left ⟨_,rfl⟩
  simp_rw [he]
  exact average_const _ _

lemma exactTrial_feasible (htotal : (∑ i,r i)=∑ j,c j) :
    (ExactMatrixTrial.trial (exactMatrixInput (List.ofFn r,List.ofFn c))).All
      (FeasibleOutcome r c) := by
  rw [exactMatrixInput_code r c htotal,ExactMatrixTrial.trial,Experiment.all_map]
  apply (Experiment.all_true _).mono
  intro o _
  cases o with
  | none => trivial
  | some i =>
    exact ExactMatrixTrial.lookup_feasible r c (GreedyFeasibleTable.table r c htotal) i

lemma correctionPrefix_feasible (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (correctionPrefix (List.ofFn r,List.ofFn c) N).All (FeasibleOutcome r c) := by
  unfold correctionPrefix
  induction N with
  | zero => trivial
  | succ N ih =>
    rw [OnlineIntegerRetry.prefixExperiment,Experiment.all_bind]
    apply (exactTrial_feasible r c htotal).mono
    intro o ho
    cases o with
    | none => exact ih
    | some X => exact ho

lemma exactPrefix_feasible (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).All (FeasibleOutcome r c) := by
  rw [ExactCoreProgram.prefixExperiment,Experiment.all_bind]
  apply (Experiment.all_true _).mono
  intro rare _
  cases rare with
  | false =>
    rw [ite_eq_right Bool.false_ne_true,Experiment.all_map]
    exact exactOrdinary_feasible r c htotal
  | true => exact correctionPrefix_feasible r c htotal N

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactTablePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical prefixes indexed by feasible tables -/

namespace ContingencyTables.ExactTablePrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open DensePrograms SmallGraphProfiles Turing
open scoped Classical BigOperators
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] ExactCoreProgram.prefixExperiment
  ExactPhysicalProgram.program ExactPhysicalProgram.output

lemma code_injective : Function.Injective (code r c) := by
  intro X Y h
  cases X with
  | none => cases Y <;> simp_all [code]
  | some X =>
    cases Y with
    | none => simp [code] at h
    | some Y =>
      apply congrArg some
      apply Subtype.ext
      have he : matrixCode X.val=matrixCode Y.val := Option.some.inj h
      change List.ofFn (fun i => List.ofFn (X.val i))=List.ofFn (fun i => List.ofFn (Y.val i)) at he
      funext i
      exact List.ofFn_injective (congrFun (List.ofFn_injective he) i)

lemma decode_code (o : Option (Table r c)) : decode r c (code r c o)=o :=
  Function.leftInverse_invFun (code_injective r c) o

lemma code_decode {o : Option MatrixCode} (h : FeasibleOutcome r c o) :
    code r c (decode r c o)=o := by
  cases o with
  | none => exact congrArg (code r c) (decode_code r c none)
  | some X =>
    obtain ⟨T,hT⟩ := h
    subst X
    exact congrArg (code r c) (decode_code r c (some T))

lemma output_injective : Function.Injective (output r c) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some Y =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) none).state=
        (ExactPhysicalProgram.output (input r c) (some (matrixCode Y.val))).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he)
  | some X =>
    cases b with
    | none =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) (some (matrixCode X.val))).state=
        (ExactPhysicalProgram.output (input r c) none).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he.symm)
    | some Y =>
      apply congrArg some
      apply PackedMatrixInjective.table_injective X Y
      change ExactPhysicalProgram.output _ (some (matrixCode X.val))=
        ExactPhysicalProgram.output _ (some (matrixCode Y.val)) at h
      rw [ExactPhysicalProgram.output_some,ExactPhysicalProgram.output_some] at h
      simpa only [Program.final,Cfg.mk.injEq,true_and] using h

theorem physical_prefix (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements ExactPhysicalProgram.program.table (output r c)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (input r c)))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactPhysicalProgram.prefix_correct (input r c) N
  have hm (g : Option MatrixCode → ℚ) :
      p.mean g=(ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean g := by
    simpa only [input,exactParsedMargins_spec] using hpm g
  have hall : p.All (FeasibleOutcome r c) :=
    Experiment.all_of_mean_eq hm _ (exactPrefix_feasible r c htotal N)
  refine ⟨p.map (decode r c),hp.map_all (decode r c) (output r c)
    (hall.mono (by intro o ho; unfold output; rw [code_decode r c ho])),?_⟩
  intro g
  rw [Experiment.mean_map,hm,experiment,Experiment.mean_map]

end
end ContingencyTables.ExactTablePrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exact-sampling machine on the literal public binary tape -/

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma middle_prefix (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements middle.table (middleOutput r c)
      (middle.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactTablePrefix.physical_prefix r c htotal N
  obtain ⟨q,hq,hqm,_⟩ := PhysicalPartialSequence.left_prefix_injective
    ExactPhysicalProgram.program.table LiteralProgram.post.table LiteralProgram.post.entry
    (ExactTablePrefix.output r c) (ExactTablePrefix.output_injective r c) _ p hp
  have next (o : Option (Table r c)) : ∃ u,
      Implements middle.table (middleOutput r c)
        (leftCfg LiteralProgram.post.entry (ExactTablePrefix.output r c o)) u ∧
      ∀ g : Option (Table r c) → ℚ,u.mean g=g o := by
    cases o with
    | none => exact ⟨.done none,.done none,fun _ => rfl⟩
    | some X =>
      obtain ⟨u,hu,hum,_⟩ := LiteralProgram.post_realizes (word r c X)
        (ProfilePrograms.printMatrix_alphabet _)
      have hu' := hu.right (M := ExactPhysicalProgram.program.table) LiteralProgram.post.entry
      have hall : u.All (fun T => T=Tape.mk₁ (word r c X)) :=
        Experiment.all_of_mean_eq hum _ rfl
      refine ⟨u.map (fun _ => some X),?_,?_⟩
      · have hv := hu'.map_all (fun _ => some X) (middleOutput r c)
          (hall.mono (by intro T hT; rw [hT]; rfl))
        simpa only [middle,Program.seq,ExactTablePrefix.output,ExactTablePrefix.code,Option.map_some,
          ExactPhysicalProgram.output_some,word,leftCfg,Program.final,Program.initial,
          Option.elim_none,rightCfg,Option.map_some] using hv
      · intro g
        rw [Experiment.mean_map,PhysicalPartialSequence.mean_const]
  choose u hu hum using next
  refine ⟨q.bind u,hq.bind u _ hu,?_⟩
  intro g
  rw [Experiment.mean_bind]
  simp_rw [hum]
  exact (hqm g).trans (hpm g)

theorem prefix_correct_oai (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements program.table (output r c)
      (program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := middle_prefix r c htotal N
  have hi : ∀ a∈ExactTablePrefix.input r c,a≠0 := by
    intro a ha
    exact GreedyFeasibleTable.encodeMargins_nonzero r c a ha
  obtain ⟨u,hu,hum,_⟩ := LiteralProgram.pack_realizes (ExactTablePrefix.input r c) hi
  obtain ⟨v,hv,hvm,_⟩ := PhysicalPartialSequence.left_prefix LiteralProgram.pack.table middle.table
    middle.entry LiteralProgram.pack.final _ u hu
  have hall : v.All (fun x => x=LiteralProgram.pack.final
      (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) := by
    rw [Experiment.all_indicator,hvm,hum]
    simp only [Experiment.mean,ite_true, if_true]
  have hp' := hp.right (M := LiteralProgram.pack.table) middle.entry
  refine ⟨v.bind (fun _ => p),?_,?_⟩
  · apply hv.bind_all (fun _ => p) (output r c)
    exact hall.mono (by intro x hx; rw [hx]; exact hp')
  · intro g
    rw [Experiment.mean_bind,PhysicalPartialSequence.mean_const]
    exact hpm g

end
end ContingencyTables.ExactPublicPrefix

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.ExactPublicPrefix.prefix_correct_oai := @OAI.ContingencyTables.ExactPublicPrefix.prefix_correct_oai

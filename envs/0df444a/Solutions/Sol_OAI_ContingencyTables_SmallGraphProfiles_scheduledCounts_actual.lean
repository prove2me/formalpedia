-- Prove2me | solution 1 for OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:44:41.902703+00:00
-- url     : https://prove2.me/submissions/a71f14ae-148d-4c1d-b29d-ce0ea4a0481f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridAdjacency
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual axis neighbours and the `2q` proposal-degree bound -/

namespace ContingencyTables.GridBoundary

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] {K : ℕ}

omit [Fintype I] [DecidableEq I] in
theorem neighbor_ne (a b : Grid (I := I) K) (h : Neighbor a b) : a ≠ b := by
  rintro rfl
  obtain ⟨i, sign, hs⟩ := h
  cases sign
  · have hh : corner a i = corner a i + 1 := hs.1
    omega
  · have hh : corner a i = corner a i + 1 := hs.1
    omega

end

end ContingencyTables.GridBoundary

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))

lemma stateCode_injective : Function.Injective (stateCode r c e) := by
  intro x y h
  have he := congrArg (decodeStateCode r c e) h
  rw [decode_stateCode,decode_stateCode] at he
  exact Option.some.inj he

end
end ContingencyTables.SmallGraphProfiles

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

end
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSuccessCounts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One entry per accepted dense table, with no trial-fibre enumeration -/

namespace ContingencyTables.GridBoundary
open FairBits
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The unique bin-offset trial for a table supplies its entire success
count. This removes a sum over all trials from each output lookup. -/
theorem denseTrial_success_count (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I×J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (X : Table R P) :
    ((denseTrialCounts R P d hd hR hP e h a).push (trialSuccess R P d e htotal)).count
      (some X)=
    (denseTrialCounts R P d hd hR hP e h a).count (tableTrial R P d hd hR hP e X) := by
  change (∑ t,if trialSuccess R P d e htotal t=some X then
    (denseTrialCounts R P d hd hR hP e h a).count t else 0)=_
  simp_rw [trialSuccess_some_iff R P d hd hR hP e htotal]
  simp

/-- Evaluation uses one propagated bin numerator and one product of
closed-form offset counts; it never enumerates the acceptance bits. -/
theorem denseTrial_table_count (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I×J ≃ Fin q) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (X : Table R P) :
    (denseTrialCounts R P d hd hR hP e h a).count (tableTrial R P d hd hR hP e X)=
      IntegerPropagation.numerators (denseTransitionCount R P d e) a (d^50*(h+1)^2)
        (tableTrial R P d hd hR hP e X).1 *
      ∏ j : Fin q,OffsetCountPrograms.offsetCount
        ((integerWidth R P d (e.symm j),
          2^offsetBitLength (integerWidth R P d (e.symm j)) h d),
          ((offsetCoordinateEquiv e (integerWidth R P d)).symm
            (tableTrial R P d hd hR hP e X).2 j).val) := rfl

end
end ContingencyTables.GridBoundary

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialSemantics
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

end
end ContingencyTables.DensePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTableCoordinates
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the unique bin and offset of an accepted table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms
open scoped BigOperators Classical

lemma tableFreeValue_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) (i : Fin m) (j : Fin n) :
    tableFreeValue (tableCoordinatesCode R P d X,(i.val,j.val))=X.val (some i) (some j) := by
  exact tableOutput_entry R P X (some i) (some j)

lemma tableCellWidth_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) (i : Fin m) (j : Fin n) :
    gridCellWidth (tableCoordinatesCode R P d X,(i.val,j.val))=integerWidth R P d (i,j) := by
  have hr := marginCode_getD R (some i)
  have hc := marginCode_getD P (some j)
  change (marginCode R).getD (i.val+1) 0=R (some i) at hr
  change (marginCode P).getD (j.val+1) 0=P (some j) at hc
  simp only [gridCellWidth,shiftedCell,exponentCellData,tableCoordinatesCode,hr,hc]
  rfl

lemma tableBinCoordinate_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) (i : Fin m) (j : Fin n) :
    tableBinCoordinate (tableCoordinatesCode R P d X,(i.val,j.val))=
      (corner (tableTrial R P d hd hR hP finProdFinEquiv X).1
        (finProdFinEquiv (i,j))).toNat := by
  rw [tableBinCoordinate,tableFreeValue_code,tableCellWidth_code]
  change _ = X.val (some ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm
    (finProdFinEquiv (i,j))).1)
    (some (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2)/
      integerWidth R P d (finProdFinEquiv.symm (finProdFinEquiv (i,j)))
  rw [Equiv.symm_apply_apply]

lemma tableOffsetCoordinate_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) (i : Fin m) (j : Fin n) :
    tableOffsetCoordinate (tableCoordinatesCode R P d X,(i.val,j.val))=
      ((tableTrial R P d hd hR hP finProdFinEquiv X).2 (i,j)).val := by
  rw [tableOffsetCoordinate,tableFreeValue_code,tableCellWidth_code]
  rfl

lemma tableFreeCells_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableFreeCells (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      (((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1.val,
        (finProdFinEquiv.symm v).2.val)) := by
  simp only [tableFreeCells,freeCells,tableCoordinatesCode,marginCode,List.tail_cons]
  exact cellPairs_ofFn _ _

lemma tableBinCoordinates_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) :
    tableBinCoordinates (tableCoordinatesCode R P d X)=
      gridNatCode (tableTrial R P d hd hR hP finProdFinEquiv X).1 := by
  rw [tableBinCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  have he := tableBinCoordinate_code R P hd hR hP X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2
  simpa only [Function.comp_apply,Prod.mk.eta,Equiv.apply_symm_apply] using he

lemma tableOffsetCoordinates_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (X : Table R P) :
    tableOffsetCoordinates (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      ((tableTrial R P d hd hR hP finProdFinEquiv X).2 (finProdFinEquiv.symm v)).val) := by
  rw [tableOffsetCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact tableOffsetCoordinate_code R P hd hR hP X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2

lemma tableWidths_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableWidths (tableCoordinatesCode R P d X)=List.ofFn (fun v : Fin (m*n) =>
      integerWidth R P d (finProdFinEquiv.symm v)) := by
  rw [tableWidths,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  exact tableCellWidth_code R P d X
    ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1
    (finProdFinEquiv.symm v).2

lemma tableOffsetLengths_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d h : ℕ) (X : Table R P) :
    offsetLengths (tableCoordinatesCode R P d X,h)=List.ofFn (fun v : Fin (m*n) =>
      FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm v)) h d) := by
  change (tableFreeCells (tableCoordinatesCode R P d X)).map _=_
  rw [tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  unfold offsetLength
  dsimp only [Function.comp_apply]
  rw [tableCellWidth_code]
  rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawSemantics
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

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma iterate_succ (N : ℕ) (B : List (List ℕ)) (v : List ℕ) :
    iterate (N+1,(B,v))=iterate (N,(B,propagate (B,v))) := rfl

lemma dot_nil (b : List ℕ) : dot ([],b)=0 := by simp [dot]

lemma dot_cons (a : ℕ) (v b : List ℕ) :
    dot (a::v,b)=a*b.headD 0+dot (v,b.tail) := by
  have hzero : b.getD 0 0=b.headD 0 := by cases b <;> rfl
  simp only [dot,List.length_cons,List.sum_range_succ',List.getD_cons_zero]
  rw [hzero]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  cases b <;> simp

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NatListEquality
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list equality for matching tabulated states and outputs -/

namespace ContingencyTables.NatListEquality
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem listEqual_true (xs ys : List ℕ) : listEqual (xs,ys)=true ↔ xs=ys := by
  simp only [listEqual,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · rintro ⟨hlen,h⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have hv:=of_decide_eq_true (h i (List.mem_range.mpr hi))
    simpa only [atEqual,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj,Option.getD_some] using hv
  · intro h
    subst ys
    exact ⟨rfl,fun _ _ => by simp [atEqual]⟩

end ContingencyTables.NatListEquality

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AxisProposalTest
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing dense adjacency by the polynomial list of signed directions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary

theorem axisNumberStep_eq {q K M : ℕ} (a : Grid (I := Fin q) K) (v : Fin M) :
    axisNumberStep ((K,gridNatCode a),v.val)=(axisCodeStep a v).map gridNatCode := by
  change axisListStep (((K,gridNatCode a),v.val/2),decide (v.val%2=1))=_
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

lemma gridNatCode_injective {q K : ℕ} : Function.Injective (gridNatCode (q := q) (K := K)) := by
  intro a b h
  have hv:=List.ofFn_injective h
  funext i
  apply Subtype.ext
  have hi:=congrFun hv i
  change (corner a i).toNat=(corner b i).toNat at hi
  have ha: 0 ≤ corner a i := (a i).property.1
  have hb: 0 ≤ corner b i := (b i).property.1
  change corner a i=corner b i
  have hv:=congrArg (fun n : ℕ => (n:ℤ)) hi
  simpa only [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb] using hv

theorem hasProposal_code {q K : ℕ} (a b : Grid (I := Fin q) K) :
    hasProposal ((K,gridNatCode a),gridNatCode b)=true ↔ Neighbor a b := by
  simp only [hasProposal,List.any_eq_true]
  constructor
  · rintro ⟨v,hv,h⟩
    have hlen : v<2*q := by simpa [proposalIndices,gridNatCode] using hv
    rw [proposalMatches,axisNumberStep_eq a (⟨v,by omega⟩ : Fin (2*q))] at h
    cases he:axisCodeStep a (⟨v,by omega⟩ : Fin (2*q)) with
    | none => simp [he] at h
    | some c =>
      have hc : gridNatCode c=gridNatCode b :=
        (NatListEquality.listEqual_true _ _).mp (by simpa [he] using h)
      have hcb:=gridNatCode_injective hc
      subst c
      exact axisCodeStep_sound a b _ he
  · intro h
    obtain ⟨v,hv⟩:=axisCodeStep_exists (le_refl (q*2)) a b h
    refine ⟨v.val,?_,?_⟩
    · simpa only [proposalIndices,List.mem_range,gridNatCode,List.length_ofFn,Nat.mul_comm] using v.isLt
    · rw [proposalMatches,axisNumberStep_eq a v,hv]
      simpa only [Option.map_some,Option.elim_some] using
        (NatListEquality.listEqual_true _ _).mpr rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable dense off-diagonal counts without acceptance-word enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped Classical

theorem offCountCode_eq {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    offCountCode ((((marginCode R,marginCode P),gridNatCode a),d),gridNatCode b)=
      if Neighbor a b then
        2^(8*d^5-(denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a))
      else 0 := by
  unfold offCountCode countProposalInput countPowerInput replaceFlat
  rw [BinaryPowerPrograms.power_eq,flatExponent_code,flatExponent_code]
  by_cases h : Neighbor a b
  · simp [(hasProposal_code a b).mpr h,h]
  · have hp : hasProposal ((4*d^8,gridNatCode a),gridNatCode b)=false :=
      Bool.eq_false_iff.mpr (fun he => h ((hasProposal_code a b).mp he))
    simp [hp,h]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedPowerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reusing a unary allowance across a binary transition table -/

namespace ContingencyTables.BoundedPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem power_eq (xs : List Bool) (gap : ℕ) : power (xs,gap)=2^(xs.length-gap) :=
  BinaryPowerPrograms.power_eq 2 (xs.length-gap)

end ContingencyTables.BoundedPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedDenseCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial transition entries with a shared acceptance allowance -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma preparedOffCount_eq (xs : List Bool) (z : CountInput) (h : xs.length=8*z.1.2^5) :
    preparedOffCount (xs,z)=offCountCode z := by
  unfold preparedOffCount offCountCode
  simp only [BoundedPowerPrograms.power_eq,BinaryPowerPrograms.power_eq,preparedGap,
    countPowerInput,h]

lemma offCountCode_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    offCountCode ((((marginCode R,marginCode P),gridNatCode a),d),gridNatCode b)=
      FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
  rw [offCountCode_eq]
  by_cases hba : b=a
  · subst b
    have hn : ¬Neighbor a a := fun h => neighbor_ne a a h rfl
    simp [FiniteAcceptCounts.offCount,hn]
  · simp only [FiniteAcceptCounts.offCount,ite_eq_right hba]
    rw [axisCodeStep_count (dense_proposal_code_bound d (m*n) hq)]
    split_ifs <;> simp

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual dense transition matrix from its finite states -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma rowEntry_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs : List Bool) (hxs : xs.length=8*d^5)
    (a b : Grid (I := Fin (m*n)) (4*d^8)) :
    rowEntry (((((xs,2^denseStepBits d),
      (((marginCode R,marginCode P),gridNatCode a),d)),
      List.ofFn (fun i => gridNatCode (e i)))),gridNatCode b)=
        denseTransitionCount R P d finProdFinEquiv a b := by
  have hoff (b : Grid (I := Fin (m*n)) (4*d^8)) :
      rowOffEntry (((((xs,2^denseStepBits d),
        (((marginCode R,marginCode P),gridNatCode a),d)),
        List.ofFn (fun i => gridNatCode (e i)))),gridNatCode b)=
      FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
    unfold rowOffEntry
    rw [preparedOffCount_eq xs _ hxs]
    exact offCountCode_actual R P hq a b
  have hs : (rowOffCounts ((((xs,2^denseStepBits d),
      (((marginCode R,marginCode P),gridNatCode a),d)),
      List.ofFn (fun i => gridNatCode (e i))))).sum=
      ∑ b,FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) b := by
    simp only [rowOffCounts,List.map_ofFn,Function.comp_apply,hoff,List.sum_ofFn]
    exact e.sum_comp _
  have he : NatListEquality.listEqual (gridNatCode a,gridNatCode b)=true ↔ a=b := by
    rw [NatListEquality.listEqual_true]
    exact ⟨fun h => gridNatCode_injective h,fun h => congrArg gridNatCode h⟩
  unfold rowEntry denseTransitionCount FiniteAcceptCounts.row
  rw [hs,hoff]
  by_cases hab : a=b
  · subst b
    have hh : FiniteAcceptCounts.offCount a
        (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
        (fun b => denseExponent R P d finProdFinEquiv b-
          denseExponent R P d finProdFinEquiv a) (8*d^5) a=0 := by
      simp [FiniteAcceptCounts.offCount]
    simp [he,hh,FiniteAcceptCounts.denominator,denseStepBits,pow_add]
  · have hh : NatListEquality.listEqual (gridNatCode a,gridNatCode b)=false :=
      Bool.eq_false_iff.mpr (fun h => hab (he.mp h))
    simp [hh,Ne.symm hab]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial assembly of the dense count matrix in column order -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma countMatrix_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs : List Bool) (hxs : xs.length=8*d^5) :
    countMatrix ((((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),
      List.ofFn (fun i => gridNatCode (e i))))=
        List.ofFn (fun j => List.ofFn (fun i =>
          denseTransitionCount R P d finProdFinEquiv (e i) (e j))) := by
  simp only [countMatrix,countColumn,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  exact rowEntry_actual R P hq e xs hxs (e i) (e j)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary matrix propagation of the implemented dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma initialVector_actual {m n d N : ℕ}
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8)) (start : Fin N) :
    initialVector (List.ofFn (fun i => gridNatCode (e i)),gridNatCode (e start))=
      List.ofFn (fun i => if i=start then 1 else 0) := by
  simp only [initialVector,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have he : NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=true ↔
      i=start := by
    rw [NatListEquality.listEqual_true]
    constructor
    · intro h
      exact (e.injective (gridNatCode_injective h)).symm
    · rintro rfl
      rfl
  change (if NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=true
    then (1:ℕ) else 0)=(if i=start then 1 else 0)
  by_cases hi : i=start
  · simp only [ite_eq_left (he.mpr hi),ite_eq_left hi]
  · have hh : NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=false :=
      Bool.eq_false_iff.mpr (fun h => hi (he.mp h))
    simp [hh,hi]

private lemma numerators_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (M : B → B → ℕ)
    (start : A) (N : ℕ) (y : A) :
    IntegerPropagation.numerators (fun x y => M (e x) (e y)) start N y=
      IntegerPropagation.numerators M (e start) N (e y) := by
  induction N generalizing y with
  | zero => simp [IntegerPropagation.numerators,e.injective.eq_iff]
  | succ N ih =>
    simp only [IntegerPropagation.numerators,ih]
    exact e.sum_comp (fun x => IntegerPropagation.numerators M (e start) N x*M x (e y))

/-- The matrix is the count matrix of the actual Boolean walk, including
all rejected proposals and unused proposal codes. -/
theorem matrixWalk_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs steps : List Bool) (hxs : xs.length=8*d^5) (start : Fin N) :
    matrixWalk ((steps,(((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),
      List.ofFn (fun i => gridNatCode (e i)))),gridNatCode (e start))=
      List.ofFn (fun i => IntegerPropagation.numerators
        (denseTransitionCount R P d finProdFinEquiv) (e start) steps.length (e i)) := by
  unfold matrixWalk matrixWalkInput
  rw [countMatrix_actual R P hq e xs hxs,initialVector_actual]
  rw [IntegerMatrixPrograms.iterate_ofFn]
  congr 1
  funext i
  exact numerators_reindex e _ start steps.length i

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UnaryMarkers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded unary loop markers used in tabulation -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma unaryMarkers_length (n : ℕ) : (unaryMarkers n).length=n := by
  simp only [unaryMarkers,List.length_map,List.length_range]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical dense-walk tabulation from binary margins and precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma tabulationDimensions_length (z : TabulationData) :
    (tabulationDimensions z).length=tabulationDimension z := by
  simp [tabulationDimensions,zeroGrid,cellPairs,tabulationDimension]

lemma tabulationDimension_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d h : ℕ) :
    tabulationDimension ((marginCode R,marginCode P),(d,h))=m*n := by
  simp [tabulationDimension,marginCode]

/-- The caller computes its grid, zero starting state and full iteration
schedule from the margins. No state list or probability oracle is supplied. -/
theorem tabulateDenseWalk_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d) (hd : 0<d) (h : ℕ) :
    tabulateDenseWalk ((marginCode R,marginCode P),(d,h))=
      List.ofFn (fun i => IntegerPropagation.numerators
        (denseTransitionCount R P d finProdFinEquiv)
        (canonicalOrigin (m*n) d hd) (d^50*(h+1)^2)
        (gridEnumeration (m*n) (4*d^8) i)) := by
  let e := gridEnumeration (m*n) (4*d^8)
  let start := e.symm (canonicalOrigin (m*n) d hd)
  have he : e start=canonicalOrigin (m*n) d hd := e.apply_symm_apply _
  have hdim : (tabulationDimensions ((marginCode R,marginCode P),(d,h))).length=m*n := by
    rw [tabulationDimensions_length,tabulationDimension_code]
  unfold tabulateDenseWalk tabulationInput enumeratedMatrixInput enumerationData
  simp only [tabulationCountInput,tabulationDenominator,tabulationDenominatorInput,
    BinaryPowerPrograms.power_eq]
  rw [gridWords_eq_length _ _ _ hdim,zeroGrid_code R P hd,←he]
  rw [matrixWalk_actual R P hq e _ _ (by simp [tabulationAllowance,unaryMarkers_length]) start]
  simp only [unaryMarkers_length,tabulationSteps,he,e]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

private lemma range_sum (f : ℕ → ℕ) (q : ℕ) :
    ((List.range q).map f).sum=∑ j : Fin q,f j.val := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.sum_range_succ,Fin.sum_univ_castSucc,ih]
    rfl

lemma gridIndex_ofFn {q K : ℕ} (f : Fin q → Fin K) :
    gridIndex (List.ofFn (fun i => (f i).val),K)=(finFunctionFinEquiv f).val := by
  unfold gridIndex gridIndexIndices
  rw [List.length_ofFn,range_sum,finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold gridIndexTerm gridIndexPowerInput clippedGridPower clippedGridPowerInput
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,List.length_map,
    List.length_ofFn,BinaryPowerPrograms.power_eq,dite_true,Option.getD_some]
  rw [min_eq_left (Nat.le_of_lt i.isLt)]

/-- The computed integer is exactly the position used by the state list. -/
theorem gridIndex_code {q K : ℕ} (a : Grid (I := Fin q) K) :
    gridIndex (gridNatCode a,K)=((gridEnumeration q K).symm a).val := by
  let f : Fin q → Fin K := fun i => (gridDigitEquiv K).symm (a i)
  have hcode : gridNatCode a=List.ofFn (fun i => (f i).val) := rfl
  rw [hcode,gridIndex_ofFn]
  rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedOffsetCount
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

lemma preparedOffsetFactor_ofFn {q : ℕ} (cap : List Bool) (w r o : Fin q → ℕ)
    (j : Fin q) (hr : r j ≤ cap.length) :
    preparedOffsetFactor ((((cap,List.ofFn w),List.ofFn r),List.ofFn o),j.val)=
      OffsetCountPrograms.offsetCount ((w j,2^r j),o j) := by
  unfold preparedOffsetFactor preparedOffsetInput
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  rw [BoundedPowerPrograms.power_eq,Nat.sub_sub_self hr]

private lemma range_prod (f : ℕ → ℕ) (q : ℕ) :
    ((List.range q).map f).prod=∏ j : Fin q,f j.val := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.prod_range_succ,Fin.prod_univ_castSucc,ih]
    rfl

theorem preparedOffsetProduct_ofFn {q : ℕ} (cap : List Bool) (w r o : Fin q → ℕ)
    (hr : ∀ j,r j ≤ cap.length) :
    preparedOffsetProduct (((cap,List.ofFn w),List.ofFn r),List.ofFn o)=
      ∏ j : Fin q,OffsetCountPrograms.offsetCount ((w j,2^r j),o j) := by
  unfold preparedOffsetProduct preparedOffsetIndices
  rw [List.length_ofFn,range_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact preparedOffsetFactor_ofFn cap w r o j (hr j)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing one accepted-table numerator from the cached bin vector -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

/-- The program computes the count of the unique accepted trial for this
table, using canonical walk tabulation. -/
theorem trialTableCount_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (h : ℕ)
    (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),
      FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d ≤ cap.length)
    (X : Table R P) :
    trialTableCount ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
      (tableCoordinatesCode R P d X,h))=
    (denseTrialCounts R P d hd hR hP finProdFinEquiv h
      (canonicalOrigin (m*n) d (by omega))).count
        (tableTrial R P d hd hR hP finProdFinEquiv X) := by
  unfold trialTableCount trialCountIndexInput trialCountOffsetInput
  change (tabulateDenseWalk ((marginCode R,marginCode P),(d,h))).getD
      (gridIndex (tableBinCoordinates (tableCoordinatesCode R P d X),4*d^8)) 0*
    preparedOffsetProduct (((cap,tableWidths (tableCoordinatesCode R P d X)),
      offsetLengths (tableCoordinatesCode R P d X,h)),
      tableOffsetCoordinates (tableCoordinatesCode R P d X))=_
  rw [tableBinCoordinates_code R P hd hR hP X,gridIndex_code,
    tableWidths_code,tableOffsetLengths_code,tableOffsetCoordinates_code R P hd hR hP X,
    preparedOffsetProduct_ofFn cap _ _ _ hcap,
    tabulateDenseWalk_actual R P hq (by omega) h]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,
    dite_true,Option.getD_some,Fin.eta,Equiv.apply_symm_apply]
  exact denseTrial_table_count R P d hd hR hP finProdFinEquiv h
    (canonicalOrigin (m*n) d (by omega)) X |>.symm

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoxCompletion
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating tables through their free entries -/

namespace ContingencyTables.BoxCompletion
open DenseAffine DensePrograms
open scoped BigOperators Classical
noncomputable section

lemma freeValues_encode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hN : (∑ i,R i)≤N) (X : Table R P) :
    freeValues (encode R P hN X)=fun ij => X.val (some ij.1) (some ij.2) := by
  funext ij
  simp only [freeValues,encode,Equiv.symm_apply_apply]

lemma decode_encode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (X : Table R P) :
    decode R P htotal N (encode R P hN X)=some X := by
  have he := integerTable_recover R P X.val X.property.1 X.property.2
  have hz : ∀ i j,0 ≤ integerTable R P (freeValues (encode R P hN X)) i j := by
    rw [freeValues_encode,he]
    exact fun _ _ => Int.natCast_nonneg _
  rw [decode,dite_eq_left hz]
  congr 1
  apply Subtype.ext
  funext i j
  simp only [naturalTable,freeValues_encode,he,Int.toNat_natCast]

/-- Each feasible table occurs at exactly one enumerated free vector. -/
theorem decode_eq_some {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (z : Box m n N) (X : Table R P) :
    decode R P htotal N z=some X ↔ z=encode R P hN X := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next hz =>
      have he := Option.some.inj h
      funext k
      apply Fin.ext
      have hv := congrArg (fun Y : Table R P =>
        Y.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2)) he
      simpa only [naturalTable_free,freeValues,Prod.mk.eta,
        Equiv.apply_symm_apply,encode] using hv
    next hz => cases h
  · rintro rfl
    exact decode_encode R P htotal hN X

lemma decode_elim_sum {A : Type*} [Fintype A] (y : Option A) (w : A → ℕ) :
    y.elim 0 w=∑ a,if y=some a then w a else 0 := by
  cases y <;> simp

/-- Summing over candidate completions counts each feasible table once,
and gives zero weight to every rejected completion. -/
theorem sum_decode {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j)
    (hN : (∑ i,R i)≤N) (w : Table R P → ℕ) :
    (∑ z : Box m n N,(decode R P htotal N z).elim 0 w)=∑ X,w X := by
  simp_rw [decode_elim_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  simp_rw [decode_eq_some R P htotal hN]
  simp

/-- The existing executable acceptance test returns the same optional
table as the finite enumeration used in the counting proof. -/
theorem acceptCompletion_eq {m n N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (z : Box m n N) :
    acceptCompletion ((marginCode R,marginCode P),
      matrixCode (fun i j => freeValues z (i,j)))=
      (decode R P htotal N z).map tableOutput := by
  by_cases hz : ∀ i j,0 ≤ integerTable R P (freeValues z) i j
  · have hv := (completionValid_code R P (fun i j => freeValues z (i,j))).mpr hz
    simp only [acceptCompletion,hv,ite_true, if_true,decode,dite_eq_left hz]
    rw [completedMatrix_code]
    rfl
  · have hv : completionValid ((marginCode R,marginCode P),
        matrixCode (fun i j => freeValues z (i,j)))≠true := by
      intro h
      exact hz ((completionValid_code R P _).mp h)
    simp only [acceptCompletion,hv,Bool.false_eq_true,ite_false,decode,dite_eq_right hz,
      Option.map_none]

end
end ContingencyTables.BoxCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

theorem completionCandidates_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) :
    completionCandidates (marginCode R,marginCode P)=
      List.ofFn (fun k : Fin (((∑ i,R i)+1)^(m*n)) =>
        (BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)).map tableOutput) := by
  have hsum : (marginCode R).sum=∑ i,R i := by
    simp only [marginCode,List.sum_cons,List.sum_ofFn,Fintype.sum_option]
  have hlen : ((zeroGrid (marginCode R,marginCode P)).map (fun _ => false)).length=m*n := by
    simp only [zeroGrid,List.length_map,cellPairs,List.length_range,marginCode,
      List.tail_cons,List.length_ofFn]
  unfold completionCandidates completionEnumerationData
  rw [hsum,gridWords_finFunctions _ (∑ i,R i) (m*n) hlen,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply,completionCandidate]
  rw [unflattenGrid_code]
  exact BoxCompletion.acceptCompletion_eq R P htotal (finFunctionFinEquiv.symm k)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCandidateCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accepted counts throughout the enumerated completion box -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

theorem candidateCount_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d ≤ cap.length)
    (o : Option (Table R P)) :
    candidateCount
      (((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
        ((marginCode R,marginCode P),(d,h))),o.map tableOutput)=
      o.elim 0 (fun X => (denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).count
          (tableTrial R P d hd hR hP finProdFinEquiv X)) := by
  cases o with
  | none => rfl
  | some X => exact trialTableCount_actual R P hd hq hR hP h cap hcap X

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RetryNumeratorProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

private lemma iterate_eq (B : List (List ℕ)) (v : List ℕ) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,(B,v))=
      ((fun v => IntegerMatrixPrograms.propagate (B,v))^[N]) v := by
  induction N generalizing v with
  | zero => rfl
  | succ N ih =>
    rw [IntegerMatrixPrograms.iterate_succ,ih,Function.iterate_succ_apply]

private lemma propagate_two (Q phi alpha x y : ℕ) :
    IntegerMatrixPrograms.propagate ([[phi,alpha],[0,Q]],[x,y])=
      [phi*x+alpha*y,Q*y] := by
  simp [IntegerMatrixPrograms.propagate,IntegerMatrixPrograms.dot_cons,
    IntegerMatrixPrograms.dot_nil,Nat.mul_comm]

lemma count_eq (xs : List Bool) (Q phi alpha : ℕ) (hit : Bool) :
    count (xs,((Q,phi),(alpha,hit)))=
      recurrence Q phi alpha (if hit then 1 else 0) xs.length := by
  have hiter (N initial : ℕ) :
      ((fun v => IntegerMatrixPrograms.propagate ([[phi,alpha],[0,Q]],v))^[N]) [initial,1]=
        [recurrence Q phi alpha initial N,Q^N] := by
    induction N with
    | zero => simp [recurrence]
    | succ N ih =>
      rw [Function.iterate_succ_apply',ih,propagate_two]
      simp only [recurrence,pow_succ]
      rw [Nat.mul_comm Q (Q^N)]
  unfold count setup
  rw [iterate_eq,hiter]
  rfl

lemma recurrence_retry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (p : IntegerLaw (Option A) Q) (fallback x : A) (N : ℕ) :
    recurrence Q (p.count none) (p.count (some x)) (if x=fallback then 1 else 0) N=
      IntegerLaw.retryCount p fallback N x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [recurrence,ih,IntegerLaw.retryCount]
    exact Nat.add_comm _ _

end ContingencyTables.RetryNumeratorPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_VectorRetryProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma failure_ofFn {r Q : ℕ} (p : IntegerLaw (Option (Fin r)) Q)
    (xs : List Bool) (fallback : Fin r) :
    failure ((xs,Q),(List.ofFn (fun a => p.count (some a)),fallback.val))=p.count none := by
  have ht := p.total
  rw [Fintype.sum_option] at ht
  simp only [failure,List.sum_ofFn]
  omega

theorem counts_actual {r Q : ℕ} (p : IntegerLaw (Option (Fin r)) Q)
    (xs : List Bool) (fallback : Fin r) :
    counts ((xs,Q),(List.ofFn (fun a => p.count (some a)),fallback.val))=
      List.ofFn ((p.retry fallback xs.length).count) := by
  unfold counts indices
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro j hj _
    have hjr : j < r := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold entryInput
    rw [failure_ofFn]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjr,dite_true,
      Option.getD_some]
    rw [RetryNumeratorPrograms.count_eq]
    have hhit : (j=fallback.val) ↔ (⟨j,hjr⟩ : Fin r)=fallback :=
      ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [decide_eq_true_eq,hhit]
    exact RetryNumeratorPrograms.recurrence_retry p fallback ⟨j,hjr⟩ xs.length

end ContingencyTables.VectorRetryPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IndexedTableLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding accepted-table laws into the computed completion list -/

namespace ContingencyTables.IndexedTableLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)

lemma tableAt_eq_some (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (k : Index m n N) (X : Table R P) :
    tableAt R P htotal k=some X ↔ index R P hN X=k := by
  rw [tableAt,BoxCompletion.decode_eq_some R P htotal hN]
  constructor
  · intro h
    have he := congrArg finFunctionFinEquiv h
    simpa only [Equiv.apply_symm_apply,index] using he.symm
  · intro h
    rw [←h,index,Equiv.symm_apply_apply]

lemma tableAt_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (X : Table R P) : tableAt R P htotal (index R P hN X)=some X :=
  (tableAt_eq_some R P htotal hN _ X).mpr rfl

lemma index_eq_iff (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (X Y : Table R P) : index R P hN X=index R P hN Y ↔ X=Y := by
  constructor
  · intro h
    have he := congrArg (tableAt R P htotal) h
    rw [tableAt_index,tableAt_index] at he
    exact Option.some.inj he
  · rintro rfl
    rfl

lemma count_none (hN : (∑ i,R i)≤N) (p : IntegerLaw (Option (Table R P)) Q) :
    (law R P hN p).count none=p.count none := by
  simp [law,IntegerLaw.push,Fintype.sum_option]

/-- Invalid completions have zero count; every valid completion has
exactly the count of its unique feasible table. -/
lemma count_some (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (k : Index m n N) :
    (law R P hN p).count (some k)=
      (tableAt R P htotal k).elim 0 (fun X => p.count (some X)) := by
  simp only [law,IntegerLaw.push,Fintype.sum_option,Option.map_none,reduceCtorEq,
    ite_false,zero_add,Option.map_some,Option.some.injEq]
  simp_rw [←tableAt_eq_some R P htotal hN]
  cases tableAt R P htotal k <;> simp

lemma count_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (X : Table R P) :
    (law R P hN p).count (some (index R P hN X))=p.count (some X) := by
  rw [count_some R P htotal,tableAt_index]
  rfl

/-- Embedding tables into the explicit finite candidate list commutes
with every bounded first-success retry. -/
theorem retry_count_index (htotal : ∑ i,R i=∑ j,P j) (hN : (∑ i,R i)≤N)
    (p : IntegerLaw (Option (Table R P)) Q) (fallback X : Table R P) (J : ℕ) :
    ((law R P hN p).retry (index R P hN fallback) J).count (index R P hN X)=
      (p.retry fallback J).count X := by
  change IntegerLaw.retryCount (law R P hN p) (index R P hN fallback) J (index R P hN X)=
    IntegerLaw.retryCount p fallback J X
  induction J with
  | zero => simp only [IntegerLaw.retryCount,index_eq_iff R P htotal]
  | succ J ih =>
    rw [IntegerLaw.retryCount,IntegerLaw.retryCount,count_index R P htotal,count_none,ih]

end
end ContingencyTables.IndexedTableLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIndexedCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete indexed integer law of a bounded dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical
noncomputable section

theorem candidateCounts_indexed {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d ≤ cap.length) :
    candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
      ((marginCode R,marginCode P),(d,h)))=
    List.ofFn (fun k => (IndexedTableLaw.law R P (le_refl (∑ i,R i))
      ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).push
          (trialSuccess R P d finProdFinEquiv htotal))).count (some k)) := by
  unfold candidateCounts
  rw [completionCandidates_code R P htotal,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  simp only [Function.comp_apply]
  rw [candidateCount_actual R P hd hq hR hP h cap hcap,
    IndexedTableLaw.count_some R P htotal]
  unfold IndexedTableLaw.tableAt
  simp_rw [denseTrial_success_count R P d hd hR hP finProdFinEquiv htotal]

/-- Full retry numerators are obtained by the polynomial binary vector
recurrence, after the accepted-trial vector has been tabulated once. -/
theorem denseRetryVector_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap xs : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d ≤ cap.length)
    (fallback : Table R P) :
    VectorRetryPrograms.counts ((xs,2^denseTrialBits R P d finProdFinEquiv h),
      (candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
        ((marginCode R,marginCode P),(d,h))),
        (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback).val))=
    List.ofFn (((IndexedTableLaw.law R P (le_refl (∑ i,R i))
      ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).push
          (trialSuccess R P d finProdFinEquiv htotal))).retry
            (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback) xs.length).count) := by
  rw [candidateCounts_indexed R P hd hq hR hP htotal h cap hcap]
  exact VectorRetryPrograms.counts_actual _ xs _

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

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TableIndexProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the position of a table in the completion enumeration -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma tableFreeCoordinates_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d : ℕ) (X : Table R P) :
    tableFreeCoordinates (tableCoordinatesCode R P d X)=
      List.ofFn (fun k : Fin (m*n) =>
        X.val (some (finProdFinEquiv.symm k).1) (some (finProdFinEquiv.symm k).2)) := by
  rw [tableFreeCoordinates,tableFreeCells_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  exact tableFreeValue_code R P d X _ _

theorem tableIndex_actual {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (X : Table R P) :
    tableIndex ((marginCode R,marginCode P),tableOutput X)=
      (IndexedTableLaw.index R P (le_refl (∑ i,R i)) X).val := by
  unfold tableIndex tableIndexInput
  change gridIndex (tableFreeCoordinates (tableCoordinatesCode R P 0 X),
    (marginCode R).sum+1)=_
  rw [tableFreeCoordinates_code]
  have hsum : (marginCode R).sum=∑ i,R i := by
    simp only [marginCode,List.sum_cons,List.sum_ofFn,Fintype.sum_option]
  rw [hsum]
  change gridIndex (List.ofFn (fun k =>
    (BoxCompletion.encode R P (le_refl (∑ i,R i)) X k).val),(∑ i,R i)+1)=_
  rw [gridIndex_ofFn]
  rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawTabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the full integer law of an initialized dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma rawTrialBits_code {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 0<d) (h : ℕ) :
    rawTrialBits ((marginCode R,marginCode P),(d,h))=
      denseTrialBits R P d finProdFinEquiv h := by
  unfold rawTrialBits rawDrawParameters
  rw [zeroGrid_code R P hd]
  exact trialWidth_code R P h _

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSuppliedFallback
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense law tabulation retains the supplied feasible fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

/-- The fallback is transported by the caller's normalization, rather
than being recomputed in the normalized margin order. -/
theorem suppliedDrawCounts_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (fallback : Table R P) :
    suppliedDrawCounts (((marginCode R,marginCode P),(d,h)),tableOutput fallback)=
      List.ofFn (((IndexedTableLaw.law R P (le_refl (∑ i,R i))
        ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
          (canonicalOrigin (m*n) d (by omega))).push
            (trialSuccess R P d finProdFinEquiv htotal))).retry
        (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback) (d^4*(h+1))).count) := by
  have hc : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤
        (unaryMarkers (denseTrialBits R P d finProdFinEquiv h)).length := by
    intro j
    rw [unaryMarkers_length]
    have hs : FairBits.offsetBitLength (integerWidth R P d (finProdFinEquiv.symm j)) h d≤
        ∑ k : Fin (m*n),FairBits.offsetBitLength
          (integerWidth R P d (finProdFinEquiv.symm k)) h d :=
      Finset.single_le_sum
        (f := fun k : Fin (m*n) => FairBits.offsetBitLength
          (integerWidth R P d (finProdFinEquiv.symm k)) h d)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact hs.trans (by unfold denseTrialBits; omega)
  unfold suppliedDrawCounts suppliedVectorInput replaceVectorFallback rawVectorInput rawCountContext
  rw [rawTrialBits_code (d := d) R P (show 0<d by omega),
    BinaryPowerPrograms.power_eq,tableIndex_actual]
  have he := denseRetryVector_actual R P hd hq hR hP htotal h
    (unaryMarkers (denseTrialBits R P d finProdFinEquiv h))
    (unaryMarkers (rawRepeat ((marginCode R,marginCode P),(d,h)))) hc fallback
  rw [unaryMarkers_length] at he
  simpa only [rawRepeat] using he

theorem suppliedDrawCounts_at {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (fallback X : Table R P) :
    (suppliedDrawCounts (((marginCode R,marginCode P),(d,h)),tableOutput fallback)).getD
      (tableIndex ((marginCode R,marginCode P),tableOutput X)) 0=
    (denseDrawCounts R P d hd hR hP finProdFinEquiv htotal h
      (canonicalOrigin (m*n) d (by omega)) fallback).count X := by
  rw [suppliedDrawCounts_actual R P hd hq hR hP htotal,tableIndex_actual]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,dite_true,
    Option.getD_some,Fin.eta]
  exact IndexedTableLaw.retry_count_index R P htotal (le_refl (∑ i,R i)) _
    fallback X (d^4*(h+1))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CanonicalDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dense counts after computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

attribute [local irreducible] canonicalCountInputRealizer suppliedDrawCountsRealizer

lemma canonicalCountInput_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (d h : ℕ) :
    canonicalCountInput ((marginCode R,marginCode P),(d,h))=
      (((marginCode (normalizedMargin R),marginCode (normalizedMargin P)),(d,h)),
        tableOutput (tableReindex (indexPermutation (marginPosition R))
          (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))) := by
  unfold canonicalCountInput swapMargins marginIndices
  rw [←marginPosition_val,←marginPosition_val,marginCode_swap,marginCode_swap,
    ←canonicalFallback_output R P htotal,tableOutput_swap]
  rfl

lemma canonicalTableIndex_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (htotal : ∑ i,R i=∑ j,P j) (d h : ℕ) (X : Table R P) :
    canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)=
      (IndexedTableLaw.index (normalizedMargin R) (normalizedMargin P)
        (le_refl (∑ i,normalizedMargin R i))
        (tableReindex (indexPermutation (marginPosition R))
          (indexPermutation (marginPosition P)) R P X)).val := by
  unfold canonicalTableIndex
  rw [canonicalCountInput_code R P htotal]
  simp only [marginIndices,←marginPosition_val]
  rw [tableOutput_swap]
  exact tableIndex_actual (normalizedMargin R) (normalizedMargin P) _

/-- The cached numerator is the count at the transported table, including
all fallback words of the actual normalized dense program. -/
theorem canonicalDrawCounts_at {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (X : Table R P) :
    (canonicalDrawCounts ((marginCode R,marginCode P),(d,h))).getD
      (canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)) 0=
    (denseDrawCounts (normalizedMargin R) (normalizedMargin P) d hd
      (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
      finProdFinEquiv (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
      (canonicalOrigin (m*n) d (by omega))
      (tableReindex (indexPermutation (marginPosition R))
        (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))).count
      (tableReindex (indexPermutation (marginPosition R))
        (indexPermutation (marginPosition P)) R P X) := by
  dsimp only [canonicalDrawCounts,Function.comp_apply]
  rw [canonicalCountInput_code R P htotal,canonicalTableIndex_code R P htotal]
  have he := suppliedDrawCounts_at (normalizedMargin R) (normalizedMargin P) hd hq
    (normalizedMargin_lower R _ hR) (normalizedMargin_lower P _ hP)
    (by rw [normalizedMargin_total,normalizedMargin_total]; exact htotal) h
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P (canonicalFallback R P htotal))
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P X)
  have hi := tableIndex_actual (normalizedMargin R) (normalizedMargin P)
    (tableReindex (indexPermutation (marginPosition R))
      (indexPermutation (marginPosition P)) R P X)
  dsimp only [normalizedMargin] at he hi ⊢
  rw [hi] at he
  exact he

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CanonicalIntegerLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite integer law of the normalized Boolean sampler -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

variable {m n d : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
variable (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
variable (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)

theorem canonicalCounts_computed (hq : m*n≤d) (X : Table R P) :
    (canonicalDrawCounts ((marginCode R,marginCode P),(d,h))).getD
      (canonicalTableIndex (((marginCode R,marginCode P),(d,h)),tableOutput X)) 0=
      (canonicalCounts R P hd hR hP htotal h).count X :=
  canonicalDrawCounts_at R P hd hq hR hP htotal h X

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedCompletionWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit table weights from the computed dense-law cache -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

attribute [local irreducible] canonicalDrawCounts canonicalCounts

lemma cachedCompletionWeight_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (o : Option (Table R P)) :
    cachedCompletionWeight ((((marginCode R,marginCode P),(d,h)),
      canonicalDrawCounts ((marginCode R,marginCode P),(d,h))),o.map tableOutput)=
      o.elim 0 (fun X => (canonicalCounts R P hd hR hP htotal h).count X) := by
  cases o with
  | none => rfl
  | some X => exact canonicalCounts_computed R P hd hR hP htotal h hq X

/-- The explicit list contains every feasible table once. Each rejected
free vector has zero weight; the surviving weights are the actual draw counts. -/
theorem completionWeights_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ) :
    completionWeights ((marginCode R,marginCode P),(d,h))=
      List.ofFn (fun k : Fin (((∑ i,R i)+1)^(m*n)) =>
        let o := BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)
        (o.map tableOutput,o.elim 0 (fun X => (canonicalCounts R P hd hR hP htotal h).count X))) := by
  unfold completionWeights
  rw [completionCandidates_code R P htotal,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  congr 1
  exact cachedCompletionWeight_actual R P hd hq hR hP htotal h _

end ContingencyTables.DensePrograms

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

end
end ContingencyTables.SmallGraphProfiles

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


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedDecisionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cached completions implement the same outer-profile transition -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

/-- This identity holds for every feasible cached completion, including
those not selected by a particular finite random word. -/
theorem cachedDecision_encoded (htotal : ∑ i,r i=∑ j,c j) (h : ℕ)
    (x : PaperStates r c) (word : Fin s → Bool) (A : Table (R x) (P x)) :
    cachedDecision (encodedShortStep r c e h x word,tableOutput A)=
      stateCode r c e (completionDecision R P x (decodedCodeProposal r c e x word) A) := by
  have hp := codeProposal_encoded r c e htotal x word
  cases hd : decodedCodeProposal r c e x word with
  | none =>
    rw [hd,Option.map_none] at hp
    have hviews : stepCandidateViews (shortStepInput (encodedShortStep r c e h x word))=
        stateCode r c e x := by
      simp only [stepCandidateViews,stepProposal,shortStepInput,encodedShortStep,hp,
        Option.getD_none]
      rfl
    unfold cachedDecision
    rw [hviews]
    split_ifs <;> rfl
  | some y =>
    rw [hd,Option.map_some] at hp
    have hparams : stepCandidateParameters (shortStepInput (encodedShortStep r c e h x word))=
        ((stateCodeData r c e y,d^12),(d,h)) := by
      simp only [stepCandidateParameters,stepCandidate,stepCandidateViews,stepProposal,
        shortStepInput,encodedShortStep,hp,Option.getD_some]
      rfl
    have hdata : cachedDecisionInput (encodedShortStep r c e h x word,tableOutput A)=
        (((marginCode (R x),marginCode (P x)),(marginCode (R y),marginCode (P y))),
          tableOutput A) := by
      unfold cachedDecisionInput stepOldMargins stepNewMargins
      rw [hparams]
      dsimp only [shortStepInput,encodedShortStep]
      rw [residualParameters_code,residualParameters_code]
    have hviews : stepCandidateViews (shortStepInput (encodedShortStep r c e h x word))=
        stateCode r c e y := by
      simp only [stepCandidateViews,stepProposal,shortStepInput,encodedShortStep,hp,
        Option.getD_some]
    have hv := translationValid_code (R x) (R y) (P x) (P y) A
    unfold cachedDecision
    rw [hdata,hviews]
    change (if translationValid _ then stateCode r c e y else stateCode r c e x)=
      stateCode r c e (if ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
        then y else x)
    by_cases ht : ∀ i j,0 ≤ (A.val i j:ℤ)+between (R x) (R y) (P x) (P y) i j
    · rw [ite_eq_left ht,ite_eq_left (hv.mpr ht)]
    · rw [ite_eq_right ht,ite_eq_right (fun hv' => ht (hv.mp hv'))]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma booleanWords_of_length (xs : List Bool) (s : ℕ) (hs : xs.length=s) :
    booleanWords xs=List.ofFn (fun k => List.ofFn (booleanEnumeration s k)) := by
  unfold booleanWords
  rw [gridWords_finFunctions xs 1 s hs,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change digitBool ((finFunctionFinEquiv.symm k) i).val=
    finTwoEquiv ((finFunctionFinEquiv.symm k) i)
  have hb (a : Fin 2) : digitBool a.val=finTwoEquiv a := by
    fin_cases a <;> rfl
  exact hb _

lemma sum_booleanWords (xs : List Bool) (s : ℕ) (hs : xs.length=s)
    (w : List Bool → ℕ) :
    ((booleanWords xs).map w).sum=∑ bits : Fin s → Bool,w (List.ofFn bits) := by
  rw [booleanWords_of_length xs s hs,List.map_ofFn,List.sum_ofFn]
  exact (booleanEnumeration s).sum_comp (fun bits => w (List.ofFn bits))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedStepCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted transitions from the cached completion list -/

namespace ContingencyTables.DensePrograms
open scoped BigOperators Classical
noncomputable section

/-- Free-box enumeration sums each feasible table's weight once. -/
lemma sum_completionWeights {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (w : MatrixCode → ℕ) :
    ((completionWeights ((marginCode R,marginCode P),(d,h))).map
      (fun z => z.1.elim 0 (fun X => z.2*w X))).sum=
      ∑ X : Table R P,(canonicalCounts R P hd hR hP htotal h).count X*w (tableOutput X) := by
  rw [completionWeights_actual R P hd hq hR hP htotal h,List.map_ofFn,List.sum_ofFn]
  let f : BoxCompletion.Box m n (∑ i,R i) → ℕ := fun z =>
    (BoxCompletion.decode R P htotal (∑ i,R i) z).elim 0
      (fun X => (canonicalCounts R P hd hR hP htotal h).count X*w (tableOutput X))
  have hs := finFunctionFinEquiv.symm.sum_comp f
  have hi : (∑ k : Fin (((∑ i,R i)+1)^(m*n)),
      let o := BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k)
      (o.map tableOutput).elim 0 (fun X =>
        o.elim 0 (fun T => (canonicalCounts R P hd hR hP htotal h).count T)*w X))=
      ∑ z : BoxCompletion.Box m n (∑ i,R i),f z := by
    rw [←hs]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f]
    cases BoxCompletion.decode R P htotal (∑ i,R i) (finFunctionFinEquiv.symm k) <;> rfl
  exact hi.trans (BoxCompletion.sum_decode R P htotal le_rfl _)

end
end ContingencyTables.DensePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] canonicalCounts completionWeights decisionWeightSum

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma decisionWeightSum_actual (htotal : ∑ i,r i=∑ j,c j) (h : ℕ)
    (x y : PaperStates r c) (word : Fin s → Bool) :
    decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ∑ A : Table (R x) (P x),if completionDecision R P x (decodedCodeProposal r c e x word) A=y
        then (canonicalCounts (R x) (P x) (listed_dimension_fourteen r c hr hc)
          (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
          (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
          (listed_paper_totals r c hr hc x) h).count A else 0 := by
  let w : MatrixCode → ℕ := fun X =>
    if cachedDecision (encodedShortStep r c e h x word,X)=stateCode r c e y then 1 else 0
  have he : decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
        (fun z => z.1.elim 0 (fun X => z.2*w X))).sum := by
    unfold decisionWeightSum
    congr 1
    apply List.map_congr_left
    intro z _
    rcases z with ⟨o,a⟩
    cases o with
    | none => rfl
    | some X =>
      simp only [decisionWeight,Option.elim_some,w]
      split_ifs <;> simp
  rw [he,sum_completionWeights (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (by simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h w]
  apply Finset.sum_congr rfl
  intro A _
  simp only [w,cachedDecision_encoded r c e hr hc htotal h x word A,
    (stateCode_injective r c e).eq_iff]
  split_ifs <;> simp

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixCodeEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality of explicitly stored rectangular arrays -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

lemma matrixCode_injective {m n : ℕ} :
    Function.Injective (matrixCode (m := m) (n := n)) := by
  intro X Y h
  have hi := List.ofFn_injective h
  funext i
  exact List.ofFn_injective (congrFun hi i)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the short proposal words with a shared dense cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped BigOperators Classical

lemma transitionCount_words (z : TransitionCache×(List ℕ×List ℕ))
    (xs : List Bool) (s : ℕ) (hs : xs.length=s) :
    transitionCount (z,xs)=∑ bits : Fin s → Bool,cachedWordCount (z,List.ofFn bits) :=
  sum_booleanWords xs s hs _

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma booleanFinish_count {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {s f : ℕ} (p : IntegerLaw A (2^f)) (finish : (Fin s → Bool) → A → B) (b : B) :
    (booleanFinish p finish).count b=
      ∑ bits : Fin s → Bool,∑ a,if finish bits a=b then p.count a else 0 := by
  change (∑ z : (Fin s → Bool)×A,if finish z.1 z.2=b then 1*p.count z.2 else 0)=_
  rw [Fintype.sum_prod_type]
  simp only [one_mul]

end
end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedTransitionCache
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense cache and the unused-bit multiplicity -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

lemma completionMultiplicity_encoded (b h : ℕ) (x : PaperStates r c) :
    completionMultiplicity ((((stateCodeData r c e x,d^12),(d,h)),25*(d+b+h+1)^62))=
      2^(25*(d+b+h+1)^62-normalizedDrawBits (R x) (P x) d h) := by
  unfold completionMultiplicity
  rw [residualParameters_code r c hr hc e,BinaryPowerPrograms.power_eq,
    canonicalBitCount_code (R x) (P x) (by have := listed_dimension_fourteen r c hr hc; omega)
      (listed_paper_totals r c hr hc x)]

lemma prepareTransitionCache_encoded (b h : ℕ) (x : PaperStates r c) :
    prepareTransitionCache ((((stateCodeData r c e x,d^12),(d,h)),25*(d+b+h+1)^62))=
      (((stateCodeData r c e x,d^12),(d,h)),
        (2^(25*(d+b+h+1)^62-normalizedDrawBits (R x) (P x) d h),
          completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))) := by
  unfold prepareTransitionCache
  rw [completionMultiplicity_encoded r c e hr hc,
    residualParameters_code r c hr hc e]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedTerminalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact terminal counts from the retained dense-completion cache -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma terminalCount_eq (p : ResidualParameters) (M : ℕ)
    (entries : List (Option MatrixCode×ℕ)) (target : MatrixCode) :
    terminalCount ((p,(M,entries)),target)=
      M*(entries.map (fun entry => entry.1.elim 0
        (fun X => if outerTrial (p.1,X)=some target then entry.2 else 0))).sum := by
  unfold terminalCount terminalOutputs successfulWeightSum
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  rintro ⟨o,n⟩ _
  cases o with
  | none => rfl
  | some X =>
    simp only [Function.comp_apply,terminalOutputEntry,Option.bind_some,successfulWeight,
      Option.elim_some]
    cases outerTrial (p.1,X) with
    | none => rfl
    | some Y => simp only [Option.elim_some,Option.some.injEq]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanCountTransport
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A completion-coordinate change in the finite transition count -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma booleanFinish_equiv_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] {s f Q : ℕ} (p : IntegerLaw A (2^f)) (q : IntegerLaw B Q)
    (e : A ≃ B) (M : ℕ) (finish : (Fin s → Bool) → B → C)
    (h : ∀ a,p.count a=q.count (e a)*M) (c : C) :
    (booleanFinish p (fun bits a => finish bits (e a))).count c=
      ∑ bits : Fin s → Bool,∑ b,if finish bits b=c then q.count b*M else 0 := by
  rw [booleanFinish_count]
  simp_rw [h]
  apply Finset.sum_congr rfl
  intro bits _
  exact e.sum_comp (fun b : B => if finish bits b=c then q.count b*M else 0)

end
end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionCountSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed cached transitions have the actual walk's integer counts -/

namespace ContingencyTables.ProfilePrograms

lemma cachedWordCount_eq (p : ResidualParameters) (M : ℕ)
    (cache : List (Option DensePrograms.MatrixCode×ℕ)) (target : List ℕ×List ℕ)
    (bits : List Bool) :
    cachedWordCount (((p,(M,cache)),target),bits)=
      M*decisionWeightSum (((p,bits),target),cache) := rfl

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] canonicalCounts listedStepCounts listedCompletionCounts
  normalizedDrawBits prepareTransitionCache stateCode stateCodeData listedRows listedColumns
  completionDecision transitionCount cachedWordCount cachedWordInput completionWeights decisionWeightSum

attribute [local irreducible] listedUnpaddedCounts listedCompletionFactor listedCachedDecision

lemma listedCompletionCounts_count (x : PaperStates r c) (A : PaperFibre r c x) :
    (listedCompletionCounts r c hr hc b h hb x).count A=
      (listedUnpaddedCounts r c hr hc h x).count (paperListedEquiv r c hr hc x A)*
        listedCompletionFactor r c hr hc b h x := by
  unfold listedUnpaddedCounts listedCompletionFactor listedCompletionCounts
  rfl

lemma listedStepCounts_sum (x y : PaperStates r c) :
    (listedStepCounts r c e hr hc b h hb x).count y=
      ∑ word : Fin s → Bool,∑ A : Table (R x) (P x),
        if listedCachedDecision r c e hr hc x word A=y then
          (listedUnpaddedCounts r c hr hc h x).count A*
            listedCompletionFactor r c hr hc b h x else 0 := by
  have he := IntegerLaw.booleanFinish_equiv_count
    (listedCompletionCounts r c hr hc b h hb x) (listedUnpaddedCounts r c hr hc h x)
    (paperListedEquiv r c hr hc x) (listedCompletionFactor r c hr hc b h x)
    (listedCachedDecision r c e hr hc x)
    (listedCompletionCounts_count r c hr hc b h hb x) y
  simpa only [listedStepCounts,listedCachedDecision] using he

lemma decisionWeightSum_listed (htotal : ∑ i,r i=∑ j,c j)
    (x y : PaperStates r c) (word : Fin s → Bool) :
    decisionWeightSum ((encodedShortStep r c e h x word,stateCode r c e y),
      completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))=
      ∑ A : Table (R x) (P x),if listedCachedDecision r c e hr hc x word A=y
        then (listedUnpaddedCounts r c hr hc h x).count A else 0 := by
  unfold listedCachedDecision listedUnpaddedCounts
  exact decisionWeightSum_actual r c e hr hc htotal h x y word

lemma transitionCount_actual (htotal : ∑ i,r i=∑ j,c j)
    (x y : PaperStates r c) (xs : List Bool) (hs : xs.length=s) :
    transitionCount ((prepareTransitionCache
      ((((stateCodeData r c e x,d^12),(d,h)),f)),stateCode r c e y),xs)=
      (listedStepCounts r c e hr hc b h hb x).count y := by
  rw [prepareTransitionCache_encoded r c e hr hc,transitionCount_words _ xs s hs,
    listedStepCounts_sum r c e hr hc b h hb x y]
  apply Finset.sum_congr rfl
  intro word _
  rw [cachedWordCount_eq]
  have he := decisionWeightSum_listed r c e hr hc h htotal x y word
  unfold encodedShortStep at he
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold listedCompletionFactor
  split_ifs
  · exact Nat.mul_comm _ _
  · exact Nat.mul_zero _

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerPushTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Count transport through a completion-coordinate bijection -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma push_equiv_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] {P Q : ℕ} (p : IntegerLaw A P) (q : IntegerLaw B Q)
    (e : A ≃ B) (M : ℕ) (finish : B → C)
    (h : ∀ a,p.count a=q.count (e a)*M) (c : C) :
    (p.push (fun a => finish (e a))).count c=
      ∑ b,if finish b=c then q.count b*M else 0 := by
  change (∑ a,if finish (e a)=c then p.count a else 0)=_
  simp_rw [h]
  exact e.sum_comp (fun b : B => if finish b=c then q.count b*M else 0)

end
end ContingencyTables.IntegerLaw

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedTerminalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cached terminal success counts equal the actual completion law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] canonicalCounts listedCompletionCounts listedUnpaddedCounts
  listedCompletionFactor stateCode stateCodeData completionWeights prepareTransitionCache
  terminalCount listedRows listedColumns

lemma tableCode_option_eq (o : Option (Table r c)) (T : Table r c) :
    o.map (fun X => matrixCode X.val)=some (matrixCode T.val) ↔ o=some T := by
  cases o with
  | none => simp
  | some X =>
    simp only [Option.map_some,Option.some.injEq]
    constructor
    · intro he
      exact Subtype.ext (matrixCode_injective he)
    · rintro rfl
      rfl

attribute [local irreducible] listedTerminalDecision

lemma terminal_completion_sum (x : PaperStates r c) (T : Table r c) :
    ((listedCompletionCounts r c hr hc b h hb x).push
      (fun A => stateTrial r c ⟨x,A⟩)).count (some T)=
      ∑ A : Table (R x) (P x),if listedTerminalDecision r c hr hc x A=some T
        then (listedUnpaddedCounts r c hr hc h x).count A*
          listedCompletionFactor r c hr hc b h x else 0 := by
  have he := IntegerLaw.push_equiv_count
    (listedCompletionCounts r c hr hc b h hb x) (listedUnpaddedCounts r c hr hc h x)
    (paperListedEquiv r c hr hc x) (listedCompletionFactor r c hr hc b h x)
    (listedTerminalDecision r c hr hc x)
    (listedCompletionCounts_count r c hr hc b h hb x) (some T)
  simpa only [listedTerminalDecision,Equiv.symm_apply_apply] using he

lemma terminal_cache_sum (x : PaperStates r c) (T : Table r c) :
    ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
      (fun entry => entry.1.elim 0 (fun X =>
        if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val)
        then entry.2 else 0))).sum=
      ∑ A : Table (R x) (P x),if listedTerminalDecision r c hr hc x A=some T
        then (listedUnpaddedCounts r c hr hc h x).count A else 0 := by
  let w : MatrixCode → ℕ := fun X =>
    if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val) then 1 else 0
  have he : ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
      (fun entry => entry.1.elim 0 (fun X =>
        if outerTrial ((stateCodeData r c e x,d^12),X)=some (matrixCode T.val)
        then entry.2 else 0))).sum=
      ((completionWeights ((marginCode (R x),marginCode (P x)),(d,h))).map
        (fun entry => entry.1.elim 0 (fun X => entry.2*w X))).sum := by
    congr 1
    apply List.map_congr_left
    rintro ⟨o,n⟩ _
    cases o with
    | none => rfl
    | some X => simp only [Option.elim_some,w]; split_ifs <;> simp
  rw [he,sum_completionWeights (R x) (P x) (listed_dimension_fourteen r c hr hc)
    (by simpa only [Fintype.card_prod,Fintype.card_fin] using (listed_dimensions r c hr hc).2.2)
    (listed_row_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_column_padding r c (d^20) (d^12) (stateCapacity r c) hr hc x)
    (listed_paper_totals r c hr hc x) h w]
  apply Finset.sum_congr rfl
  intro A _
  have ho := actualOuterTrial r c e hr hc x ((paperListedEquiv r c hr hc x).symm A)
  rw [Equiv.apply_symm_apply] at ho
  simp only [w,ho,tableCode_option_eq]
  unfold listedTerminalDecision listedUnpaddedCounts
  split_ifs <;> simp

lemma terminalCount_actual (x : PaperStates r c) (T : Table r c) :
    terminalCount (prepareTransitionCache
      ((((stateCodeData r c e x,d^12),(d,h)),f)),matrixCode T.val)=
      ((listedCompletionCounts r c hr hc b h hb x).push
        (fun A => stateTrial r c ⟨x,A⟩)).count (some T) := by
  rw [prepareTransitionCache_encoded r c e hr hc,terminalCount_eq,
    terminal_cache_sum r c e hr hc h x T,terminal_completion_sum r c hr hc b h hb x T,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  unfold listedCompletionFactor
  split_ifs
  · exact Nat.mul_comm _ _
  · exact Nat.mul_zero _

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

lemma matrix_encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : matrix (encode r c hN T)=T.val := by
  funext i j
  simp only [matrix,encode,Equiv.symm_apply_apply]

lemma decode_encode {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (T : Table r c) : decode r c (encode r c hN T)=some T := by
  unfold decode
  rw [matrix_encode]
  simp only [T.property,dite_true]
  rfl

lemma decode_eq_some {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (z : Box m n N) (T : Table r c) :
    decode r c z=some T ↔ z=encode r c hN T := by
  constructor
  · intro ht
    unfold decode at ht
    split at ht
    next hm =>
      have he := congrArg Subtype.val (Option.some.inj ht)
      funext k
      apply Fin.ext
      have hk := congrFun (congrFun he (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
      simpa only [matrix,encode,Equiv.apply_symm_apply,Prod.mk.eta] using hk
    next hm => cases ht
  · rintro rfl
    exact decode_encode r c hN T

lemma tableAt_eq_some {m n N : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hN : (∑ i,r i)≤N) (k : Index m n N) (T : Table r c) :
    tableAt r c k=some T ↔ index r c hN T=k := by
  rw [tableAt,decode_eq_some r c hN]
  constructor
  · intro he
    have hh := congrArg finFunctionFinEquiv he
    simpa only [Equiv.apply_symm_apply,index] using hh.symm
  · intro he
    rw [←he,index,Equiv.symm_apply_apply]

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lookup of an original table's finite-box index -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma matrixCode_flatten {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    (matrixCode X).flatten=List.ofFn (fun k : Fin (m*n) =>
      X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  let k : Fin (m*n) := ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩
  have hk : finProdFinEquiv (i,j)=k := Fin.ext (by dsimp [k,finProdFinEquiv]; ac_rfl)
  change X i j=X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  rw [←hk,Equiv.symm_apply_apply]

lemma originalIndex_actual {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (T : Table r c) :
    originalIndex ((List.ofFn r,List.ofFn c),matrixCode T.val)=
      (OriginalTableBox.index r c le_rfl T).val := by
  unfold originalIndex originalIndexInput
  rw [matrixCode_flatten,List.sum_ofFn]
  change gridIndex (List.ofFn (fun k =>
    (OriginalTableBox.encode r c le_rfl T k).val),(∑ i,r i)+1)=_
  rw [gridIndex_ofFn]
  rfl

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding original-table laws in their computed finite box -/

namespace ContingencyTables.OriginalBoxLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
open OriginalTableBox

lemma tableAt_index (hN : (∑ i,r i)≤N) (X : Table r c) :
    tableAt r c (index r c hN X)=some X :=
  (tableAt_eq_some r c hN _ X).mpr rfl

lemma index_eq_iff (hN : (∑ i,r i)≤N) (X Y : Table r c) :
    index r c hN X=index r c hN Y ↔ X=Y := by
  constructor
  · intro h
    have he := congrArg (tableAt r c) h
    rw [tableAt_index,tableAt_index] at he
    exact Option.some.inj he
  · rintro rfl
    rfl

lemma count_none (hN : (∑ i,r i)≤N) (p : IntegerLaw (Option (Table r c)) Q) :
    (law r c hN p).count none=p.count none := by
  simp [law,IntegerLaw.push,Fintype.sum_option]

/-- Invalid box entries have zero count; every valid completion has
exactly the count of its unique feasible table. -/
lemma count_some (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (k : Index m n N) :
    (law r c hN p).count (some k)=
      (tableAt r c k).elim 0 (fun X => p.count (some X)) := by
  simp only [law,IntegerLaw.push,Fintype.sum_option,Option.map_none,reduceCtorEq,
    ite_false,zero_add,Option.map_some,Option.some.injEq]
  simp_rw [←tableAt_eq_some r c hN]
  cases tableAt r c k <;> simp

lemma count_index (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (X : Table r c) :
    (law r c hN p).count (some (index r c hN X))=p.count (some X) := by
  rw [count_some r c,tableAt_index]
  rfl

/-- Embedding tables into the explicit finite candidate list commutes
with every bounded first-success retry. -/
theorem retry_count_index (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (fallback X : Table r c) (J : ℕ) :
    ((law r c hN p).retry (index r c hN fallback) J).count (index r c hN X)=
      (p.retry fallback J).count X := by
  change IntegerLaw.retryCount (law r c hN p) (index r c hN fallback) J (index r c hN X)=
    IntegerLaw.retryCount p fallback J X
  induction J with
  | zero => simp only [IntegerLaw.retryCount,index_eq_iff r c]
  | succ J ih =>
    rw [IntegerLaw.retryCount,IntegerLaw.retryCount,count_index r c,count_none,ih]

/-- A retry keeps every invalid finite-box entry at zero. -/
lemma retry_count_some (hN : (∑ i,r i)≤N)
    (p : IntegerLaw (Option (Table r c)) Q) (fallback : Table r c) (J : ℕ)
    (k : Index m n N) :
    ((law r c hN p).retry (index r c hN fallback) J).count k=
      (tableAt r c k).elim 0 (fun T => (p.retry fallback J).count T) := by
  cases hk : tableAt r c k with
  | none =>
    have hi : k≠index r c hN fallback := by
      intro he
      rw [he,tableAt_index] at hk
      cases hk
    change IntegerLaw.retryCount (law r c hN p) (index r c hN fallback) J k=0
    induction J with
    | zero => simp only [IntegerLaw.retryCount,hi,ite_false]
    | succ J ih =>
      rw [IntegerLaw.retryCount,count_some r c hN,hk,ih]
      simp
  | some T =>
    have he := (tableAt_eq_some r c hN k T).mp hk
    rw [←he]
    exact retry_count_index r c hN p fallback T J

end
end ContingencyTables.OriginalBoxLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed finite-box index for the two small-profile views -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

attribute [local irreducible] physicalProfile

lemma profileBoxCoordinates_code (x : PaperStates r c) :
    List.ofFn (fun i => (profileBoxCoordinates r c e x i).val)=
      flattenViews (stateCode r c e x) := by
  unfold profileBoxCoordinates stateCode
  exact (flatten_profileCode (paperSmall r c) e
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) x)).symm

attribute [local irreducible] profileBoxCoordinates profileIndex

lemma profileBoxIndex_actual (x : PaperStates r c) :
    profileBoxIndex (stateCodeData r c e x)=(profileIndex r c e x).val := by
  unfold profileBoxIndex stateCodeData codeCheckData
  rw [←profileBoxCoordinates_code r c e x]
  unfold profileIndex
  exact gridIndex_ofFn _

lemma profileAt_index (x : PaperStates r c) :
    profileAt r c e (profileIndex r c e x)=some x := by
  unfold profileAt profileIndex
  rw [Equiv.symm_apply_apply,profileBoxCoordinates_code]
  have hl : (stateCode r c e x).1.length=q := by
    simp only [stateCode,profileCode,viewList,List.length_ofFn]
  have hs : splitViews (q,flattenViews (stateCode r c e x))=stateCode r c e x := by
    calc
      _=splitViews ((stateCode r c e x).1.length,flattenViews (stateCode r c e x)) :=
        congrArg (fun k => splitViews (k,flattenViews (stateCode r c e x))) hl.symm
      _=_ := split_flattenViews _
  rw [hs]
  exact decode_stateCode r c e x

lemma profileIndex_injective : Function.Injective (profileIndex r c e) := by
  intro x y hxy
  have h := congrArg (profileAt r c e) hxy
  simpa only [profileAt_index,Option.some.injEq] using h

lemma profileAt_eq_some (k : ProfileIndex (m := m) (n := n) (q := q))
    (x : PaperStates r c) : profileAt r c e k=some x ↔ profileIndex r c e x=k := by
  constructor
  · intro h
    have hc := (decodeStateCode_eq_some_iff r c e _ x).mp h
    have he : List.ofFn (fun i => (profileBoxCoordinates r c e x i).val)=
        List.ofFn (fun i => ((finFunctionFinEquiv.symm k :
          ProfileBox (m := m) (n := n) (q := q)) i).val) := by
      rw [profileBoxCoordinates_code]
      exact (congrArg flattenViews hc).trans (by simp [flattenViews,splitViews])
    have hv : profileBoxCoordinates r c e x=finFunctionFinEquiv.symm k := by
      funext i
      exact Fin.ext (congrFun (List.ofFn_injective he) i)
    unfold profileIndex
    rw [hv,Equiv.apply_symm_apply]
  · intro h
    rw [←h]
    exact profileAt_index r c e x

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable enumeration of the bounded two-view profile box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma profileBoxViews_actual (x : PaperStates r c) :
    profileBoxViews (stateCodeData r c e x)=
      List.ofFn (fun k : ProfileIndex (m := m) (n := n) (q := q) =>
        splitViews (q,List.ofFn (fun i =>
          ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val))) := by
  have hlen : ((cellCatalog (paperSmall r c) e++cellCatalog (paperSmall r c) e).map
      (fun _ => false)).length=q+q := by
    simp only [List.length_map,List.length_append,cellCatalog,List.length_ofFn]
  unfold profileBoxViews profileEnumerationData stateCodeData codeCheckData
  rw [gridWords_finFunctions _ (d^20) (q+q) hlen,List.map_ofFn]
  simp only [cellCatalog,List.length_ofFn]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLawEmbedding
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating a finite law inside a larger executable state box -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {Q : ℕ}

lemma push_count_injective (p : IntegerLaw A Q) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.push f).count (f a)=p.count a := by
  change (∑ x,if f x=f a then p.count x else 0)=_
  simp only [hf.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]

/-- A transition matrix may contain unused box states. Starting in the
embedded state set gives exactly the pushed-forward original walk. -/
theorem walk_push_count (K : A → IntegerLaw A Q) (L : B → IntegerLaw B Q)
    (f : A → B) (hf : ∀ x,L (f x)=(K x).push f) (start : A) (N : ℕ) (b : B) :
    (walk L (f start) N).count b=((walk K start N).push f).count b := by
  induction N generalizing b with
  | zero =>
    change (if b=f start then 1 else 0)=∑ a,if f a=b then (if a=start then 1 else 0) else 0
    have he (a : A) : (if f a=b then (if a=start then 1 else 0) else 0)=
        if a=start then (if f start=b then 1 else 0) else 0 := by
      by_cases h : a=start <;> simp [h]
    simp_rw [he]
    simp [eq_comm]
  | succ N ih =>
    change (∑ y,(walk L (f start) N).count y*(L y).count b)=
      ∑ a,if f a=b then (∑ x,(walk K start N).count x*(K x).count a) else 0
    simp_rw [ih]
    change (∑ y,(∑ x,if f x=y then (walk K start N).count x else 0)*(L y).count b)=_
    simp_rw [Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
    simp_rw [hf]
    change (∑ x,(walk K start N).count x*(∑ a,if f a=b then (K x).count a else 0))=_
    simp_rw [Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp

end
end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual adaptive profile walk embedded in its enumerable box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] listedStepCounts profileIndex

lemma profileBoxStep_index (x : PaperStates r c) :
    profileBoxStep r c e hr hc b h hb (profileIndex r c e x)=
      (listedStepCounts r c e hr hc b h hb x).push (profileIndex r c e) := by
  unfold profileBoxStep
  rw [profileAt_index]
  rfl

lemma profileBoxWalk_count (x : PaperStates r c) (N : ℕ) (k : BoxIndex) :
    (IntegerLaw.walk (profileBoxStep r c e hr hc b h hb) (profileIndex r c e x) N).count k=
      ((listedWalkCounts r c e hr hc b h hb x N).push (profileIndex r c e)).count k :=
  IntegerLaw.walk_push_count (listedStepCounts r c e hr hc b h hb)
    (profileBoxStep r c e hr hc b h hb) (profileIndex r c e)
    (profileBoxStep_index r c e hr hc b h hb) x N k

/-- Matrix propagation computes all box masses, including the zero
masses of invalid vectors, without enumerating random histories. -/
lemma profileBox_iterate (x : PaperStates r c) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,
      (List.ofFn (fun target : BoxIndex => List.ofFn (fun source : BoxIndex =>
        (profileBoxStep r c e hr hc b h hb source).count target)),
       List.ofFn (fun k : BoxIndex => if k=profileIndex r c e x then 1 else 0)))=
      List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb x N).push (profileIndex r c e)).count k) := by
  rw [IntegerMatrixPrograms.iterate_ofFn]
  apply congrArg List.ofFn
  funext k
  exact profileBoxWalk_count r c e hr hc b h hb x N k

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed matrix is the actual profile transition law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] stateCode stateCodeData prepareTransitionCache transitionCount
  ProfilePrograms.matrixEntry validMatrixEntry listedStepCounts listedCompletionCounts

lemma boxCode_injective : Function.Injective (boxCode (m := m) (n := n) (q := q)) := by
  intro k l hkl
  have hv := congrArg flattenViews hkl
  simp only [boxCode,splitViews,flattenViews,List.take_append_drop] at hv
  have he : (finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q))=
      finFunctionFinEquiv.symm l := by
    funext i
    exact Fin.ext (congrFun (List.ofFn_injective hv) i)
  exact finFunctionFinEquiv.symm.injective he

lemma boxCode_index (x : PaperStates r c) :
    boxCode (profileIndex r c e x)=stateCode r c e x := by
  exact ((decodeStateCode_eq_some_iff r c e _ x).mp (profileAt_index r c e x)).symm

lemma candidate_stateCodeData (x y : PaperStates r c) :
    candidateData (stateCodeData r c e x,stateCode r c e y)=stateCodeData r c e y := by
  unfold candidateData stateCodeData codeCheckData
  rfl

lemma test_candidate_iff (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c)
    (v : List ℕ×List ℕ) :
    profileTest (candidateData (stateCodeData r c e x,v))=true ↔
      ∃ y : PaperStates r c,stateCode r c e y=v := by
  simpa only [candidateData,stateCodeData,codeCheckData,stateCode] using
    (profileTest_code_iff r c htotal e v)

lemma matrixEntry_codes (htotal : ∑ i,r i=∑ j,c j) (z x y : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(stateCode r c e x,stateCode r c e y))=
      (listedStepCounts r c e hr hc b h hb x).count y := by
  have hx : profileTest (candidateData (stateCodeData r c e z,stateCode r c e x))=true :=
    (test_candidate_iff r c e htotal z _).mpr ⟨x,rfl⟩
  have hy : profileTest (candidateData (stateCodeData r c e z,stateCode r c e y))=true :=
    (test_candidate_iff r c e htotal z _).mpr ⟨y,rfl⟩
  unfold ProfilePrograms.matrixEntry sourceData targetData matrixData matrixInput
  rw [hx,hy]
  simp only [ite_true, if_true]
  unfold validMatrixEntry entryQuery entryCacheParameters
  dsimp only [sourceData,matrixData]
  rw [candidate_stateCodeData]
  exact transitionCount_actual r c e hr hc b h hb htotal x y xs hs

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every entry of the computed profile matrix has its exact integer law -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma push_count_not_range {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (b : B) (hb : ∀ a,f a≠b) :
    (p.push f).count b=0 := by
  change (∑ a,if f a=b then p.count a else 0)=0
  simp only [hb,ite_false,Finset.sum_const_zero]

end ContingencyTables.IntegerLaw

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
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
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData listedStepCounts prepareTransitionCache
  profileIndex profileAt ProfilePrograms.matrixEntry matrixInput IntegerLaw.push listedWalkCounts

lemma boxCode_test_false (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (k : BoxIndex) (hk : profileAt r c e k=none) :
    profileTest (candidateData (stateCodeData r c e z,boxCode k))=false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨x,hx⟩ := (test_candidate_iff r c e htotal z _).mp ht
  have hd : profileAt r c e k=some x := by
    unfold profileAt
    exact (decodeStateCode_eq_some_iff r c e _ x).mpr hx
  rw [hk] at hd
  cases hd

lemma matrixDenominator_actual (z : PaperStates r c) (xs : List Bool) (hs : xs.length=s) :
    matrixDenominator (matrixInput r c e b h z xs)=2^(s+f) := by
  unfold matrixDenominator matrixInput
  rw [BinaryPowerPrograms.power_eq,hs]

lemma sourceData_input (z : PaperStates r c) (xs : List Bool) (u v : List ℕ×List ℕ) :
    sourceData (matrixInput r c e b h z xs,(u,v))=candidateData (stateCodeData r c e z,u) := by
  unfold sourceData matrixData matrixInput
  rfl

lemma targetData_input (z : PaperStates r c) (xs : List Bool) (u v : List ℕ×List ℕ) :
    targetData (matrixInput r c e b h z xs,(u,v))=candidateData (stateCodeData r c e z,v) := by
  unfold targetData matrixData matrixInput
  rfl

lemma matrixEntry_invalid_source (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex)
    (hi : profileAt r c e i=none) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      if j=i then 2^(s+f) else 0 := by
  have hp := boxCode_test_false r c e htotal z i hi
  unfold ProfilePrograms.matrixEntry
  rw [sourceData_input,hp]
  simp only [Bool.false_eq_true,ite_false]
  unfold diagonalMatrixEntry
  rw [matrixDenominator_actual r c e b h z xs hs]
  have hij : boxCode i=boxCode j ↔ i=j :=
    (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
  simp only [hij,eq_comm]

lemma matrixEntry_invalid_target (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (j : BoxIndex) (hj : profileAt r c e j=none) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(stateCode r c e x,boxCode j))=0 := by
  have hx := (test_candidate_iff r c e htotal z (stateCode r c e x)).mpr ⟨x,rfl⟩
  have hj' := boxCode_test_false r c e htotal z j hj
  unfold ProfilePrograms.matrixEntry
  rw [sourceData_input,targetData_input,hx,hj']
  simp only [ite_true, if_true,Bool.false_eq_true,ite_false]

lemma matrixEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex) :
    ProfilePrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      (profileBoxStep r c e hr hc b h hb i).count j := by
  cases hi : profileAt r c e i with
  | none =>
    rw [matrixEntry_invalid_source r c e b h htotal z xs hs i j hi]
    unfold profileBoxStep
    rw [hi]
    rfl
  | some x =>
    have hix : profileIndex r c e x=i := (profileAt_eq_some r c e i x).mp hi
    have hcode : boxCode i=stateCode r c e x := by rw [←hix,boxCode_index]
    rw [hcode]
    unfold profileBoxStep
    rw [hi]
    simp only [Option.elim_some]
    cases hj : profileAt r c e j with
    | none =>
      rw [matrixEntry_invalid_target r c e b h htotal z x xs j hj]
      symm
      apply IntegerLaw.push_count_not_range
      intro a hindex
      rw [←hindex,profileAt_index] at hj
      cases hj
    | some y =>
      have hjy : profileIndex r c e y=j := (profileAt_eq_some r c e j y).mp hj
      rw [←hjy,boxCode_index,
        IntegerLaw.push_count_injective _ _ (profileIndex_injective r c e)]
      exact matrixEntry_codes r c e hr hc b h hb htotal z x y xs hs

lemma profileMatrix_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    profileMatrix (matrixInput r c e b h z xs)=
      List.ofFn (fun j : BoxIndex => List.ofFn (fun i : BoxIndex =>
        (profileBoxStep r c e hr hc b h hb i).count j)) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=
      List.ofFn (boxCode (m := m) (n := n) (q := q)) :=
    by
      unfold matrixData matrixInput
      exact profileBoxViews_actual r c e z
  unfold profileMatrix
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  unfold matrixColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact matrixEntry_actual r c e hr hc b h hb htotal z xs hs i j

lemma profileMatrix_walk (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) :
    IntegerMatrixPrograms.iterate (N,(profileMatrix (matrixInput r c e b h z xs),
      List.ofFn (fun k : BoxIndex => if k=profileIndex r c e z then 1 else 0)))=
      List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb z N).push (profileIndex r c e)).count k) := by
  rw [profileMatrix_actual r c e hr hc b h hb htotal z xs hs]
  exact profileBox_iterate r c e hr hc b h hb z N

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMatrixPoint
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma pointVector_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) :
    pointVector (List.ofFn (fun j => List.ofFn (fun i => B i j)),start.val)=
      List.ofFn (fun i : Fin n => if i=start then 1 else 0) := by
  unfold pointVector
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,pointEntry,Fin.ext_iff]


lemma fromPoint_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) (N : ℕ) :
    fromPoint (N,(List.ofFn (fun j => List.ofFn (fun i => B i j)),start.val))=
      List.ofFn (IntegerPropagation.numerators B start N) := by
  unfold fromPoint
  rw [pointVector_ofFn,iterate_ofFn]

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTerminalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact trial counts from matrix propagation and cached terminal weights -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma bind_count {A B : Type*} [Fintype A] [Fintype B]
    {Q R : ℕ} (p : IntegerLaw A Q) (K : A → IntegerLaw B R) (b : B) :
    (p.bind K).count b=∑ a,p.count a*(K a).count b := rfl

lemma sum_push_mul {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (w : B → ℕ) :
    (∑ b,(p.push f).count b*w b)=∑ a,p.count a*w (f a) := by
  change (∑ b,(∑ a,if f a=b then p.count a else 0)*w b)=_
  simp_rw [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]

end ContingencyTables.IntegerLaw

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData listedCompletionCounts listedWalkCounts
  listedTrialCounts prepareTransitionCache terminalCount matrixInput IntegerLaw.push

lemma terminalEntry_actual (z x : PaperStates r c) (xs : List Bool) (T : Table r c) :
    terminalEntry (matrixInput r c e b h z xs,(stateCode r c e x,matrixCode T.val))=
      (terminalFibreCounts r c hr hc b h hb x).count (some T) := by
  unfold terminalEntry terminalEntryQuery terminalSourceInput entryCacheParameters
  dsimp only [sourceData,matrixData]
  unfold matrixInput
  rw [candidate_stateCodeData]
  exact terminalCount_actual r c e hr hc b h hb x T

lemma terminalColumn_ofFn (z : PaperStates r c) (xs : List Bool) (T : Table r c) :
    terminalColumn (matrixInput r c e b h z xs,matrixCode T.val)=
      List.ofFn (fun k : BoxIndex => terminalEntry
        (matrixInput r c e b h z xs,(boxCode k,matrixCode T.val))) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=List.ofFn
      (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold terminalColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  rfl

lemma listedTrialCounts_count (z : PaperStates r c) (N : ℕ) (T : Table r c) :
    (listedTrialCounts r c e hr hc b h hb z N).count (some T)=
      ∑ x,(listedWalkCounts r c e hr hc b h hb z N).count x*
        (terminalFibreCounts r c hr hc b h hb x).count (some T) := by
  unfold listedTrialCounts terminalFibreCounts
  exact IntegerLaw.bind_count _ _ _

attribute [local irreducible] terminalFibreCounts

lemma terminal_dot_trial (z : PaperStates r c) (xs : List Bool) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (List.ofFn (fun k : BoxIndex =>
        ((listedWalkCounts r c e hr hc b h hb z N).push (profileIndex r c e)).count k),
       terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (listedTrialCounts r c e hr hc b h hb z N).count (some T) := by
  rw [terminalColumn_ofFn r c e b h z xs T,IntegerMatrixPrograms.dot_ofFn,
    IntegerLaw.sum_push_mul]
  change (∑ x,(listedWalkCounts r c e hr hc b h hb z N).count x*
    terminalEntry (matrixInput r c e b h z xs,(boxCode (profileIndex r c e x),matrixCode T.val)))=_
  simp_rw [boxCode_index,terminalEntry_actual r c e hr hc b h hb]
  exact (listedTrialCounts_count r c e hr hc b h hb z N T).symm

lemma fromPoint_trial_count (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (IntegerMatrixPrograms.fromPoint (N,
        (profileMatrix (matrixInput r c e b h z xs),(profileIndex r c e z).val)),
       terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (listedTrialCounts r c e hr hc b h hb z N).count (some T) := by
  unfold IntegerMatrixPrograms.fromPoint
  rw [profileMatrix_actual r c e hr hc b h hb htotal z xs hs,
    IntegerMatrixPrograms.pointVector_ofFn]
  rw [←profileMatrix_actual r c e hr hc b h hb htotal z xs hs,
    profileMatrix_walk r c e hr hc b h hb htotal z xs hs N]
  exact terminal_dot_trial r c e hr hc b h hb z xs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed walk-and-terminal integer trial counts -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma trialCount_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (T : Table r c) :
    trialCount ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),matrixCode T.val)=
      (listedTrialCounts r c e hr hc b h hb z N).count (some T) := by
  unfold trialCount walkCounts walkCountData
  exact fromPoint_trial_count r c e hr hc b h hb htotal z xs hs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTrialVector
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] trialCount listedTrialCounts matrixInput

lemma trialVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) :
    trialVector ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c))=
      List.ofFn (fun k : OriginalTableBox.Index m n (∑ i,r i) =>
        (OriginalBoxLaw.law r c le_rfl (listedTrialCounts r c e hr hc b h hb z N)).count (some k)) := by
  unfold trialVector
  rw [candidates_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  rw [OriginalBoxLaw.count_some]
  dsimp only [Function.comp_apply]
  cases he : tableAt r c k with
  | none => rfl
  | some T =>
    simp only [Option.map_some,optionalTrialCount,Option.isSome_some,ite_true, if_true,optionalTrialInput,
      Option.getD_some,Option.elim_some]
    exact trialCount_actual r c e hr hc b h hb htotal z xs hs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalOuterVector
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
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

attribute [local irreducible] trialVector listedTrialCounts matrixInput outerVectorInput

lemma outerVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (js : List Bool) (fallback : Table r c) :
    outerVector (((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c)),((js,(2^(s+f))^N*2^f),matrixCode fallback.val))=
      List.ofFn ((OriginalBoxLaw.law r c le_rfl
        (listedTrialCounts r c e hr hc b h hb z N)).retry
        (OriginalTableBox.index r c le_rfl fallback) js.length).count := by
  unfold outerVector outerVectorInput
  rw [trialVector_actual r c e hr hc b h hb htotal z xs hs N,originalIndex_actual]
  exact VectorRetryPrograms.counts_actual _ js _

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

lemma parameterTrials_ofFn (k : ℕ) :
    parameterTrials ((List.ofFn r,List.ofFn c),k)=outerTrials d k := by
  rw [parameterTrials,parameterDimension_ofFn]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitBoxLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual adaptive profile walk embedded in its enumerable box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] unitStepCounts profileIndex

lemma unitBoxStep_index (x : PaperStates r c) :
    unitBoxStep r c e (profileIndex r c e x)=
      (unitStepCounts r c e x).push (profileIndex r c e) := by
  unfold unitBoxStep
  rw [profileAt_index]
  rfl

lemma unitBoxWalk_count (x : PaperStates r c) (N : ℕ) (k : BoxIndex) :
    (IntegerLaw.walk (unitBoxStep r c e) (profileIndex r c e x) N).count k=
      ((unitWalkCounts r c e x N).push (profileIndex r c e)).count k :=
  IntegerLaw.walk_push_count (unitStepCounts r c e)
    (unitBoxStep r c e) (profileIndex r c e)
    (unitBoxStep_index r c e) x N k

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitMatrixLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-small matrix computes its actual finite-word law -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical

lemma push_push_count {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] {Q : ℕ} (p : IntegerLaw A Q)
    (f : A → B) (g : B → C) (c : C) :
    ((p.push f).push g).count c=(p.push (g ∘ f)).count c := by
  calc
    _ = ∑ b,(p.push f).count b*(if g b=c then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : g b=c <;> simp only [h,ite_true, if_true,ite_false,mul_one,mul_zero]
    _ = ∑ a,p.count a*(if g (f a)=c then 1 else 0) := sum_push_mul p f _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : g (f a)=c <;> simp only [h,Function.comp_apply,ite_true, if_true,ite_false,mul_one,mul_zero]

lemma push_count_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {Q : ℕ} (p : IntegerLaw A Q) (f : A → B) (b : B) :
    (p.push f).count b=∑ a,if f a=b then p.count a else 0 := rfl

lemma boolean_push_count {B : Type*} [Fintype B] [DecidableEq B] (s : ℕ)
    (f : (Fin s → Bool) → B) (b : B) :
    ((boolean s).push f).count b=∑ bits,if f bits=b then 1 else 0 := rfl

end ContingencyTables.IntegerLaw

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c)) (b h : ℕ)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData profileIndex profileAt matrixInput
  UnitCountPrograms.matrixEntry unitStepCounts

lemma unit_wordViews_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (v : List ℕ×List ℕ) (bits : Fin s → Bool) :
    UnitCountPrograms.wordViews ((matrixInput r c e b h z xs,(stateCode r c e x,v)),List.ofFn bits)=
      stateCode r c e (unitCodeBitStep r c e x bits) := by
  unfold UnitCountPrograms.wordViews
  rw [sourceData_input,candidate_stateCodeData,codeProposal_encoded r c e htotal x bits]
  cases hp : decodedCodeProposal r c e x bits <;>
    simp only [Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,unitCodeBitStep,hp]

lemma unitStepCounts_push_count (x : PaperStates r c) (j : BoxIndex) :
    ((unitStepCounts r c e x).push (profileIndex r c e)).count j=
      ∑ bits : Fin s → Bool,if profileIndex r c e (unitCodeBitStep r c e x bits)=j then 1 else 0 := by
  unfold unitStepCounts
  rw [IntegerLaw.push_push_count]
  exact IntegerLaw.boolean_push_count s
    (profileIndex r c e ∘ unitCodeBitStep r c e x) j

lemma unit_wordCount_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (j : BoxIndex) (bits : Fin s → Bool) :
    UnitCountPrograms.wordCount
      ((matrixInput r c e b h z xs,(stateCode r c e x,boxCode j)),List.ofFn bits)=
      if profileIndex r c e (unitCodeBitStep r c e x bits)=j then 1 else 0 := by
  unfold UnitCountPrograms.wordCount
  rw [unit_wordViews_actual r c e b h htotal z x xs (boxCode j) bits,←boxCode_index r c e]
  have he (a b : BoxIndex) : boxCode a=boxCode b ↔ a=b :=
    (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
  simp only [he]

lemma unit_validEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z x : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (j : BoxIndex) :
    UnitCountPrograms.validEntry (matrixInput r c e b h z xs,(stateCode r c e x,boxCode j))=
      ((unitStepCounts r c e x).push (profileIndex r c e)).count j := by
  unfold UnitCountPrograms.validEntry
  have hxs : (matrixInput r c e b h z xs).2=xs := by unfold matrixInput; rfl
  rw [hxs]
  change ((booleanWords xs).map (fun w => UnitCountPrograms.wordCount
    ((matrixInput r c e b h z xs,(stateCode r c e x,boxCode j)),w))).sum=_
  rw [sum_booleanWords xs s hs,unitStepCounts_push_count]
  apply Finset.sum_congr rfl
  intro bits _
  exact unit_wordCount_actual r c e b h htotal z x xs j bits

lemma unit_matrixEntry_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (i j : BoxIndex) :
    UnitCountPrograms.matrixEntry (matrixInput r c e b h z xs,(boxCode i,boxCode j))=
      (unitBoxStep r c e i).count j := by
  cases hi : profileAt r c e i with
  | none =>
    have hp := boxCode_test_false r c e htotal z i hi
    unfold UnitCountPrograms.matrixEntry
    rw [sourceData_input,hp]
    simp only [Bool.false_eq_true,ite_false]
    unfold UnitCountPrograms.diagonalEntry UnitCountPrograms.denominator
    unfold unitBoxStep
    rw [hi]
    simp only [Option.elim_none,IntegerLaw.point]
    unfold matrixInput
    rw [BinaryPowerPrograms.power_eq,hs]
    have he (a b : BoxIndex) : boxCode a=boxCode b ↔ a=b :=
      (boxCode_injective (m := m) (n := n) (q := q)).eq_iff
    simp only [he,eq_comm]
  | some x =>
    have hix : profileIndex r c e x=i := (profileAt_eq_some r c e i x).mp hi
    have hcode : boxCode i=stateCode r c e x := by rw [←hix,boxCode_index]
    rw [hcode]
    unfold UnitCountPrograms.matrixEntry
    rw [sourceData_input]
    have hx := (test_candidate_iff r c e htotal z (stateCode r c e x)).mpr ⟨x,rfl⟩
    rw [hx]
    simp only [ite_true, if_true]
    unfold unitBoxStep
    rw [hi]
    exact unit_validEntry_actual r c e b h htotal z x xs hs j

lemma unit_profileMatrix_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) :
    UnitCountPrograms.profileMatrix (matrixInput r c e b h z xs)=
      List.ofFn (fun j : BoxIndex => List.ofFn (fun i : BoxIndex =>
        (unitBoxStep r c e i).count j)) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=
      List.ofFn (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold UnitCountPrograms.profileMatrix
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  unfold UnitCountPrograms.matrixColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact unit_matrixEntry_actual r c e b h htotal z xs hs i j

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTerminalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-small trial counts from the computed matrix and terminal column -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c)) (b h : ℕ)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)
local notation "BoxIndex" => ProfileIndex (m := m) (n := n) (q := q)

attribute [local irreducible] stateCode stateCodeData matrixInput unitWalkCounts unitTrialCounts
  UnitCountPrograms.terminalEntry IntegerLaw.push

lemma successfulWeight_table (o : Option (Table r c)) (T : Table r c) :
    successfulWeight (matrixCode T.val,(o.map (fun A => matrixCode A.val),1))=
      if o=some T then 1 else 0 := by
  cases o with
  | none => rfl
  | some A =>
    unfold successfulWeight
    simp only [Option.map_some,Option.elim_some,Option.some.injEq]
    have he : matrixCode A.val=matrixCode T.val ↔ A=T := by
      constructor
      · intro he
        exact Subtype.ext (matrixCode_injective he)
      · rintro rfl
        rfl
    simp only [he]

lemma unit_terminalEntry_actual (hsmall : ∀ i j,paperSmall r c i j=true)
    (z x : PaperStates r c) (xs : List Bool) (T : Table r c) :
    UnitCountPrograms.terminalEntry (matrixInput r c e b h z xs,(stateCode r c e x,matrixCode T.val))=
      if stateTrial r c ⟨x,allSmallFibre r c hsmall x⟩=some T then 1 else 0 := by
  unfold UnitCountPrograms.terminalEntry UnitCountPrograms.terminalData terminalSourceInput
  dsimp only [sourceData,matrixData]
  unfold matrixInput
  rw [candidate_stateCodeData,unitOuterTrial r c e hsmall x]
  exact successfulWeight_table r c _ T

lemma unit_terminalColumn_ofFn (z : PaperStates r c) (xs : List Bool) (T : Table r c) :
    UnitCountPrograms.terminalColumn (matrixInput r c e b h z xs,matrixCode T.val)=
      List.ofFn (fun k : BoxIndex => UnitCountPrograms.terminalEntry
        (matrixInput r c e b h z xs,(boxCode k,matrixCode T.val))) := by
  have hv : profileBoxViews (matrixData (matrixInput r c e b h z xs))=List.ofFn
      (boxCode (m := m) (n := n) (q := q)) := by
    unfold matrixData matrixInput
    exact profileBoxViews_actual r c e z
  unfold UnitCountPrograms.terminalColumn
  dsimp only [Prod.fst]
  rw [hv,List.map_ofFn]
  rfl

lemma unitTrialCounts_count (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) (N : ℕ) (T : Table r c) :
    (unitTrialCounts r c e hsmall z N).count (some T)=
      ∑ x,(unitWalkCounts r c e z N).count x*
        (if stateTrial r c ⟨x,allSmallFibre r c hsmall x⟩=some T then 1 else 0) := by
  unfold unitTrialCounts
  rw [IntegerLaw.push_count_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

lemma unit_terminal_dot_trial (hsmall : ∀ i j,paperSmall r c i j=true)
    (z : PaperStates r c) (xs : List Bool) (N : ℕ) (T : Table r c) :
    IntegerMatrixPrograms.dot
      (List.ofFn (fun k : BoxIndex =>
        ((unitWalkCounts r c e z N).push (profileIndex r c e)).count k),
       UnitCountPrograms.terminalColumn (matrixInput r c e b h z xs,matrixCode T.val))=
      (unitTrialCounts r c e hsmall z N).count (some T) := by
  rw [unit_terminalColumn_ofFn r c e b h z xs T,IntegerMatrixPrograms.dot_ofFn,IntegerLaw.sum_push_mul]
  change (∑ x,(unitWalkCounts r c e z N).count x*
    UnitCountPrograms.terminalEntry
      (matrixInput r c e b h z xs,(boxCode (profileIndex r c e x),matrixCode T.val)))=_
  simp_rw [boxCode_index,unit_terminalEntry_actual r c e b h hsmall]
  exact (unitTrialCounts_count r c e hsmall z N T).symm

lemma unit_trialCount_actual (htotal : ∑ i,r i=∑ j,c j)
    (hsmall : ∀ i j,paperSmall r c i j=true) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (T : Table r c) :
    UnitCountPrograms.trialCount
      ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),matrixCode T.val)=
      (unitTrialCounts r c e hsmall z N).count (some T) := by
  unfold UnitCountPrograms.trialCount UnitCountPrograms.walkCounts UnitCountPrograms.walkCountData
  rw [unit_profileMatrix_actual r c e b h htotal z xs hs,IntegerMatrixPrograms.fromPoint_ofFn]
  have he : List.ofFn (IntegerPropagation.numerators
      (fun i j : BoxIndex => (unitBoxStep r c e i).count j) (profileIndex r c e z) N)=
      List.ofFn (fun k : BoxIndex => ((unitWalkCounts r c e z N).push (profileIndex r c e)).count k) := by
    apply congrArg List.ofFn
    funext k
    exact unitBoxWalk_count r c e z N k
  rw [he]
  exact unit_terminal_dot_trial r c e b h hsmall z xs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOriginalVector
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms UnitCountPrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (b h : ℕ) (hsmall : ∀ i j,paperSmall r c i j=true)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] UnitCountPrograms.trialCount unitTrialCounts matrixInput

lemma unit_trialVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) :
    UnitCountPrograms.trialVector ((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c))=
      List.ofFn (fun k : OriginalTableBox.Index m n (∑ i,r i) =>
        (OriginalBoxLaw.law r c le_rfl (unitTrialCounts r c e hsmall z N)).count (some k)) := by
  unfold UnitCountPrograms.trialVector
  rw [candidates_code,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  rw [OriginalBoxLaw.count_some]
  dsimp only [Function.comp_apply]
  cases he : tableAt r c k with
  | none => rfl
  | some T =>
    simp only [Option.map_some,UnitCountPrograms.optionalTrialCount,Option.isSome_some,ite_true, if_true,UnitCountPrograms.optionalTrialInput,
      Option.getD_some,Option.elim_some]
    exact unit_trialCount_actual r c e b h htotal hsmall z xs hs N T

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOuterVector
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms UnitCountPrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (b h : ℕ) (hsmall : ∀ i j,paperSmall r c i j=true)
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] UnitCountPrograms.trialVector unitTrialCounts matrixInput UnitCountPrograms.outerVectorInput

lemma unit_outerVector_actual (htotal : ∑ i,r i=∑ j,c j) (z : PaperStates r c)
    (xs : List Bool) (hs : xs.length=s) (N : ℕ) (js : List Bool) (fallback : Table r c) :
    UnitCountPrograms.outerVector (((matrixInput r c e b h z xs,(N,(profileIndex r c e z).val)),
      (List.ofFn r,List.ofFn c)),((js,(2^s)^N),matrixCode fallback.val))=
      List.ofFn ((OriginalBoxLaw.law r c le_rfl
        (unitTrialCounts r c e hsmall z N)).retry
        (OriginalTableBox.index r c le_rfl fallback) js.length).count := by
  unfold UnitCountPrograms.outerVector UnitCountPrograms.outerVectorInput
  rw [unit_trialVector_actual r c e b h hsmall htotal z xs hs N,originalIndex_actual]
  exact VectorRetryPrograms.counts_actual _ js _

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalBoxPush
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting weighted sums through the original-table enumeration -/

namespace ContingencyTables.OriginalBoxLaw
open OriginalTableBox ProfilePrograms DensePrograms
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma push_count (hN : (∑ i,r i)≤N) (p : IntegerLaw (Table r c) Q) (k : Index m n N) :
    (p.push (index r c hN)).count k=(tableAt r c k).elim 0 p.count := by
  change (∑ X,if index r c hN X=k then p.count X else 0)=_
  simp_rw [←tableAt_eq_some r c hN]
  cases tableAt r c k <;> simp

end
end ContingencyTables.OriginalBoxLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledCountSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scheduled executable numerator vector is the public sampler's law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] scheduledTrialDenominator scheduledTrialWidth
  scheduledCounts scheduledOuterInput listedOuterCounts unitOuterCounts matrixInput
  scheduledTableDraw listedOuterDraw unitCodeOuterDraw


variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

lemma scheduledOuterInput_code (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    scheduledOuterInput ((List.ofFn r,List.ofFn c),k)=
      (((matrixInput r c (computedCellEquiv r c) b (outerAccuracy d b k)
        (tableState r c (GreedyFeasibleTable.table r c htotal)) (unaryMarkers s),
        (outerSteps d b k,(profileIndex r c (computedCellEquiv r c)
          (tableState r c (GreedyFeasibleTable.table r c htotal))).val)),
        (List.ofFn r,List.ofFn c)),
        ((unaryMarkers (outerTrials d k),scheduledTrialDenominator ((List.ofFn r,List.ofFn c),k)),
          matrixCode (GreedyFeasibleTable.table r c htotal).val)) := by
  unfold scheduledOuterInput scheduledTrialInput scheduledWalkInput scheduledMatrixParameters
    scheduledCacheParameters scheduledStartIndex
  rw [initialCheck_code r c htotal,marginPadding_ofFn,parameterDimension_ofFn,
    parameterAccuracy_ofFn,parameterCompletionWidth_ofFn,parameterProposalWidth_ofFn,
    parameterSteps_ofFn,profileBoxIndex_actual,parameterTrials_ofFn,GreedyFeasibleTable.listMatrix_ofFn]
  unfold matrixInput
  rfl

/-- Every literal vector entry equals the corresponding embedded table count,
including zero at infeasible matrices in the original bounding box. -/
lemma scheduledCounts_actual_oai (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    scheduledCounts ((List.ofFn r,List.ofFn c),k)=
      List.ofFn (((scheduledCountsLaw r c htotal k).push (index r c le_rfl)).count) := by
  unfold scheduledCounts
  by_cases hlarge : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true
  · rw [ite_eq_left hlarge,scheduledOuterInput_code r c htotal]
    conv_lhs => rw [scheduledTrialDenominator_dense r c k hlarge]
    rw [outerVector_actual r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp hlarge).1 ((hasLargeRectangle_spec r c k).mp hlarge).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1 htotal _ _
        (unaryMarkers_length _) _ _ _]
    apply congrArg List.ofFn
    funext j
    rw [OriginalBoxLaw.retry_count_some,OriginalBoxLaw.push_count]
    simp only [scheduledCountsLaw,dite_eq_left hlarge,IntegerLaw.rebase,listedOuterCounts]
    simp only [IntegerLaw.retry,unaryMarkers_length]
  · rw [ite_eq_right hlarge,scheduledOuterInput_code r c htotal]
    conv_lhs => rw [scheduledTrialDenominator_unit r c k hlarge]
    rw [unit_outerVector_actual r c (computedCellEquiv r c) b (outerAccuracy d b k)
      (allSmall_of_no_large r c k hlarge) htotal _ _ (unaryMarkers_length _) _ _ _]
    apply congrArg List.ofFn
    funext j
    rw [OriginalBoxLaw.retry_count_some,OriginalBoxLaw.push_count]
    simp only [scheduledCountsLaw,dite_eq_right hlarge,IntegerLaw.rebase,unitOuterCounts]
    simp only [IntegerLaw.retry,unaryMarkers_length]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual_oai := @OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual_oai

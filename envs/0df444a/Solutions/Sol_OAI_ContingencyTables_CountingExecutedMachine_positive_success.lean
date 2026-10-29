-- Prove2me | solution 1 for OAI.ContingencyTables.CountingExecutedMachine.positive_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:52:57.179982+00:00
-- url     : https://prove2.me/submissions/8ceed8ee-e7e3-4ea6-b521-bde6080cd352

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_RootedHistoryConfidence_history_success

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

open scoped BigOperators Classical

lemma final_estimate_accuracy (ε Z C Zhat : ℝ) (hε0 : 0<ε) (hε1 : ε<1) (hZ : 0≤Z)
    (hC : Z≤C ∧ C≤(1+ε/10)*Z)
    (hhat : (1-ε/4)*C≤Zhat ∧ Zhat≤(1+ε/4)*C) :
    (1-ε)*Z≤Zhat ∧ Zhat≤(1+ε)*Z := by
  have hl := mul_le_mul_of_nonneg_left hC.1 (show 0≤1-ε/4 by linarith)
  have hu := mul_le_mul_of_nonneg_left hC.2 (show 0≤1+ε/4 by linarith)
  have he : (1+ε/4)*(1+ε/10)≤1+ε := by nlinarith [sq_nonneg ε]
  have he' := mul_le_mul_of_nonneg_right he hZ
  constructor <;> nlinarith [mul_nonneg hε0.le hZ]

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma uniformAverage_mul_left {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformAverage (fun x => r*f x)=r*uniformAverage f := by
  simp [uniformAverage,← Finset.mul_sum,mul_div_assoc]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

lemma uniformAverage_nonneg {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x,0≤f x) : 0≤uniformAverage f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)
lemma uniformAverage_mono {X : Type*} [Fintype X] (f g : X → ℝ)
    (hfg : ∀ x,f x≤g x) : uniformAverage f≤uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (Nat.cast_nonneg _)
open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

lemma median_bad_count (l : List ℚ) (hl : 0<l.length) (a b : ℚ)
    (hbad : ¬(a ≤ rationalMedian l ∧ rationalMedian l≤b)) :
    l.length ≤ 2*l.countP (outsideInterval a b) := by
  let s := l.mergeSort (· ≤ ·)
  have hlen : s.length=l.length := List.length_mergeSort _
  have hs : s.SortedLE := List.sortedLE_mergeSort
  have hk : l.length/2 < s.length := by rw [hlen]; omega
  have he : rationalMedian l=s[l.length/2] := List.getD_eq_getElem s 0 hk
  rw [he] at hbad
  have hc : s.countP (outsideInterval a b)=l.countP (outsideInterval a b) :=
    List.Perm.countP_eq _ (List.mergeSort_perm _ _)
  by_cases ha : a ≤ s[l.length/2]
  · have hb : b < s[l.length/2] := lt_of_not_ge (fun hh => hbad ⟨ha,hh⟩)
    have htail : (s.drop (l.length/2)).countP (outsideInterval a b)=(s.drop (l.length/2)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_drop]
      apply decide_eq_true
      intro hh
      have hm := hs.getElem_le_getElem_of_le (i := l.length/2) (j := l.length/2+i) (hi := hk) (hj := by simp only [List.length_drop] at hi; omega) (by omega)
      exact (not_le_of_gt (hb.trans_le hm)) hh.2
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2)) (l₂ := s.drop (l.length/2))
    rw [List.take_append_drop,htail,hc,List.length_drop,hlen] at hdecomp
    omega
  · have hfront : (s.take (l.length/2+1)).countP (outsideInterval a b)=(s.take (l.length/2+1)).length := by
      apply List.countP_eq_length.mpr
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take]
      apply decide_eq_true
      intro hh
      have hi' : i≤l.length/2 := by simp only [List.length_take] at hi; omega
      have hm := hs.getElem_le_getElem_of_le (i := i) (j := l.length/2) (hi := by simp only [List.length_take] at hi; omega) (hj := hk) hi'
      exact ha (hh.1.trans hm)
    have hdecomp := List.countP_append (p := outsideInterval a b)
      (l₁ := s.take (l.length/2+1)) (l₂ := s.drop (l.length/2+1))
    rw [List.take_append_drop,hfront,hc,List.length_take,hlen] at hdecomp
    omega

lemma uniformAverage_mul_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x*c)=uniformAverage f*c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

lemma countP_ofFn_cons {X : Type*} (p : X → Bool) (x : X) {R : ℕ} (xs : Fin R → X) :
    (List.ofFn (Fin.cons x xs)).countP p=(if p x then 1 else 0)+(List.ofFn xs).countP p := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,List.countP_cons]
  change (List.ofFn xs).countP p+(if p x then 1 else 0)=(if p x then 1 else 0)+(List.ofFn xs).countP p
  omega

lemma independent_bad_moment {X : Type*} [Fintype X] [Nonempty X]
    (bad : X → Bool) (R : ℕ) :
    uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad))=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R := by
  induction R with
  | zero => simp [List.ofFn_zero,uniformAverage_const]
  | succ R ih =>
    rw [uniformAverage_fin_succ]
    simp_rw [countP_ofFn_cons,pow_add,uniformAverage_mul_left,ih]
    rw [uniformAverage_mul_const]
    have he : (fun x : X => (4:ℝ)^(if bad x then 1 else 0:ℕ))=
        fun x => 1+3*(if bad x then (1:ℝ) else 0) := by
      funext x; cases bad x <;> norm_num
    rw [he,uniformAverage_add,uniformAverage_const,uniformAverage_mul_left,pow_succ]
    ring

lemma countP_map {X Y : Type*} (l : List X) (f : X → Y) (p : Y → Bool) :
    (l.map f).countP p=l.countP (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.countP_cons,ih]

theorem median_failure_bound {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (R : ℕ) (hR : 0<R)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    uniformAverage (fun xs : Fin R → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))
      then (1:ℝ) else 0) ≤ (31/32:ℝ)^R := by
  let bad : X → Bool := fun x => outsideInterval a b (output x)
  have hx : ∀ xs : Fin R → X,
      (if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)
      ≤ (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R := by
    intro xs
    by_cases he : outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i))))=true
    · rw [ite_eq_left he]
      have hc := median_bad_count (List.ofFn (fun i => output (xs i))) (by simpa using hR) a b (by
        simpa only [outsideInterval,decide_eq_true_eq] using he)
      have hmap : List.ofFn (fun i => output (xs i))=(List.ofFn xs).map output := by rw [List.map_ofFn]; rfl
      rw [hmap,countP_map,List.length_map,List.length_ofFn] at hc
      have hp : (2:ℝ)^R≤4^((List.ofFn xs).countP bad) := by
        calc
          (2:ℝ)^R ≤ 2^(2*((List.ofFn xs).countP bad)) := pow_le_pow_right₀ (by norm_num) hc
          _ = _ := by rw [pow_mul]; norm_num
      exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
    · rw [ite_eq_right he]; positivity
  have hm := uniformAverage_mono _ _ hx
  have hrw : uniformAverage (fun xs : Fin R → X => (4:ℝ)^((List.ofFn xs).countP bad)/(2:ℝ)^R)=
      (1+3*uniformAverage (fun x => if bad x then (1:ℝ) else 0))^R/(2:ℝ)^R := by
    simp_rw [div_eq_mul_inv]
    rw [uniformAverage_mul_const,independent_bad_moment]
  rw [hrw] at hm
  apply hm.trans
  rw [←div_pow]
  apply pow_le_pow_left₀ (by
    apply div_nonneg _ (by norm_num)
    have hz := uniformAverage_nonneg (fun x => if bad x then (1:ℝ) else 0) (by intro x; split_ifs <;> norm_num)
    linarith)
  dsimp [bad] at *
  linarith

lemma repetitionCount_pos (δ : ℚ) : 0 < repetitionCount δ := by unfold repetitionCount; omega
lemma rational_binary_accuracy (δ : ℚ) (hδ : 0<δ) :
    (1/2:ℝ)^(δ.den.bits.length+1) ≤ (δ:ℝ) := by
  have hd : (0:ℝ)<δ.den := by exact_mod_cast δ.den_pos
  have hn : (1:ℝ)≤(δ.num:ℝ) := by exact_mod_cast (show (1:ℤ)≤δ.num by have h := Rat.num_pos.mpr hδ; omega)
  have hp : (δ.den:ℝ)≤(2:ℝ)^(δ.den.bits.length+1) := by
    exact_mod_cast (Nat.le_of_lt ((Nat.size_le.mp (show δ.den.size≤δ.den.bits.length+1 by rw [Nat.size_eq_bits_len]; omega))))
  rw [one_div,inv_pow,Rat.cast_def]
  apply le_trans (inv_anti₀ hd hp)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hn hd.le
lemma confidence_decay (δ : ℚ) (hδ : 0<δ) :
    (31/32:ℝ)^(repetitionCount δ) ≤ (δ:ℝ) := by
  unfold repetitionCount
  rw [pow_mul]
  apply le_trans _ (rational_binary_accuracy δ hδ)
  apply pow_le_pow_left₀ (by positivity)
  norm_num

theorem median_confidence {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (a b : ℚ) (δ : ℚ) (hδ : 0<δ)
    (hbad : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0)≤5/16) :
    1-(δ:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
  have h := (median_failure_bound output a b (repetitionCount δ) (repetitionCount_pos δ) hbad).trans
    (confidence_decay δ hδ)
  have he : (fun xs : Fin (repetitionCount δ) → X =>
      if outsideInterval a b (rationalMedian (List.ofFn (fun i => output (xs i)))) then (1:ℝ) else 0)=
    fun xs => 1-(if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    funext xs
    simp only [outsideInterval,decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [he] at h
  have hei : uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      1-(if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0))=
      1-uniformAverage (fun xs : Fin (repetitionCount δ) → X =>
      if a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
        rationalMedian (List.ofFn (fun i => output (xs i)))≤b then (1:ℝ) else 0) := by
    unfold uniformAverage
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [sub_div,div_self (by exact_mod_cast ne_of_gt (Fintype.card_pos))]
  rw [hei] at h
  linarith

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section CanonicalFair
open scoped BigOperators Classical
lemma uniformAverage_independent_eq {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z)
    (h : ∀ φ : Z → ℝ,uniformAverage (fun x => φ (f x))=uniformAverage (fun y => φ (g y)))
    (k : ℕ) (F : (Fin k → Z) → ℝ) :
    uniformAverage (fun xs : Fin k → X => F (fun i => f (xs i)))=
      uniformAverage (fun ys : Fin k → Y => F (fun i => g (ys i))) := by
  induction k with
  | zero =>
    have hf : ∀ xs : Fin 0 → X,(fun i => f (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro xs; funext i; exact Fin.elim0 i
    have hg : ∀ ys : Fin 0 → Y,(fun i => g (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro ys; funext i; exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ k ih =>
    have hf (x : X) (xs : Fin k → X) :
        (fun i : Fin (k+1) => f ((Fin.cons x xs : Fin (k+1) → X) i))=Fin.cons (f x) (fun i => f (xs i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin k → Y) :
        (fun i : Fin (k+1) => g ((Fin.cons y ys : Fin (k+1) → Y) i))=Fin.cons (g y) (fun i => g (ys i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have hi (x : X) := ih (fun zs => F (Fin.cons (f x) zs))
    simp_rw [hi]
    exact h (fun z => uniformAverage (fun ys : Fin k → Y => F (Fin.cons z (fun i => g (ys i)))))
end CanonicalFair

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion signature marginal is the literal weighted completion count

The physical all-large product is split bijectively into tree and free
assignments. Exact nonroot equations then retain one tree completion per
free assignment, with exactly its root/tree exponential penalty.
-/

namespace ContingencyTables.ForestCountIdentification

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration PhysicalLargeProfiles
open ForestCapacity GraphCompletionCounts ForestAssignmentSplit ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

/-- At annealing parameter zero the original count is exactly the
product of the free interval lengths. -/
theorem sourceMarginal_zero (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    sourceMarginal small T d b r c 0 z=
      ∏ a : FreeCell small T, ((b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [sourceMarginal,Fintype.card_pi,Nat.cast_prod]

end ContingencyTables.ForestCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

omit [Fintype C] in
lemma viewCounts_eq_occupancy (cell : P → C) (S : Set (P × Bool)) (c : C) :
    viewCount cell S c false + viewCount cell S c true =
      ∑ p, if cell p=c then occupancy S p else 0 := by
  unfold viewCount occupancy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : cell p=c <;> simp [hc]

omit [Fintype P] in
lemma occupancy_single (S : Set (P × Bool)) (p : P) (h : PairSingle (pair p) S) :
    occupancy S p = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [occupancy,pair] at ha hb ⊢ <;> simp [ha,hb]

omit [Fintype C] in
/-- Every actual plain state is balanced in every physical cell. -/
theorem plain_counts (cell : P → C) (S : Set (P × Bool))
    (hS : PlainState pairs S) (c : C) :
    viewCount cell S c false + viewCount cell S c true = width cell c := by
  rw [viewCounts_eq_occupancy,width_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [occupancy_single S p (hS _ (pair_mem p))]

end ContingencyTables.TwoLiftStates

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_InitializationBrackets
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact local factorial sums for the companion's initial multipliers

These are the four brackets in the manuscript's exact initialization
formula. The full-pair case reduces to an explicitly evaluated quadratic
sum, so the rational initializer uses no factorial evaluation oracle.
-/

namespace ContingencyTables.InitializationBrackets

open scoped BigOperators
open Nat

private lemma choose_factorial (n k : ℕ) (hk : k≤n) :
    (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ)=(n !:ℝ) := by
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk

private lemma unshifted_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(k !:ℝ)*((n-k)!:ℝ))=
      ((n:ℝ)+1)*(n !:ℝ) := by
  calc
    _ = ∑ _k ∈ Finset.range (n+1), (n !:ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact choose_factorial n k (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp

theorem bracket_neither (b : ℕ) : bracket b 0 0=(b:ℝ)+1 := by
  unfold bracket
  simp only [Nat.sub_zero,Nat.add_zero]
  rw [unshifted_sum]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))

end ContingencyTables.InitializationBrackets

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialLocalChoices
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initialization brackets are actual sums over remaining row labels -/

namespace ContingencyTables.InitialLocalChoices

open scoped BigOperators Classical
open Nat
open InitializationBrackets

/-- Enumerating all choices of the remaining row labels gives exactly
the binomial/factorial bracket, including empty local spaces. -/
theorem sum_localWeight (b u v : ℕ) :
    (∑ S : Finset (Fin (b-u-v)), localWeight b u v S)=bracket b u v := by
  have h := Finset.sum_powerset_apply_card
    (fun k => ((k+v)!:ℝ)*((b-u-v-k+v)!:ℝ)/(b !:ℝ))
    (x := (Finset.univ : Finset (Fin (b-u-v))))
  simpa [localWeight,bracket,nsmul_eq_mul,Finset.sum_div,mul_div_assoc,mul_assoc] using h

/-- Independent choices in the cells factor exactly; the expression is
a finite combinatorial sum before evaluating its four bracket cases. -/
theorem sum_independent_choices {C : Type*} [Fintype C] (b u v : C → ℕ) :
    (∑ S : ((c : C) → Finset (Fin (b c-u c-v c))),
      ∏ c, localWeight (b c) (u c) (v c) (S c))=
      ∏ c, bracket (b c) (u c) (v c) := by
  rw [← Fintype.prod_sum]
  simp_rw [sum_localWeight]

end ContingencyTables.InitialLocalChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

lemma width_cell (c : C) : width (cell b) c=b c := by
  rw [width_eq_sum,Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c then 1 else 0)=
        if x=c then b x else 0 := by
    by_cases hx : x=c
    · subst x
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then b x else 0)=b c by simp) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma row_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c false=(S c).card := by
  unfold viewCount
  rw [Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c ∧ ((⟨x,k⟩,false):Copy b×Bool)∈encode b S then 1 else 0)=
        if x=c then (S c).card else 0 := by
    by_cases hx : x=c
    · subst x
      simp only [cell,true_and,encode_false]
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then (S c).card else 0)=(S c).card by simp) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma column_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c true=b c-(S c).card := by
  have h := plain_counts (cell b) (encode b S) (encode_plain b S) c
  rw [row_count,width_cell] at h
  omega

lemma firstLift_encode (M : ℝ) (S : (c : C) → Finset (Fin (b c))) :
    firstLift (group (cell b)) (fun _ => M) (denominator b) (encode b S)=
      M*∏ c, localWeight (b c) 0 0 (S c) := by
  unfold firstLift FactorialSignatures.factorialProduct denominator
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,groupCount_eq_viewCount,row_count,column_count]
  simp only [localWeight,Nat.sub_zero,Nat.add_zero]
  rw [Finset.prod_div_distrib]
  have he : (∏ c, ((b c-(S c).card)!:ℝ)*((S c).card !:ℝ))=
      ∏ c, ((S c).card !:ℝ)*((b c-(S c).card)!:ℝ) := by
    apply Finset.prod_congr rfl
    intro c _
    exact mul_comm _ _
  rw [he]
  ring

/-- The actual paired-transversal total at a constant raw completion
count M is exactly the manuscript's M*product(b+1). -/
theorem slotTotal_constant (M : ℝ) :
    slotTotal pairs (firstLift (group (cell b)) (fun _ => M) (denominator b)) ∅=
      M*∏ c, ((b c:ℝ)+1) := by
  rw [slotTotal_eq_plain_sum pairs PairedLabels.fresh PairedLabels.cover]
  rw [Finset.sum_subtype (p := PlainState (pairs : List ((Copy b×Bool)×(Copy b×Bool)))) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Fin (b c))), M*∏ c, localWeight (b c) 0 0 (S c) := by
      apply Fintype.sum_equiv (plainEquivChoices b)
      intro S
      have h := firstLift_encode b M ((plainEquivChoices b) S)
      have he : encode b ((plainEquivChoices b) S)=S.val :=
        congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
      rwa [he] at h
    _ = _ := by
      rw [← Finset.mul_sum]
      have he := sum_independent_choices b (fun _ => 0) (fun _ => 0)
      simp only [Nat.sub_zero] at he
      rw [he]
      simp_rw [InitializationBrackets.bracket_neither]

end ContingencyTables.InitialTransversals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialization
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact initial normalizer for the literal companion completion count -/

namespace ContingencyTables.CompanionInitialization

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_zero (A : Instance I J) (z : View A → ℕ) : h A 0 z=freeTotal A :=
  ForestCountIdentification.sourceMarginal_zero A.small A.T A.d A.b A.r A.c z

theorem denominator_eq (A : Instance I J) :
    CompanionFactorialApplication.denominator A=
      InitialTransversals.denominator (fun s : SmallCell A => A.b s.val.1 s.val.2) := by
  unfold CompanionFactorialApplication.denominator TwoLiftStates.denominator InitialTransversals.denominator
  simp_rw [label_width]

/-- C(0) is derived for the actual source f, using the finite
paired-transversal enumeration and the literal free-completion count. -/
theorem total_zero (A : Instance I J) :
    slotTotal pairs (f A 0) ∅=freeTotal A*∏ s : SmallCell A, ((A.b s.val.1 s.val.2:ℝ)+1) := by
  have he : f A 0=firstLift (group (labelCell A)) (fun _ => freeTotal A)
      (CompanionFactorialApplication.denominator A) := by
    funext S
    unfold f firstLift
    rw [h_zero]
  rw [he,denominator_eq]
  convert InitialTransversals.slotTotal_constant
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (freeTotal A) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

end ContingencyTables.CompanionInitialization

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionReferenceAccuracy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative accuracy of the literal companion ratio estimator

The source's tolerance epsilon/(200(H+1)) turns the proved accumulated
logarithmic error into the required multiplicative error. The terminal
contamination bound supplies the remaining error term.
-/

namespace ContingencyTables.CompanionReferenceAccuracy

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication

theorem relative_of_log_error (epsilon R : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hR : 0 < R) (herr : |Real.log R| ≤ epsilon/50) :
    1-epsilon/4 ≤ R ∧ R ≤ 1+epsilon/4 := by
  have hl := Real.log_le_sub_one_of_pos hR
  have hu := Real.one_sub_inv_le_log_of_pos hR
  have he := abs_le.mp herr
  have hinv : 1-epsilon/50 ≤ R⁻¹ := by linarith
  have hm := mul_le_mul_of_nonneg_right hinv hR.le
  rw [inv_mul_cancel₀ hR.ne'] at hm
  have hc : (1-epsilon/50)*(1+epsilon/4) ≥ 1 := by
    nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1.le)]
  constructor
  · linarith
  · exact le_of_mul_le_mul_left (hm.trans hc) (show 0 < 1-epsilon/50 by linarith)

end ContingencyTables.CompanionReferenceAccuracy

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMedianConfidence
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational medians with real target intervals -/

namespace ContingencyTables.FiniteMedianConfidence

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

/-- Rational thresholds used only in the proof permit direct reuse of
finite median amplification when the intended target is a real number. -/
theorem median_confidence_real {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (L L' U' U : ℝ) (hL : L < L') (hU : U' < U)
    (delta : ℚ) (hdelta : 0 < delta)
    (hbad : uniformAverage (fun x =>
      if (output x:ℝ) < L' ∨ U' < (output x:ℝ) then (1:ℝ) else 0) ≤ 5/16) :
    1-(delta:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount delta) → X =>
      if L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U
      then (1:ℝ) else 0) := by
  obtain ⟨a,haL,haL'⟩ := exists_rat_btwn hL
  obtain ⟨b,hU'b,hbU⟩ := exists_rat_btwn hU
  have hab : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0) ≤ 5/16 := by
    apply (uniformAverage_mono _ _ (fun x => ?_)).trans hbad
    simp only [outsideInterval,decide_eq_true_eq]
    by_cases hn : ¬(a ≤ output x ∧ output x ≤ b)
    · have hor : output x < a ∨ b < output x := by
        by_cases ha : output x < a
        · exact Or.inl ha
        · right
          by_contra hb
          exact hn ⟨le_of_not_gt ha,le_of_not_gt hb⟩
      have ht : (output x:ℝ) < L' ∨ U' < (output x:ℝ) := by
        rcases hor with ha|hb
        · left
          exact lt_trans (by exact_mod_cast ha) haL'
        · right
          exact lt_trans hU'b (by exact_mod_cast hb)
      simp [hn,ht]
    · simp only [hn,ite_false]
      split_ifs <;> norm_num
  have hm := median_confidence output a b delta hdelta hab
  apply hm.trans
  apply uniformAverage_mono
  intro xs
  by_cases hg : a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
      rationalMedian (List.ofFn (fun i => output (xs i))) ≤ b
  · have hreal : L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U :=
      ⟨le_trans haL.le (by exact_mod_cast hg.1),le_trans (by exact_mod_cast hg.2) hbU.le⟩
    simp [hg,hreal]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

end

end ContingencyTables.FiniteMedianConfidence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication
open CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma initial_positive (A : Instance I J) (p q : Pair A) : 0 < initial A p q := by
  unfold initial
  split_ifs <;> positivity

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error contributed by the actual fresh weight calls in a phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open scoped BigOperators Classical

noncomputable section

lemma average_ext_instances {X : Type*} (s t : Fintype X) (f g : X → ℝ)
    (h : ∀ x,f x=g x) : @uniformAverage X s f=@uniformAverage X t g := by
  cases Subsingleton.elim s t
  exact congrArg (@uniformAverage X s) (funext h)

lemma failure_of_success {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) (delta : ℝ)
    (h : 1-delta ≤ uniformAverage (fun x => if P x then (1:ℝ) else 0)) :
    uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ delta := by
  have hp (x : X) : (if P x then (1:ℝ) else 0)+(if ¬P x then 1 else 0)=1 := by
    by_cases hx : P x <;> simp [hx]
  have he := uniformAverage_add (fun x => if P x then (1:ℝ) else 0)
    (fun x => if ¬P x then (1:ℝ) else 0)
  simp_rw [hp] at he
  rw [uniformAverage_const] at he
  linarith

end

end ContingencyTables.CompanionPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestBoxCardinality
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The expanded physical forest box still has a short cardinality bound

The tree interval width 20db has at most (b+1)^2 integer positions
when every large capacity is at least 20d. This provides a uniform bound
for the positive equality-softened balanced sums before taking limits.
-/

namespace ContingencyTables.ForestBoxCardinality

open scoped BigOperators Classical
open CompanionFactorialApplication ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

lemma width_add_one_le_square (A : Instance I J) (hW : 20*A.d ≤ A.W) (i : I) (j : J) :
    width A.T A.d A.b i j+1 ≤ (A.b i j+1)^2 := by
  unfold width
  split_ifs with ht
  · have hs : A.small i j=false := A.hTG ht
    have hb : 20*A.d ≤ A.b i j := hW.trans (A.hlarge i j hs).1
    nlinarith
  · nlinarith

theorem cardinality_le_square (A : Instance I J) (hW : 20*A.d ≤ A.W) :
    Fintype.card (Assignments A) ≤ (∏ a : I×J,(A.b a.1 a.2+1))^2 := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_fin]
  calc
    _ ≤ ∏ a : I×J,(A.b a.1 a.2+1)^2 := by
      apply Finset.prod_le_prod'
      intro a _
      exact width_add_one_le_square A hW a.1 a.2
    _ = _ := Finset.prod_pow Finset.univ 2 (fun a : I×J => A.b a.1 a.2+1)

/-- The full balanced physical box, including every expanded tree
interval, has at most 2^K profiles under the source's bit-size allowance. -/
theorem cardinality_le_two_pow (A : Instance I J) (hW : 20*A.d ≤ A.W)
    (L K : ℕ) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L) (hK : 2*L ≤ K) :
    Fintype.card (Assignments A) ≤ 2^K := by
  calc
    _ ≤ (∏ a : I×J,(A.b a.1 a.2+1))^2 := cardinality_le_square A hW
    _ ≤ (2^L)^2 := Nat.pow_le_pow_left hL 2
    _ = 2^(2*L) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hK

end ContingencyTables.ForestBoxCardinality

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBalancedMarginal
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Balanced marginal closure at capacities zero and one

Capacity one has two old quadratic blocks with a common mixed
functional. Each fresh coordinate is isotropic. This proves closure
directly on the raw integer forms, including the small cells that must
be eliminated to obtain an actual tree-coordinate marginal.
-/

namespace ContingencyTables

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)

theorem isotropic_kernel_nonpositive
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : BilinForm ℝ V) (hsymm : ∀ x y, B x y=B y x)
    (hsig : OnePositiveDirection B) (e w : V)
    (hee : B e e=0) (hew : B e w≠0)
    (v : V) (hev : B e v=0) : B v v ≤ 0 := by
  by_contra hn
  have hv : 0 < B v v := lt_of_not_ge hn
  let u := w-(B v w/B v v) • v
  have hvu : B v u=0 := by
    simp only [u,LinearMap.BilinForm.sub_right,LinearMap.BilinForm.smul_right]
    field_simp [hv.ne']
    ring
  have heu : B e u=B e w := by
    simp only [u,LinearMap.BilinForm.sub_right,LinearMap.BilinForm.smul_right,hev,
      mul_zero,sub_zero]
  have hue : B u e=B e w := by rw [hsymm,heu]
  have hve : B v e=0 := by rw [hsymm,hev]
  let t := (1-B u u)/(2*B e w)
  have horth : B v (u+t • e)=0 := by
    simp only [LinearMap.BilinForm.add_right,LinearMap.BilinForm.smul_right,hvu,hve,
      mul_zero,add_zero]
  have hsquare : B (u+t • e) (u+t • e)=1 := by
    simp only [LinearMap.BilinForm.add_left,LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,hee,heu,hue,mul_zero,add_zero]
    dsimp only [t]
    field_simp [hew]
    ring
  have hh := hsig v hv (u+t • e) horth
  rw [hsquare] at hh
  norm_num at hh

namespace IntegerMarginal

open CommonBasesFPRAS FactorialSignatures BalancedBox

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem marginal_zero_removal_slice (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R : ℕ)
    (hsig : RemovalSlice F (profile m 0 0) R) :
    RemovalSlice (marginal F 0) m R := by
  intro z hz ht
  have hs := hsig (profile z 0 0)
    (profile_inBox m z 0 0 0 hz le_rfl le_rfl)
    (by simp only [profile_total,ht,add_zero])
  rw [marginal_old_block]
  simp only [Nat.zero_add,Finset.sum_range_one]
  intro u hu v huv
  exact hs (old u) hu (old v) huv

lemma removeOne_total (z : I → ℕ) (i : I) (hi : 0 < z i) :
    (∑ u,removeOne z i u)+1=∑ u,z u := by
  have he : ∀ u,removeOne z i u+(if u=i then 1 else 0)=z u := by
    intro u
    by_cases hu : u=i
    · subst u
      simp only [removeOne,ite_true, if_true]
      omega
    · simp [removeOne,hu]
  have hh := congrArg (fun f : I → ℕ => ∑ u,f u) (funext he)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] using hh

theorem marginal_one_removal_slice (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R : ℕ)
    (hpos : PositiveSlice F (profile m 1 1) (R+1))
    (hsig : RemovalSlice F (profile m 1 1) (R+1)) :
    RemovalSlice (marginal F 1) m R := by
  intro z hz ht
  have hex : ∃ i,0 < z i := by
    by_contra hn
    push Not at hn
    have hz0 : ∀ i,z i=0 := fun i => Nat.eq_zero_of_le_zero (hn i)
    simp only [hz0,Finset.sum_const_zero] at ht
    omega
  obtain ⟨i,hi⟩ := hex
  let B (j : ℕ) := (pairMatrix F 1 z j).toBilin'
  let ell : (I → ℝ) →ₗ[ℝ] ℝ := cross F 1 z 1
  have hsigB (j : ℕ) (hj : j ≤ 1) : OnePositiveDirection (B j) := by
    apply hsig _ (profile_inBox m z 1 j (1-j) hz hj (Nat.sub_le _ _))
    rw [profile_total,ht]
    omega
  have he0 : B 0 (Pi.single (.inr true) 1) (Pi.single (.inr true) 1)=0 := by
    simp [B,Matrix.toBilin'_apply,pairMatrix_bb,innerWeight]
  have he1 : B 1 (Pi.single (.inr false) 1) (Pi.single (.inr false) 1)=0 := by
    simp [B,Matrix.toBilin'_apply,pairMatrix_aa,innerWeight]
  have hcross0 (v : I → ℝ) : B 0 (old v) (Pi.single (.inr true) 1)=ell v :=
    cross_b F 1 z 0 (by omega) v
  have hcross1 (v : I → ℝ) : B 1 (old v) (Pi.single (.inr false) 1)=ell v :=
    cross_a F 1 z 1 le_rfl v
  have hpositive : 0 < F (profile (removeOne z i) 0 0) := by
    apply hpos _ (profile_inBox m (removeOne z i) 1 0 0
      (fun u => (Nat.sub_le _ _).trans (hz u)) (by omega) (by omega))
    have hh := removeOne_total z i hi
    rw [profile_total]
    omega
  have hell : ell (Pi.single i 1)≠0 := by
    have hv : ValidPair (profile z 1 0) (.inl i) (.inr false) := by
      simp [ValidPair,profile,hi]
    have he : ell (Pi.single i 1)=F (profile (removeOne z i) 0 0) := by
      dsimp only [ell]
      rw [← cross_a F 1 z 1 le_rfl,old_single]
      simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
      rw [pairMatrix,integerRemovalMatrix,ite_eq_left hv,profile_removeOldA]
    rw [he]
    exact hpositive.ne'
  have hker (v : I → ℝ) (hv : ell v=0) : B 0 (old v) (old v)+B 1 (old v) (old v) ≤ 0 := by
    have hs0 : ∀ x y,B 0 x y=B 0 y x :=
      fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
    have hs1 : ∀ x y,B 1 x y=B 1 y x :=
      fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
    have hh0 := isotropic_kernel_nonpositive (B 0) hs0 (hsigB 0 (by omega))
      (Pi.single (.inr true) 1) (old (Pi.single i 1)) he0
      (by rw [hs0,hcross0]; exact hell) (old v) (by rw [hs0,hcross0,hv])
    have hh1 := isotropic_kernel_nonpositive (B 1) hs1 (hsigB 1 le_rfl)
      (Pi.single (.inr false) 1) (old (Pi.single i 1)) he1
      (by rw [hs1,hcross1]; exact hell) (old v) (by rw [hs1,hcross1,hv])
    linarith
  apply onePositiveDirection_of_kernel _
    (fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y) ell
  intro v hv
  have hh := hker v hv
  rw [marginal_old_block]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    LinearMap.add_apply,LinearMap.compl₁₂_apply,B] using hh

end IntegerMarginal
end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllBalancedWidths
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual balanced finite family allows every small-cell capacity

The proved zero/one boundary cases complete the finite balanced
elimination theorem. The physical equality-softened tree marginal can
therefore eliminate the original small cells directly.
-/

namespace ContingencyTables.BalancedBox

open scoped BigOperators Classical
open IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem marginal_removal_slice_all (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R M : ℕ)
    (hpos : PositiveSlice F (profile m M M) (R+M))
    (hsig : RemovalSlice F (profile m M M) (R+M)) :
    RemovalSlice (marginal F M) m R := by
  rcases M with _|M
  · exact marginal_zero_removal_slice F m R (by simpa only [add_zero] using hsig)
  rcases M with _|M
  · exact marginal_one_removal_slice F m R hpos hsig
  · exact marginal_removal_slice F m R _ (by omega) hpos hsig

end ContingencyTables.BalancedBox

namespace ContingencyTables.BalancedFamily

open scoped BigOperators Classical
open IntegerMarginal BalancedBox

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every original small-cell width, including zero and one, may be
eliminated on its precise box-valid total slice. -/
theorem eliminate_slices_all (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum)) :
    PositiveSlice (eliminate Ms F) m R ∧ RemovalSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil,add_zero,eliminate,bounds] using And.intro hpos hsig
  | cons M Ms ih =>
    have htotal : R+(M::Ms).sum=(R+Ms.sum)+M := by simp only [List.sum_cons]; omega
    rw [htotal] at hpos hsig
    exact ih (marginal F M)
      (marginal_positive_slice F (bounds m Ms) (R+Ms.sum) M hpos)
      (marginal_removal_slice_all F (bounds m Ms) (R+Ms.sum) M hpos hsig)

end ContingencyTables.BalancedFamily

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open EqualitySoftening BalancedFamily BalancedBox

variable {S D G : Type*} [Fintype S] [DecidableEq S] [Fintype D] [Fintype G]

omit [DecidableEq S] in
lemma softenedWeight_reindex (Ms : List ℕ) (e : Coordinates S Ms ≃ D)
    (line : D → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : D → ℝ) (L : ℝ) (z : Coordinates S Ms → ℕ) :
    softenedWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e)
      (uslope ∘ e) (cap ∘ e) L z=
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm) := by
  unfold softenedWeight
  exact productWeight_reindex e line (lineFactor root rate offset slope L)
    (unaryFactor urate ell uslope cap) z

/-- The literal physical positive factor family can retain one tree
pair while summing all other original pairs, at every capacity. -/
theorem physical_softened_slices_all (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ) (L : ℝ)
    (hrate : ∀ g,0 ≤ rate g) (hu : ∀ d,0 ≤ urate d) (hL : 0 ≤ L) :
    PositiveSlice (eliminate Ms (fun z =>
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm))) m R ∧
    RemovalSlice (eliminate Ms (fun z =>
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm))) m R := by
  have heq : (fun z => softenedWeight line root rate offset slope urate ell uslope cap L
      (z ∘ e.symm))=softenedWeight (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L := by
    funext z
    exact (softenedWeight_reindex Ms e line root rate offset slope urate ell uslope cap L z).symm
  rw [heq]
  apply eliminate_slices_all Ms m R
  · intro z _ _
    exact softenedWeight_positive (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L z
  · intro z _ _
    convert softenedWeight_removal (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L hrate (fun i => hu (e i)) hL z using 1
    all_goals try with_reducible_and_instances rfl
    congr 2 <;> exact Subsingleton.elim _ _

end ContingencyTables.EqualityReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PositiveSequenceInterpolation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite log-concave interpolation for the terminal tree marginal

The scalar statement used in the contamination estimate follows from
the actual adjacent two-removal inequality. No continuous extension of
the integer marginal is assumed.
-/

namespace ContingencyTables

open scoped BigOperators

private lemma decreasing_increments_average (g : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k, k+2 ≤ N → g k+g (k+2) ≤ 2*g (k+1))
    (n : ℕ) (hn : n+1 ≤ N) :
    (n:ℝ)*(g (n+1)-g n) ≤ g n-g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha := ih (by omega)
    have hd : g (n+2)-g (n+1) ≤ g (n+1)-g n := by
      linarith [hc n (by omega)]
    have hm := mul_le_mul_of_nonneg_left hd
      (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
    push_cast at hm ⊢
    nlinarith

/-- A finite sequence with decreasing adjacent increments lies above
each secant joining its first point to a later point. -/
theorem discrete_secant (g : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k, k+2 ≤ N → g k+g (k+2) ≤ 2*g (k+1))
    (n : ℕ) (hn : n ≤ N) (k : ℕ) (hk : k ≤ n) :
    (k:ℝ)*(g n-g 0) ≤ (n:ℝ)*(g k-g 0) := by
  induction n with
  | zero =>
    have hk0 : k=0 := by omega
    simp [hk0]
  | succ n ih =>
    by_cases hkn : k ≤ n
    · by_cases hn0 : n=0
      · have hk0 : k=0 := by omega
        simp [hk0]
      · have hi := ih (by omega) hkn
        have ha := decreasing_increments_average g N hc n (by omega)
        have hi' := mul_le_mul_of_nonneg_left hi
          (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
        have ha' := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg k : (0:ℝ) ≤ k)
        have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        push_cast at hi' ⊢
        nlinarith
    · have hke : k=n+1 := by omega
      simp only [hke]
      exact le_rfl

/-- Adjacent log-concavity gives the exact finite logarithmic secant
inequality used for each positive tree-coordinate marginal. -/
theorem positive_sequence_log_secant (a : ℕ → ℝ) (N : ℕ)
    (hp : ∀ k, k ≤ N → 0 < a k)
    (hc : ∀ k, k+2 ≤ N → a k*a (k+2) ≤ (a (k+1))^2)
    (k : ℕ) (hk : k ≤ N) :
    (k:ℝ)*(Real.log (a N)-Real.log (a 0)) ≤
      (N:ℝ)*(Real.log (a k)-Real.log (a 0)) := by
  apply discrete_secant (fun j => Real.log (a j)) N _ N le_rfl k hk
  intro j hj
  have h0 := hp j (by omega)
  have h1 := hp (j+1) (by omega)
  have h2 := hp (j+2) hj
  have hh := Real.log_le_log (mul_pos h0 h2) (hc j hj)
  rw [Real.log_mul h0.ne' h2.ne',Real.log_pow] at hh
  simpa only [Nat.cast_ofNat] using hh

/-- A positive log-concave sequence whose far endpoint has mass at
least one and whose first mass is at most 2^K loses at most a factor
two over the first N/K integer positions. -/
theorem positive_sequence_half_window (a : ℕ → ℝ) (N K : ℕ)
    (hK : 1 ≤ K) (hN : 0 < N)
    (hp : ∀ k, k ≤ N → 0 < a k)
    (hc : ∀ k, k+2 ≤ N → a k*a (k+2) ≤ (a (k+1))^2)
    (hend : 1 ≤ a N) (hfirst : a 0 ≤ (2:ℝ)^K)
    (r : ℕ) (hr : r*K ≤ N) : a 0/2 ≤ a r := by
  have hrN : r ≤ N := by nlinarith
  have h0 := hp 0 (Nat.zero_le N)
  have hr0 := hp r hrN
  have hlog := positive_sequence_log_secant a N hp hc r hrN
  have hlogend : 0 ≤ Real.log (a N) := Real.log_nonneg hend
  have hlogfirst : Real.log (a 0) ≤ (K:ℝ)*Real.log 2 := by
    have hh := Real.log_le_log h0 hfirst
    simpa only [Real.log_pow] using hh
  have htwo : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hrK : (r:ℝ)*K ≤ N := by exact_mod_cast hr
  have hrR : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_left hlogfirst hrR
  have hsum := mul_le_mul_of_nonneg_right hrK htwo
  have hloghalf : Real.log (a 0)-Real.log 2 ≤ Real.log (a r) := by
    nlinarith [mul_nonneg hrR hlogend]
  rw [← Real.log_div h0.ne' (by norm_num : (2:ℝ) ≠ 0)] at hloghalf
  exact (Real.log_le_log_iff (div_pos h0 (by norm_num)) hr0).mp hloghalf

/-- A half-height interpolation window contains enough distinct integer
positions to give the source's normalized exterior point-mass bound. -/
theorem half_window_mass_bound (a : ℕ → ℝ) (U k N K b : ℕ)
    (hK : 0 < K) (hb : 0 < b) (hbN : b ≤ N) (hkN : k+N ≤ U)
    (ha : ∀ j,j ≤ U → 0 ≤ a j)
    (hC : 0 < ∑ j ∈ Finset.range (U+1),a j)
    (hwindow : ∀ r,r*K ≤ N → a k/2 ≤ a (k+r)) :
    a k/(∑ j ∈ Finset.range (U+1),a j) ≤ (2*K:ℝ)/b := by
  let q := N/K+1
  have hkU : k ≤ U := by omega
  have hak : 0 ≤ a k := ha k hkU
  have hsubset : (Finset.range q).image (fun r => k+r) ⊆ Finset.range (U+1) := by
    intro j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    have hrq : r ≤ N/K := by have := Finset.mem_range.mp hr; dsimp only [q] at this; omega
    have hrN : r ≤ N := hrq.trans (Nat.div_le_self _ _)
    exact Finset.mem_range.mpr (by omega)
  have hsum : (∑ r ∈ Finset.range q,a (k+r)) ≤ ∑ j ∈ Finset.range (U+1),a j := by
    rw [← Finset.sum_image (fun r _ s _ hrs => Nat.add_left_cancel hrs)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j hj _ => ha j (by have := Finset.mem_range.mp hj; omega))
  have hheight : (q:ℝ)*(a k/2) ≤ ∑ r ∈ Finset.range q,a (k+r) := by
    calc
      _ = ∑ _r ∈ Finset.range q,a k/2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro r hr
        apply hwindow
        have hrq : r ≤ N/K := by have := Finset.mem_range.mp hr; dsimp only [q] at this; omega
        exact (Nat.mul_le_mul_right K hrq).trans (Nat.div_mul_le_self _ _)
  have hcountNat : b ≤ K*q := hbN.trans (Nat.lt_mul_div_succ N hK).le
  have hcount : (b:ℝ) ≤ (K:ℝ)*(q:ℝ) := by exact_mod_cast hcountNat
  have hmass := hheight.trans hsum
  have hm1 := mul_le_mul_of_nonneg_right hcount (div_nonneg hak (by norm_num : (0:ℝ) ≤ 2))
  have hm2 := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg K : (0:ℝ) ≤ K)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_le_div_iff₀ hC hbR]
  nlinarith

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedCellFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact one-cell fibres of the physical balanced profile sum -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical

variable {C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] in
lemma join_at (M : C → ℕ) (t : C) (k : Fin (M t+1)) (a : Others M t) :
    join M t k a t=k := by
  exact congrArg Prod.fst ((Equiv.piSplitAt t (fun c => Fin (M c+1))).apply_symm_apply (k,a))

omit [Fintype C] in
lemma join_other (M : C → ℕ) (t : C) (k : Fin (M t+1)) (a : Others M t)
    (c : {c : C // c≠t}) : join M t k a c.val=a c := by
  exact congrFun (congrArg Prod.snd
    ((Equiv.piSplitAt t (fun c => Fin (M c+1))).apply_symm_apply (k,a))) c

/-- The fibre has no multiplicity: choosing the retained cell fixes
that coordinate and leaves exactly the independent choices elsewhere. -/
theorem fibre_eq_sum (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (k : Fin (M t+1)) :
    fibre M F t k=∑ a : Others M t,F (profile M (join M t k a)) := by
  let e := Equiv.piSplitAt t (fun c => Fin (M c+1))
  have he : (∑ a : Profiles M,if a t=k then F (profile M a) else 0)=
      ∑ p : Fin (M t+1)×Others M t,if p.1=k then F (profile M (e.symm p)) else 0 := by
    apply Fintype.sum_equiv e
    intro a
    simp only [Equiv.symm_apply_apply]
    rfl
  unfold fibre
  rw [he,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  rfl

/-- The actual one-cell fibres partition the full physical finite sum. -/
theorem sum_fibre (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ) (t : C) :
    (∑ k : Fin (M t+1),fibre M F t k)=∑ a : Profiles M,F (profile M a) := by
  unfold fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

end ContingencyTables.BalancedCellFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical one-cell marginal is exactly its balanced assignment fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication LargePairEnumeration
open PhysicalLargeProfiles BalancedFamily BalancedEnumeration BalancedCellFibres
open IntegerWeightedTransport

variable {I J : Type*} [Fintype I] [Fintype J]

lemma one_view_reindex (A : Instance I J) (t : I×J) (z : Bool → ℕ)
    (a : (k : Fin (Fintype.card (LargeCell (keep t)))) → Fin (otherWidths A t k+1)) :
    joinedProfile (otherWidths A t) z a ∘
      ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
        (physicalJoinEquiv (keep t) (enumeration t))).symm=
      joinedProfile (otherWidths A t) (z ∘ singleView t) a ∘
        (physicalJoinEquiv (keep t) (enumeration t)).symm := by
  funext u
  change joinedProfile (otherWidths A t) z a
    ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).symm
      ((physicalJoinEquiv (keep t) (enumeration t)).symm u))=
    joinedProfile (otherWidths A t) (z ∘ singleView t) a
      ((physicalJoinEquiv (keep t) (enumeration t)).symm u)
  generalize (physicalJoinEquiv (keep t) (enumeration t)).symm u=q
  cases q <;> rfl

lemma eliminate_eq_view_sum (A : Instance I J) (t : I×J)
    (F : ((I×J)×Bool → ℕ) → ℝ) (z : Bool → ℕ) :
    eliminate (widths (otherWidths A t)) (fun q => F (q ∘ (coordinateEquiv A t).symm)) z=
      ∑ a : ((k : Fin (Fintype.card (LargeCell (keep t)))) → Fin (otherWidths A t k+1)),
        F (joinedProfile (otherWidths A t) (z ∘ singleView t) a ∘
          (physicalJoinEquiv (keep t) (enumeration t)).symm) := by
  change eliminate (widths (otherWidths A t)) (fun q =>
    F ((q ∘ (LargePairEnumeration.coordinateEquiv Bool (otherWidths A t)).symm) ∘
      ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
        (physicalJoinEquiv (keep t) (enumeration t))).symm)) z=_
  rw [LargePairEnumeration.eliminate_eq_physical_sum (otherWidths A t)
    (fun q => F (q ∘ ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
      (physicalJoinEquiv (keep t) (enumeration t))).symm)) z]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg F (one_view_reindex A t z a)

theorem eliminate_eq_one_cell_sum (A : Instance I J) (t : I×J)
    (F : ((I×J)×Bool → ℕ) → ℝ) (z : Bool → ℕ) :
    eliminate (widths (otherWidths A t)) (fun q => F (q ∘ (coordinateEquiv A t).symm)) z=
      ∑ a : PhysicalAssignments (keep t) (cellWidth A),
        F (physicalProfile (keep t) (cellWidth A) (z ∘ singleView t) a) := by
  rw [eliminate_eq_view_sum]
  convert sum_joined_eq_physical (keep t) (cellWidth A) (enumeration t) (z ∘ singleView t) F using 1
  · rfl
  · apply Finset.sum_congr
    · ext a
      simp
    · intro a _
      rfl

lemma physical_one_cell_profile (A : Instance I J) (t : I×J)
    (k : Fin (cellWidth A t+1)) (a : BalancedCellFibres.Others (cellWidth A) t) :
    physicalProfile (keep t) (cellWidth A) (childProfile (cellWidth A t) k.val ∘ singleView t)
      ((Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
        (otherCells t)).symm a)=
      BalancedCellFibres.profile (cellWidth A) (join (cellWidth A) t k a) := by
  funext u
  rcases u with ⟨c,b⟩
  by_cases hc : c=t
  · subst c
    cases b <;> simp [physicalProfile,keep,singleView,BalancedCellFibres.profile,join_at] <;> rfl
  · have hkeep : keep t c=false := by simp only [keep,decide_eq_false_iff_not]; exact hc
    simp only [physicalProfile,hkeep,Bool.false_eq_true,dite_false,BalancedCellFibres.profile]
    rw [join_other (cellWidth A) t k a ⟨c,hc⟩]
    rfl

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedPhysicalPartition
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning actual balanced profiles into small and large cells -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical
open PhysicalLargeProfiles LargePairEnumeration

variable {C : Type*}

lemma partition_profile (small : C → Bool) (M : C → ℕ)
    (a : SmallProfiles small M×PhysicalAssignments small M) :
    profile M ((partition small M).symm a)=
      physicalProfile small M (smallDisplay small M a.1) a.2 := by
  funext p
  rcases p with ⟨c,b⟩
  by_cases hs : small c=true
  · simp only [profile,partition,Equiv.coe_fn_symm_mk,physicalProfile,hs,dite_eq_left,smallDisplay]
  · simp only [profile,partition,Equiv.coe_fn_symm_mk,physicalProfile,hs,Bool.false_eq_true,dite_false]

end ContingencyTables.BalancedCellFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TransversalCount
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact binomial/factorial cancellation in a transversal normalizer

Every small integer profile has a product of binomial numbers of label
preimages. Its factorial lift contributes the inverse product, so the
actual transversal normalizer is exactly the raw integer-profile sum.
-/

namespace ContingencyTables.TransversalCount

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialTransversals InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

omit [Fintype C] in
lemma local_fiber (c : C) (x : Fin (b c+1)) :
    (∑ S : Finset (Fin (b c)), if cardAt b c S=x then InitialLocalChoices.localWeight (b c) 0 0 S else 0)=1 := by
  have hx : x.val≤b c := by have := x.isLt; omega
  have h := Finset.sum_powerset_apply_card
    (fun k => if k=x.val then ((k.factorial:ℝ)*((b c-k).factorial:ℝ))/(b c).factorial else 0)
    (x := (Finset.univ : Finset (Fin (b c))))
  have he : (∑ S : Finset (Fin (b c)), if S.card=x.val then
      ((S.card.factorial:ℝ)*((b c-S.card).factorial:ℝ))/(b c).factorial else 0)=
      ((b c).choose x.val:ℝ)*((x.val.factorial:ℝ)*((b c-x.val).factorial:ℝ))/(b c).factorial := by
    simpa [nsmul_eq_mul,mul_ite,mul_div_assoc,Finset.mem_range,show x.val<b c+1 by omega] using h
  have hf : ((b c).choose x.val:ℝ)*(x.val.factorial:ℝ)*((b c-x.val).factorial:ℝ)=((b c).factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hx
  calc
    _ = ∑ S : Finset (Fin (b c)), if S.card=x.val then
        ((S.card.factorial:ℝ)*((b c-S.card).factorial:ℝ))/(b c).factorial else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      simp only [cardAt,Fin.ext_iff,InitialLocalChoices.localWeight,Nat.sub_zero,Nat.add_zero]
    _ = _ := he
    _ = 1 := by rw [← mul_assoc,hf]; exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

lemma profile_fiber (x : Profile b) :
    (∑ S : ((c : C) → Finset (Fin (b c))),if cardProfile b S=x then
      ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) else 0)=1 := by
  calc
    _ = ∏ c,∑ S : Finset (Fin (b c)),if cardAt b c S=x c then
          InitialLocalChoices.localWeight (b c) 0 0 S else 0 := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Fintype.prod_ite_zero]
      congr 1
      exact propext funext_iff
    _ = ∏ _c : C,(1:ℝ) := by
      apply Finset.prod_congr rfl
      intro c _
      exact local_fiber b c (x c)
    _ = 1 := by simp

/-- Pushforward of the actual finite labelled-choice weights is counting
measure on the bounded integer profiles. -/
theorem choices_sum (H : Profile b → ℝ) :
    (∑ S : ((c : C) → Finset (Fin (b c))),H (cardProfile b S)*
      ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c))=∑ x : Profile b,H x := by
  calc
    _ = ∑ x : Profile b,H x*∑ S : ((c : C) → Finset (Fin (b c))),
        if cardProfile b S=x then ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      simp [mul_ite]
    _ = _ := by simp_rw [profile_fiber]; simp

lemma count_encode (S : (c : C) → Finset (Fin (b c))) :
    groupCount (group (cell b)) (InitialTransversals.encode b S)=display b (cardProfile b S) := by
  funext u
  rcases u with ⟨c,t⟩
  rw [groupCount_eq_viewCount]
  cases t
  · exact InitialTransversals.row_count b S c
  · exact InitialTransversals.column_count b S c

lemma firstLift_encode (h : (C×Bool → ℕ) → ℝ) (S : (c : C) → Finset (Fin (b c))) :
    firstLift (group (cell b)) h (InitialTransversals.denominator b) (InitialTransversals.encode b S)=
      h (display b (cardProfile b S))*∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) := by
  calc
    _ = firstLift (group (cell b)) (fun _ => h (display b (cardProfile b S)))
        (InitialTransversals.denominator b) (InitialTransversals.encode b S) := by
      unfold firstLift
      rw [count_encode]
    _ = _ := InitialTransversals.firstLift_encode b _ S

/-- The literal factorial lift's transversal normalizer is the original
integer-profile count, for arbitrary raw h and arbitrary capacities. -/
theorem slotTotal_eq_profiles (h : (C×Bool → ℕ) → ℝ) :
    slotTotal pairs (firstLift (group (cell b)) h (InitialTransversals.denominator b)) ∅=
      ∑ x : Profile b,h (display b x) := by
  rw [slotTotal_eq_plain_sum pairs PairedLabels.fresh PairedLabels.cover]
  rw [Finset.sum_subtype (p := PlainState (pairs : List ((Copy b×Bool)×(Copy b×Bool)))) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Fin (b c))),h (display b (cardProfile b S))*
        ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) := by
      apply Fintype.sum_equiv (plainEquivChoices b)
      intro S
      have ht := firstLift_encode b h ((plainEquivChoices b) S)
      have he : InitialTransversals.encode b ((plainEquivChoices b) S)=S.val :=
        congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
      rwa [he] at ht
    _ = _ := choices_sum b (fun x => h (display b x))

end ContingencyTables.TransversalCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalNormalizer
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual companion normalizer equals the full physical balanced mass -/

namespace ContingencyTables.CompanionPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open ForestPenaltyApplication ForestCountIdentification

variable {I J : Type*} [Fintype I] [Fintype J]

lemma small_display_eq (A : Instance I J)
    (s : SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A)) :
    smallDisplay (fun a : I×J => A.small a.1 a.2) (cellWidth A) s=
      TransversalCount.display (fun s : SmallCell A => A.b s.val.1 s.val.2) (smallProfilesEquiv A s) := by
  funext u
  rcases u with ⟨a,b⟩
  cases b
  · rfl
  · change cellWidth A a.val-(s a).val=A.b a.val.1 a.val.2-(s a).val
    exact congrArg (fun n : ℕ => n-(s a).val) (small_width A a)

end ContingencyTables.CompanionPhysicalNormalizer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeFeasibleMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every feasible table contributes one unit to its actual cell fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount
open BalancedCellFibres EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

lemma tableAssignment_row (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (i : I) (j : J) :
    physicalRow (lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j=(Y i j:ℝ) := by
  have hz : 0 ≤ Y i j-lower A.T A.d A.b i j := by
    linarith [(hY i j).1,lower_nonpositive A i j]
  simp only [physicalRow,BalancedCellFibres.profile,Bool.false_eq_true,ite_false,tableAssignment]
  have hn : (((Y i j-lower A.T A.d A.b i j).toNat:ℕ):ℝ)=
      (Y i j:ℝ)-(lower A.T A.d A.b i j:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  rw [hn]
  ring

lemma tableAssignment_column (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (i : I) (j : J) :
    physicalColumn (lower A.T A.d A.b) (width A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j=(Y i j:ℝ) := by
  have hk : (tableAssignment A Y hY (i,j)).val ≤ cellWidth A (i,j) :=
    Nat.le_of_lt_succ (tableAssignment A Y hY (i,j)).isLt
  have hh := tableAssignment_row A Y hY i j
  simp only [physicalColumn,BalancedCellFibres.profile,ite_true, if_true,Nat.cast_sub hk]
  change (lower A.T A.d A.b i j:ℝ)+(cellWidth A (i,j):ℝ)-
    ((cellWidth A (i,j):ℝ)-((tableAssignment A Y hY (i,j)).val:ℝ))=(Y i j:ℝ)
  change (lower A.T A.d A.b i j:ℝ)+((tableAssignment A Y hY (i,j)).val:ℝ)=(Y i j:ℝ) at hh
  linarith

lemma tableAssignment_tree_index (A : Instance I J) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) :
    ((tableAssignment A Y hY t).val:ℤ)=Y t.1 t.2+(10*A.d*A.b t.1 t.2:ℕ) := by
  have hz : 0 ≤ Y t.1 t.2-lower A.T A.d A.b t.1 t.2 := by
    linarith [(hY t.1 t.2).1,lower_nonpositive A t.1 t.2]
  change ((Y t.1 t.2-lower A.T A.d A.b t.1 t.2).toNat:ℤ)=_
  rw [Int.toNat_of_nonneg hz]
  simp only [lower,ht,ite_true, if_true,sub_neg_eq_add]

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhysicalTables
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasible physical balanced profiles are exactly bounded contingency tables -/

namespace ContingencyTables.CompanionPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

lemma assignment_physicalTable (A : Instance I J) (a : Profiles (cellWidth A))
    (ha : ∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j) :
    tableAssignment A (physicalTable A a) ha=a := by
  funext c
  apply Fin.ext
  simp only [tableAssignment,physicalTable,add_sub_cancel_left,Int.toNat_natCast]

theorem cardinality_eq (A : Instance I J) :
    Fintype.card (PhysicalTables A)=
      Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b) :=
  Fintype.card_congr (tablesEquiv A)

end ContingencyTables.CompanionPhysicalTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeExteriorPositions
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The narrow exterior tree intervals contain fewer than 2 gamma b positions -/

namespace ContingencyTables.TreeExteriorPositions

open scoped Classical

private lemma positive_integer_positions {C : Type*} [Fintype C] (q : C → ℤ)
    (hq : Function.Injective q) (delta : ℝ) (hd : 0 < delta) :
    ((Finset.univ.filter (fun c => 0 < q c ∧ (q c:ℝ) < delta)).card:ℝ) ≤ delta := by
  let S := Finset.univ.filter (fun c => 0 < q c ∧ (q c:ℝ) < delta)
  have hm : Set.MapsTo (fun c => (q c).toNat) S (Finset.Ico 1 (Nat.ceil delta)) := by
    intro c hc
    have hh := (Finset.mem_filter.mp hc).2
    have hn : (0:ℤ) ≤ q c := hh.1.le
    have hcast : ((q c).toNat:ℝ)=(q c:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    apply Finset.mem_Ico.mpr
    constructor
    · have hv := Int.toNat_of_nonneg hn
      have hpos : 0 < q c := hh.1
      have hcast : (1:ℤ) ≤ ((q c).toNat:ℤ) := by rw [hv]; omega
      exact_mod_cast hcast
    · have hhR : ((q c).toNat:ℝ) < (Nat.ceil delta:ℝ) := by rw [hcast]; exact hh.2.trans_le (Nat.le_ceil delta)
      exact_mod_cast hhR
  have hi : (S:Set C).InjOn (fun c => (q c).toNat) := by
    intro c hc c' hc' he
    apply hq
    have hh := (Finset.mem_filter.mp hc).2.1.le
    have hh' := (Finset.mem_filter.mp hc').2.1.le
    have h := congrArg (fun n : ℕ => (n:ℤ)) he
    simpa only [Int.toNat_of_nonneg hh,Int.toNat_of_nonneg hh'] using h
  have hc := Finset.card_le_card_of_injOn (fun c => (q c).toNat) hm hi
  rw [Nat.card_Ico] at hc
  have hceil : 1 ≤ Nat.ceil delta := Nat.one_le_ceil_iff.mpr hd
  have hceilR : ((Nat.ceil delta-1:ℕ):ℝ) ≤ delta := by
    rw [Nat.cast_sub hceil]
    have hh := Nat.ceil_lt_add_one hd.le
    push_cast
    linarith
  exact (by exact_mod_cast hc : (S.card:ℝ) ≤ (Nat.ceil delta-1:ℕ)).trans hceilR

/-- Strict exterior distances avoid an additive rounding error even
when gamma*b is smaller than one. -/
theorem card_positions_le (ell : ℤ) (b U : ℕ) (delta : ℝ) (hd : 0 < delta) :
    ((positions ell b U delta).card:ℝ) ≤ 2*delta := by
  let L := Finset.univ.filter (fun k : Fin (U+1) =>
    0 < -(ell+(k.val:ℤ)) ∧ ((-(ell+(k.val:ℤ)):ℤ):ℝ)<delta)
  let R := Finset.univ.filter (fun k : Fin (U+1) =>
    0 < ell+(k.val:ℤ)-(b:ℤ) ∧ ((ell+(k.val:ℤ)-(b:ℤ):ℤ):ℝ)<delta)
  have hL : (L.card:ℝ) ≤ delta := by
    apply positive_integer_positions (fun k : Fin (U+1) => -(ell+(k.val:ℤ))) _ delta hd
    intro k k' he
    dsimp only at he
    apply Fin.ext
    have hh : (k.val:ℤ)=(k'.val:ℤ) := by omega
    exact_mod_cast hh
  have hR : (R.card:ℝ) ≤ delta := by
    apply positive_integer_positions (fun k : Fin (U+1) => ell+(k.val:ℤ)-(b:ℤ)) _ delta hd
    intro k k' he
    dsimp only at he
    apply Fin.ext
    have hh : (k.val:ℤ)=(k'.val:ℤ) := by omega
    exact_mod_cast hh
  have he : positions ell b U delta=L∪R := by
    ext k
    simp only [positions,L,R,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      neg_pos,sub_pos,Int.cast_neg,Int.cast_sub,Int.cast_natCast]
  rw [he]
  have hc : ((L∪R).card:ℝ) ≤ (L.card:ℝ)+(R.card:ℝ) := by exact_mod_cast Finset.card_union_le L R
  linarith

end ContingencyTables.TreeExteriorPositions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_SoftWeightUpper
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform upper mass of the positive physical softening family -/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical
open ScalarPenalty ProductIntegerSignature BalancedFamily BalancedEnumeration

lemma factor_le_one (A : ℝ) (p : ℕ → ℝ) (hA : 0 ≤ A) (n : ℕ) (hp : 0 ≤ p n) :
    factor A p n ≤ 1 := by
  unfold factor
  calc
    (2:ℝ)^(-A*p n) ≤ (2:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) hp)
    _ = 1 := by norm_num

variable {C G : Type*} [Fintype C] [Fintype G]

/-- Every actual line/unary soft factor lies in (0,1], even before
the exact nonroot equations are imposed. -/
theorem softenedWeight_le_one (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g,0 ≤ rate g) (hu : ∀ i,0 ≤ urate i) (hL : 0 ≤ L) (z : C → ℕ) :
    softenedWeight line root rate offset slope urate ell uslope cap L z ≤ 1 := by
  have hl (g : G) : lineFactor root rate offset slope L g (lineTotal line z g) ≤ 1 := by
    apply factor_le_one
    · split_ifs
      · exact hrate g
      · exact hL
    · exact abs_nonneg _
  have hun (i : C) : unaryFactor urate ell uslope cap i (z i) ≤ 1 :=
    factor_le_one _ _ (hu i) _ (le_max_left _ _)
  have hprodL : (∏ g,lineFactor root rate offset slope L g (lineTotal line z g)) ≤ 1 := by
    calc
      _ ≤ ∏ _g : G,(1:ℝ) := Finset.prod_le_prod (fun _ _ => (factor_positive _ _ _).le) (fun g _ => hl g)
      _ = _ := by simp
  have hprodU : (∏ i,unaryFactor urate ell uslope cap i (z i)) ≤ 1 := by
    calc
      _ ≤ ∏ _i : C,(1:ℝ) := Finset.prod_le_prod (fun _ _ => (factor_positive _ _ _).le) (fun i _ => hun i)
      _ = _ := by simp
  have hnonneg : 0 ≤ ∏ i,unaryFactor urate ell uslope cap i (z i) :=
    Finset.prod_nonneg (fun _ _ => (factor_positive _ _ _).le)
  unfold softenedWeight productWeight
  exact (mul_le_mul_of_nonneg_right hprodL hnonneg).trans
    (by simpa only [one_mul] using hprodU)


end ContingencyTables.EqualitySoftening

namespace ContingencyTables.BalancedEnumeration

open scoped BigOperators Classical
open BalancedFamily

/-- The positive softened marginal is bounded by its finite number of
physical balanced assignments, uniformly in the softening parameter. -/
theorem eliminate_le_card {S : Type*} (Ms : List ℕ)
    (F : (Coordinates S Ms → ℕ) → ℝ) (hF : ∀ z,F z ≤ 1) (z : S → ℕ) :
    eliminate Ms F z ≤ (Fintype.card (Assignments Ms):ℝ) := by
  rw [eliminate_eq_sum]
  calc
    _ ≤ ∑ _a : Assignments Ms,(1:ℝ) := Finset.sum_le_sum (fun a _ => hF (embedding Ms z a))
    _ = _ := by simp

end ContingencyTables.BalancedEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mass and interpolation bounds for the physical tree marginal

The finite positive softening has at most the actual expanded physical
box's number of summands. Consequently its interpolation estimate passes
to the exact equality-constrained marginal even when that marginal has
zero entries outside its feasible interval.
-/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical
open ScalarPenalty ProductIntegerSignature

variable {C G : Type*} [Fintype C] [Fintype G]

/-- Softening only adds mass to an exact equality indicator. This
comparison holds for every parameter value, because all soft factors
are positive and the equality case has factor one. -/
theorem exactWeight_le_softenedWeight (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ) (z : C → ℕ) :
    exactWeight line root rate offset slope urate ell uslope cap z ≤
      softenedWeight line root rate offset slope urate ell uslope cap L z := by
  have hl (g : G) : exactLineFactor root rate offset slope g (lineTotal line z g) ≤
      lineFactor root rate offset slope L g (lineTotal line z g) := by
    unfold exactLineFactor lineFactor
    split_ifs
    · exact le_rfl
    · simp_all only [factor,mul_zero,Real.rpow_zero,le_refl]
    · exact (factor_positive _ _ _).le
  have hnonneg (g : G) : 0 ≤ exactLineFactor root rate offset slope g (lineTotal line z g) := by
    unfold exactLineFactor
    split_ifs
    · exact (factor_positive _ _ _).le
    · norm_num
    · exact le_rfl
  unfold exactWeight softenedWeight productWeight
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod (fun g _ => hnonneg g) (fun g _ => hl g))
    (Finset.prod_nonneg (fun _ _ => (factor_positive _ _ _).le))

end ContingencyTables.EqualitySoftening

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical Topology
open Filter CompanionFactorialApplication ForestPenaltyApplication
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening RowColumnPenalties
open IntegerWeightedTransport

variable {I J : Type*} [Fintype I] [Fintype J]

lemma other_card_le_full (A : Instance I J) (t : I×J) :
    Fintype.card (BalancedEnumeration.Assignments (widths (otherWidths A t))) ≤
      Fintype.card (ForestBoxCardinality.Assignments A) := by
  have hc : 1 ≤ ∏ a : {a : I×J // ¬keep t a=false},(cellWidth A a.val+1) := by
    exact Finset.one_le_prod' (fun _ _ => by omega)
  have hs := Fintype.prod_subtype_mul_prod_subtype (fun a : I×J => keep t a=false)
    (fun a => cellWidth A a+1)
  calc
    _ = Fintype.card ((k : Fin (Fintype.card (LargeCell (keep t)))) →
        Fin (otherWidths A t k+1)) := Fintype.card_congr (assignmentEquiv (otherWidths A t))
    _ = ∏ k,(otherWidths A t k+1) := by simp only [Fintype.card_pi,Fintype.card_fin]
    _ = ∏ a : LargeCell (keep t),(cellWidth A a.val+1) := by
      apply Fintype.prod_equiv (enumeration t)
      intro k
      rfl
    _ ≤ ∏ a : I×J,(cellWidth A a+1) := by
      rw [← hs]
      exact le_mul_of_one_le_right (Nat.zero_le _) hc
    _ = _ := by simp only [ForestBoxCardinality.Assignments,Fintype.card_pi,
        Fintype.card_fin,cellWidth]

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_WeightedCellFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact weighted summation over one physical cell's fibres -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem weighted_fibre_sum (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (g : Fin (M t+1) → ℝ) :
    (∑ k : Fin (M t+1),fibre M F t k*g k)=
      ∑ a : Profiles M,F (profile M a)*g (a t) := by
  unfold fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end ContingencyTables.BalancedCellFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalRegions
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal infeasible physical profiles lie in the terminal far or near regions -/

namespace ContingencyTables.CompanionTerminalRegions

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables
open CompanionNearMass ForestPenaltyApplication TreeMarginalSignature BalancedCellFibres
open EqualitySoftening

variable {I J : Type*} [Fintype I] [Fintype J]

lemma physicalRow_eq_table (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J) :
    physicalRow (ForestLiteralCount.lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) i j=(physicalTable A a i j:ℝ) := by
  simp only [physicalRow,BalancedCellFibres.profile,Bool.false_eq_true,ite_false,physicalTable,
    Int.cast_add,Int.cast_natCast]

lemma physicalColumn_eq_table (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J) :
    physicalColumn (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) i j=(physicalTable A a i j:ℝ) := by
  have hk : (a (i,j)).val ≤ cellWidth A (i,j) := Nat.le_of_lt_succ (a (i,j)).isLt
  simp only [physicalColumn,BalancedCellFibres.profile,ite_true, if_true,Nat.cast_sub hk]
  change (ForestLiteralCount.lower A.T A.d A.b i j:ℝ)+(cellWidth A (i,j):ℝ)-
    ((cellWidth A (i,j):ℝ)-((a (i,j)).val:ℝ))=(physicalTable A a i j:ℝ)
  simp only [physicalTable,Int.cast_add,Int.cast_natCast]
  ring

lemma deviation_eq_integer (A : Instance I J) (a : Profiles (cellWidth A)) (v : I⊕J) :
    deviation (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
      A.r A.c (BalancedCellFibres.profile (cellWidth A) a) v=(integerDeviation A a v:ℝ) := by
  cases v with
  | inl i =>
    simp only [deviation,integerDeviation,Sum.elim_inl]
    simp_rw [physicalRow_eq_table]
    push_cast
    rfl
  | inr j =>
    simp only [deviation,integerDeviation,Sum.elim_inr]
    simp_rw [physicalColumn_eq_table]
    push_cast
    rfl

lemma nonTree_bounded (A : Instance I J) (a : Profiles (cellWidth A)) (i : I) (j : J)
    (ht : ¬A.T.Adj (.inl i) (.inr j)) :
    0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j := by
  have hk : (a (i,j)).val ≤ cellWidth A (i,j) := Nat.le_of_lt_succ (a (i,j)).isLt
  simp only [cellWidth,ForestLiteralCount.width,ht,ite_false] at hk
  simp only [physicalTable,ForestLiteralCount.lower,ht,ite_false,zero_add]
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast hk⟩

lemma treePenalty_nonnegative (A : Instance I J) (a : Profiles (cellWidth A)) :
    0 ≤ treePenalty A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (BalancedCellFibres.profile (cellWidth A) a) := by
  unfold treePenalty
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
  · exact le_rfl

end ContingencyTables.CompanionTerminalRegions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TerminalMassCover
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite mass accounting for the terminal far and near regions -/

namespace ContingencyTables.TerminalMassCover

open scoped BigOperators Classical

variable {X C : Type*} [Fintype X] [Fintype C]

/-- A finite union estimate retaining the feasible unit summands exactly.
The application proves the cover from the original root and tree penalties. -/
theorem mass_le_cover (w : X → ℝ) (feasible far : X → Prop) (near : C → X → Prop)
    (hw : ∀ x,0 ≤ w x) (hunit : ∀ x,feasible x → w x=1)
    (hcover : ∀ x,0 < w x → ¬feasible x → far x ∨ ∃ c,near c x) :
    (∑ x,w x) ≤ (∑ x,if feasible x then (1:ℝ) else 0)+
      (∑ x,if far x then w x else 0)+∑ c,∑ x,if near c x then w x else 0 := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hn : 0 ≤ ∑ c,if near c x then w x else 0 := by
    apply Finset.sum_nonneg
    intro c _
    split_ifs <;> first | exact hw x | exact le_rfl
  have hf : 0 ≤ if far x then w x else 0 := by
    split_ifs <;> first | exact hw x | exact le_rfl
  by_cases hx : feasible x
  · simp only [hx,ite_true, if_true]
    calc
      w x = 1 := hunit x hx
      _ ≤ 1+(if far x then w x else 0)+(∑ c,if near c x then w x else 0) := by linarith
  · simp only [hx,ite_false,zero_add]
    by_cases hp : 0 < w x
    · rcases hcover x hp hx with hf'|⟨c,hc⟩
      · rw [ite_eq_left hf']
        linarith
      · have hs := Finset.single_le_sum
          (f := fun c => if near c x then w x else 0)
          (fun c _ => by split_ifs <;> first | exact hw x | exact le_rfl)
          (Finset.mem_univ c)
        simp only [hc,ite_true, if_true] at hs
        linarith
    · have hz : w x=0 := le_antisymm (le_of_not_gt hp) (hw x)
      simp only [hz,ite_self,Finset.sum_const_zero,zero_add,le_refl]

/-- The manuscript's final conversion from a small fraction of the
normalizer to a relative error against the exact table count. -/
theorem relative_count_bound (Z M epsilon : ℝ) (hZ : 0 ≤ Z)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hZM : Z ≤ M)
    (hbad : M ≤ Z+(epsilon/64)*M) :
    Z ≤ M ∧ M ≤ (1+epsilon/32)*Z := by
  refine ⟨hZM,?_⟩
  have hM : 0 ≤ M := hZ.trans hZM
  have hscaled : (1-epsilon/64)*M ≤ Z := by linarith
  have hfactor : 0 ≤ 1+epsilon/32 := by positivity
  have hh := mul_le_mul_of_nonneg_left hscaled hfactor
  have hcoef : 1 ≤ (1+epsilon/32)*(1-epsilon/64) := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1.le)]
  have hmono := mul_le_mul_of_nonneg_right hcoef hM
  nlinarith

end ContingencyTables.TerminalMassCover

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual terminal companion normalizer approximates the table count -/

namespace ContingencyTables.CompanionTerminalMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables CompanionPhysicalNormalizer
open CompanionNearMass CompanionTerminalRegions BalancedCellFibres TreeMarginalSignature

variable {I J : Type*} [Fintype I] [Fintype J]

lemma tableCount_ge_one (A : Instance I J) : 1 ≤ tableCount A := by
  have ha : Feasible A (tableAssignment A A.X A.hX) := by
    unfold Feasible
    rw [physicalTable_assignment]
    exact ⟨A.hX,A.hXr,A.hXc⟩
  have hpos : 0 < Fintype.card (PhysicalTables A) :=
    Fintype.card_pos_iff.mpr ⟨⟨tableAssignment A A.X A.hX,ha⟩⟩
  have hh : 1 ≤ Fintype.card (PhysicalTables A) := hpos
  rw [cardinality_eq] at hh
  unfold tableCount
  exact_mod_cast hh

lemma treeCell_card_le (A : Instance I J) : Fintype.card (TreeCell A) ≤ A.d := by
  exact (Fintype.card_le_of_injective (fun t : TreeCell A => t.val) Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

lemma feasible_sum_eq_tableCount (A : Instance I J) :
    (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=tableCount A := by
  have hh : (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=
      (Fintype.card (PhysicalTables A):ℝ) := by simp [PhysicalTables,Fintype.card_subtype]
  rw [hh,cardinality_eq]
  rfl

end ContingencyTables.CompanionTerminalMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalParameters
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion's literal terminal parameter choices -/

namespace ContingencyTables.CompanionTerminalParameters

lemma allowance_bits (L d : ℕ) (epsilon : ℝ) : 2*L ≤ allowance L d epsilon := by
  unfold allowance
  omega

lemma gamma_le_one (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d)
    (he1 : epsilon < 1) : gamma L d epsilon ≤ 1 := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1:ℝ) ≤ allowance L d epsilon := by
    exact_mod_cast (show 1 ≤ allowance L d epsilon from allowance_positive L d epsilon)
  unfold gamma
  apply (div_le_one (by positivity)).mpr
  nlinarith [mul_le_mul hdR hKR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ d)]

lemma near_fraction (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) :
    4*(d:ℝ)*gamma L d epsilon*allowance L d epsilon=epsilon/128 := by
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hK0 : (allowance L d epsilon:ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (allowance_positive L d epsilon))
  unfold gamma
  field_simp [hd0,hK0]
  ring

lemma terminal_scale (L d : ℕ) (epsilon : ℝ) (hd : 1 ≤ d) (he : 0 < epsilon) :
    4*(allowance L d epsilon:ℝ) ≤ (coefficient L d epsilon:ℝ)*gamma L d epsilon := by
  have hg := gamma_positive L d epsilon hd he
  have hh := mul_le_mul_of_nonneg_right
    (Nat.le_ceil (4*(allowance L d epsilon:ℝ)/gamma L d epsilon)) hg.le
  rw [div_mul_cancel₀ _ hg.ne'] at hh
  exact hh

lemma reciprocal_precision (epsilon : ℝ) (he : 0 < epsilon) :
    (2:ℝ)^(-(precision epsilon:ℝ)) ≤ epsilon := by
  have hq : 1/epsilon ≤ (2:ℝ)^(precision epsilon:ℝ) := by
    calc
      _ = (2:ℝ)^Real.logb 2 (1/epsilon) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),← one_div]
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1/epsilon) hq
  simpa using hh

lemma far_fraction (L d : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    (2:ℝ)^(-(3*allowance L d epsilon:ℕ):ℝ) ≤ epsilon/128 := by
  have hindex : precision epsilon+7 ≤ 3*allowance L d epsilon := by
    unfold allowance
    omega
  calc
    _ ≤ (2:ℝ)^(-((precision epsilon:ℝ)+7)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast (show
        -((3*allowance L d epsilon:ℕ):ℤ) ≤ -((precision epsilon+7:ℕ):ℤ) by omega))
    _ = (2:ℝ)^(-(precision epsilon:ℝ))/128 := by
      rw [neg_add,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num; ring
    _ ≤ _ := div_le_div_of_nonneg_right (reciprocal_precision epsilon he) (by norm_num)

end ContingencyTables.CompanionTerminalParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTerminalApplication
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal finite phase estimator has the required counting accuracy -/

namespace ContingencyTables.CompanionTerminalApplication

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionTerminalMass CompanionTerminalParameters
open CompanionReferenceAccuracy CompanionAnnealing

variable {I J : Type*} [Fintype I] [Fintype J]

lemma final_parameter (A : Instance I J) (L : ℕ) (epsilon : ℝ) :
    (finalPhase A L epsilon:ℝ)/scale A=(coefficient L A.d epsilon:ℝ) := by
  have hs := (scale_positive A).ne'
  have hh : (finalPhase A L epsilon:ℝ)=(coefficient L A.d epsilon:ℝ)*scale A := by
    unfold finalPhase scale
    push_cast
    ring
  rw [hh,mul_div_cancel_right₀ _ hs]

end ContingencyTables.CompanionTerminalApplication

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical factors with the executed component-root convention

The line factors use the explicitly selected roots. Their tree factors,
widths and doubled row/column coordinates are exactly the source data.
-/

namespace ContingencyTables.RootedPenalty

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication RootedCompletion
open ForestPenaltyApplication ForestLiteralCount EqualitySoftening
open ProductIntegerSignature RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

theorem physicalWeight_nonnegative (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (z : ((I×J)×Bool) → ℕ) : 0≤ physicalWeight A S alpha z := by
  rw [exact_eq]
  split_ifs
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
  · exact le_rfl

end ContingencyTables.RootedPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_zero (A : Instance I J) (S : Selection A.T) (z : View A → ℕ) :
    h A S 0 z=∏ a : FreeCell A.small A.T,((A.b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [h,Fintype.card_pi,Nat.cast_prod]

end ContingencyTables.RootedCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmStart
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.RootedWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open CompanionInitialization (freeTotal)
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The initial factorial weight is independent of the selected root. -/
lemma zero_weight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    weight A R 0=CompanionAnnealing.weight A 0 := by
  funext S
  unfold weight CompanionAnnealing.weight
  simp only [Nat.cast_zero,zero_div]
  unfold RootedFactorialApplication.f CompanionFactorialApplication.f firstLift
  rw [RootedCountIdentification.h_zero,CompanionInitialization.h_zero]
  rfl

lemma total_zero (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    slotTotal pairs (weight A R 0) ∅=
      freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
  rw [zero_weight_eq]
  simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
    CompanionInitialization.total_zero A

lemma total_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) : 0< total A R j :=
  slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh

end ContingencyTables.RootedWarmStart

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalNormalizer
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root factorial normalizer is the literal physical mass -/

namespace ContingencyTables.RootedPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates RootedFactorialApplication
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open CompanionPhysicalNormalizer (smallProfilesEquiv small_display_eq)

private lemma finite_sum_congr {C : Type*} (F G : Fintype C) (f g : C → ℝ)
    (h : ∀ c,f c=g c) :
    @Finset.sum C ℝ _ (@Finset.univ C F) f=@Finset.sum C ℝ _ (@Finset.univ C G) g := by
  have he : F=G := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun c _ => h c)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma h_eq_physical_sum (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (alpha : ℝ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z) :
    RootedCountIdentification.h A R alpha z=
      ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        RootedPenalty.physicalWeight A R alpha
          (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A) z a) := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  rw [RootedCountIdentification.h_eq_largeMarginal A R alpha e z hz]
  unfold RootedLargeMarginal.largeMarginal
  convert sum_joined_eq_physical (fun a : I×J => A.small a.1 a.2) (cellWidth A) e z
    (RootedPenalty.physicalWeight A R alpha) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    apply finite_sum_congr
    intro a
    rfl

lemma physicalMass_eq_split (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    physicalMass A R alpha=
      ∑ s : SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
          RootedPenalty.physicalWeight A R alpha
            (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A)
              (smallDisplay (fun a : I×J => A.small a.1 a.2) (cellWidth A) s) a) := by
  let F := RootedPenalty.physicalWeight A R alpha
  let small : I×J → Bool := fun a => A.small a.1 a.2
  change (∑ a : Profiles (cellWidth A),F (BalancedCellFibres.profile (cellWidth A) a))=
    ∑ s : SmallProfiles small (cellWidth A),∑ a : PhysicalAssignments small (cellWidth A),
      F (physicalProfile small (cellWidth A) (smallDisplay small (cellWidth A) s) a)
  have he := Fintype.sum_equiv (partition small (cellWidth A))
    (fun a => F (BalancedCellFibres.profile (cellWidth A) a))
    (fun a => F (physicalProfile small (cellWidth A) (smallDisplay small (cellWidth A) a.1) a.2))
    (by
      intro a
      have hh := partition_profile small (cellWidth A) ((partition small (cellWidth A)) a)
      simpa only [Equiv.symm_apply_apply] using congrArg F hh)
  rw [he,Fintype.sum_prod_type]

lemma total_eq_raw_profiles (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅=
      ∑ x : TransversalCount.Profile (fun s : SmallCell A => A.b s.val.1 s.val.2),
        RootedCountIdentification.h A R alpha
          (TransversalCount.display (fun s : SmallCell A => A.b s.val.1 s.val.2) x) := by
  unfold RootedFactorialApplication.f
  rw [CompanionInitialization.denominator_eq]
  convert TransversalCount.slotTotal_eq_profiles
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (RootedCountIdentification.h A R alpha) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  all_goals
    congr 1
    ext
    simp

/-- Factorial cancellation and the actual physical partition identify
this selected-root normalizer with the mass used in terminal estimates. -/
theorem normalizer_eq_physical_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅=physicalMass A R alpha := by
  rw [total_eq_raw_profiles,physicalMass_eq_split]
  symm
  apply Fintype.sum_equiv (smallProfilesEquiv A)
  intro s
  rw [small_display_eq]
  symm
  apply h_eq_physical_sum
  intro u
  rcases u with ⟨a,b⟩
  cases b
  · exact Nat.le_of_lt_succ ((smallProfilesEquiv A s) a).isLt
  · exact Nat.sub_le _ _

end ContingencyTables.RootedPhysicalNormalizer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedFarMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential far-penalty bound for the actual selected-root mass -/

namespace ContingencyTables.RootedFarMass

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres

variable {I J : Type*} [Fintype I] [Fintype J]

lemma weight_at_large_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (K : ℕ)
    (a : Profiles (cellWidth A)) (ha : 4*(K:ℝ) ≤ alpha*actualPenalty A R a) :
    actualWeight A R alpha a ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := by
  unfold actualWeight
  rw [RootedPenalty.exact_eq]
  split_ifs
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    change -alpha*actualPenalty A R a ≤ -((4*K:ℕ):ℝ)
    push_cast
    linarith
  · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).le

/-- The true expanded physical box has at most 2^K summands, so the
entire terminal region whose penalty is at least 4K contributes at most
2^(-3K). Neither a table-count approximation nor an oracle is assumed. -/
theorem far_mass_le (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (B K : ℕ)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) :
    (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
      then actualWeight A R alpha a else 0) ≤ (2:ℝ)^(-(3*K:ℕ):ℝ) := by
  have hcard : Fintype.card (Profiles (cellWidth A)) ≤ 2^K :=
    ForestBoxCardinality.cardinality_le_two_pow A hW B K hB hBK
  have hcardR : (Fintype.card (Profiles (cellWidth A)):ℝ) ≤ (2:ℝ)^K := by exact_mod_cast hcard
  have hp : 0 ≤ (2:ℝ)^(-(4*K:ℕ):ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ∑ _a : Profiles (cellWidth A),(2:ℝ)^(-(4*K:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · exact weight_at_large_penalty A R alpha K a ha
      · exact hp
    _ = (Fintype.card (Profiles (cellWidth A)):ℝ)*(2:ℝ)^(-(4*K:ℕ):ℝ) := by simp
    _ ≤ (2:ℝ)^K*(2:ℝ)^(-(4*K:ℕ):ℝ) := mul_le_mul_of_nonneg_right hcardR hp
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      push_cast
      ring

end ContingencyTables.RootedFarMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyApplication
open TreeMarginalSignature (keep singleView enumeration cellWidth otherWidths coordinateEquiv)
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening IntegerWeightedTransport RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

theorem soft_slices (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) :
    PositiveSlice (soft A R alpha L t) (fun _ => cellWidth A t) (cellWidth A t) ∧
      RemovalSlice (soft A R alpha L t) (fun _ => cellWidth A t) (cellWidth A t) := by
  apply EqualityReindex.physical_softened_slices_all
    (widths (otherWidths A t)) (fun _ => cellWidth A t) (cellWidth A t) (coordinateEquiv A t)
  · exact fun _ => ha
  · intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  · exact hL

theorem scalar_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ cellWidth A t) :
    0 < scalarSoft A R alpha L t k :=
  (soft_slices A R alpha L t ha hL).1 _
    (childProfile_inBox _ _ hk) (childProfile_total _ _ hk)

theorem scalar_logConcave (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k+2 ≤ cellWidth A t) :
    scalarSoft A R alpha L t k*scalarSoft A R alpha L t (k+2) ≤
      (scalarSoft A R alpha L t (k+1))^2 :=
  child_logConcave (soft A R alpha L t) _ (soft_slices A R alpha L t ha hL).1
    (soft_slices A R alpha L t ha hL).2 k hk

/-- Every retained tree mass is the finite equality-softening limit of
its actual positive physical balanced sum. -/
theorem scalar_tendsto (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (k : ℕ) :
    Tendsto (fun L : ℝ => scalarSoft A R alpha L t k) atTop (nhds (scalarExact A R alpha t k)) := by
  apply eliminate_tendsto (widths (otherWidths A t))
  intro z
  exact softenedWeight_tendsto cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
    (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
    viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
    unarySlope (unaryCap A.b) (z ∘ (coordinateEquiv A t).symm)

/-- The selected-root retained-cell marginal is the actual physical fibre. -/
theorem exact_eq_fibre (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (alpha : ℝ) (t : I×J) (k : Fin (cellWidth A t+1)) :
    scalarExact A R alpha t k.val=
      BalancedCellFibres.fibre (cellWidth A) (RootedPenalty.physicalWeight A R alpha) t k := by
  unfold scalarExact exactMarginal
  rw [TreeMarginalSignature.eliminate_eq_one_cell_sum,BalancedCellFibres.fibre_eq_sum]
  apply Fintype.sum_equiv
    (Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
      (TreeMarginalSignature.otherCells t))
  intro a
  congr 1
  have h := TreeMarginalSignature.physical_one_cell_profile A t k
    ((Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
      (TreeMarginalSignature.otherCells t)) a)
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.RootedTreeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root physical tree interpolation after the equality limit -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical Topology
open Filter CompanionFactorialApplication ForestPenaltyApplication
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening RowColumnPenalties
open IntegerWeightedTransport
open TreeMarginalSignature (cellWidth otherWidths coordinateEquiv other_card_le_full)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scalar_soft_le_two_pow (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hK : 2*B ≤ K) (k : ℕ) :
    scalarSoft A R alpha L t k ≤ (2:ℝ)^K := by
  have hcard := (other_card_le_full A t).trans
    (ForestBoxCardinality.cardinality_le_two_pow A hW B K hB hK)
  have hu := BalancedEnumeration.eliminate_le_card (widths (otherWidths A t))
    (fun z => softenedWeight cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
      (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
      viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
      unarySlope (unaryCap A.b) L (z ∘ (coordinateEquiv A t).symm))
    (by
      intro z
      apply softenedWeight_le_one
      · exact fun _ => ha
      · intro a
        unfold unaryRate
        split_ifs
        · exact div_nonneg ha (Nat.cast_nonneg _)
        · exact le_rfl
      · exact hL)
    (childProfile (cellWidth A t) k)
  exact hu.trans (by exact_mod_cast hcard)

theorem scalar_exact_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (k : ℕ) (hk : k ≤ cellWidth A t) :
    0 ≤ scalarExact A R alpha t k := by
  apply ge_of_tendsto (scalar_tendsto A R alpha t k)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  exact (scalar_positive A R alpha L t ha hL k hk).le

lemma scalar_exact_le_soft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) (k : ℕ) :
    scalarExact A R alpha t k ≤ scalarSoft A R alpha L t k := by
  unfold scalarExact exactMarginal scalarSoft soft
  simp only [BalancedEnumeration.eliminate_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  exact exactWeight_le_softenedWeight _ _ _ _ _ _ _ _ _ _ _

/-- A feasible table attaining the endpoint cell value supplies the
lower bound for finite interpolation through the equality limit. -/
theorem scalar_exact_half_window (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 1 ≤ K) (hN : 0 < N) (hkN : k+N ≤ cellWidth A t)
    (hend : 1 ≤ scalarExact A R alpha t (k+N))
    (r : ℕ) (hr : r*K ≤ N) :
    scalarExact A R alpha t k/2 ≤ scalarExact A R alpha t (k+r) := by
  apply le_of_tendsto_of_tendsto ((scalar_tendsto A R alpha t k).div_const 2)
    (scalar_tendsto A R alpha t (k+r))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  apply positive_sequence_half_window (fun q => scalarSoft A R alpha L t (k+q)) N K hK hN
  · intro q hq
    exact scalar_positive A R alpha L t ha hL _ (by omega)
  · intro q hq
    have hh := scalar_logConcave A R alpha L t ha hL (k+q) (by omega)
    simpa only [Nat.add_assoc] using hh
  · exact hend.trans (scalar_exact_le_soft A R alpha L t (k+N))
  · simpa only [Nat.add_zero] using scalar_soft_le_two_pow A R alpha L t ha hL hW B K hB hBK k
  · exact hr

/-- The same physical half-height estimate when the feasible endpoint
lies to the left of an exterior tree position. -/
theorem scalar_exact_backward_half_window (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 1 ≤ K) (hN : 0 < N) (hNk : N ≤ k) (hk : k ≤ cellWidth A t)
    (hend : 1 ≤ scalarExact A R alpha t (k-N)) (r : ℕ) (hr : r*K ≤ N) :
    scalarExact A R alpha t k/2 ≤ scalarExact A R alpha t (k-r) := by
  apply le_of_tendsto_of_tendsto ((scalar_tendsto A R alpha t k).div_const 2)
    (scalar_tendsto A R alpha t (k-r))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  apply positive_sequence_half_window (fun q => scalarSoft A R alpha L t (k-q)) N K hK hN
  · intro q _
    exact scalar_positive A R alpha L t ha hL _ ((Nat.sub_le _ _).trans hk)
  · intro q hq
    have hqk : q+2 ≤ k := hq.trans hNk
    have hh := scalar_logConcave A R alpha L t ha hL (k-(q+2)) (by omega)
    rw [show k-(q+2)+2=k-q by omega,show k-(q+2)+1=k-(q+1) by omega] at hh
    simpa only [mul_comm] using hh
  · exact hend.trans (scalar_exact_le_soft A R alpha L t (k-N))
  · simpa only [Nat.sub_zero] using scalar_soft_le_two_pow A R alpha L t ha hL hW B K hB hBK k
  · exact hr

/-- The actual physical exterior point has normalized mass at most
2K/b whenever a feasible unit-mass endpoint lies at least b places to
its right, after eliminating all soft parameters. -/
theorem scalar_exact_forward_point_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N b : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 0 < K) (hN : 0 < N) (hb : 0 < b) (hbN : b ≤ N)
    (hkN : k+N ≤ cellWidth A t) (hend : 1 ≤ scalarExact A R alpha t (k+N)) :
    scalarExact A R alpha t k/(∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q) ≤
      (2*K:ℝ)/b := by
  have hnonneg : ∀ q,q ≤ cellWidth A t → 0 ≤ scalarExact A R alpha t q :=
    scalar_exact_nonnegative A R alpha t ha
  have hmass := Finset.single_le_sum
    (fun q hq => hnonneg q (by have := Finset.mem_range.mp hq; omega))
    (Finset.mem_range.mpr (show k+N < cellWidth A t+1 by omega))
  have hC : 0 < ∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q := by
    linarith
  apply half_window_mass_bound (scalarExact A R alpha t) (cellWidth A t) k N K b hK hb hbN hkN
    hnonneg hC
  intro r hr
  exact scalar_exact_half_window A R alpha t ha hW B K k N hB hBK hK hN hkN hend r hr

theorem scalar_exact_backward_point_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N b : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 0 < K) (hN : 0 < N) (hb : 0 < b) (hbN : b ≤ N)
    (hNk : N ≤ k) (hk : k ≤ cellWidth A t) (hend : 1 ≤ scalarExact A R alpha t (k-N)) :
    scalarExact A R alpha t k/(∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q) ≤
      (2*K:ℝ)/b := by
  let U := cellWidth A t
  let a : ℕ → ℝ := fun q => scalarExact A R alpha t (U-q)
  have hsum : (∑ q ∈ Finset.range (U+1),a q)=
      ∑ q ∈ Finset.range (U+1),scalarExact A R alpha t q := by
    simpa only [a,Nat.add_sub_cancel] using Finset.sum_range_reflect (scalarExact A R alpha t) (U+1)
  have hnonneg : ∀ q,q ≤ U → 0 ≤ a q := by
    intro q _
    exact scalar_exact_nonnegative A R alpha t ha _ (Nat.sub_le _ _)
  have hend' : 1 ≤ a (U-k+N) := by
    change 1 ≤ scalarExact A R alpha t (U-(U-k+N))
    rw [show U-(U-k+N)=k-N by dsimp only [U] at *; omega]
    exact hend
  have hmass := Finset.single_le_sum
    (fun q hq => hnonneg q (by have := Finset.mem_range.mp hq; omega))
    (Finset.mem_range.mpr (show U-k+N < U+1 by dsimp only [U] at *; omega))
  have hC : 0 < ∑ q ∈ Finset.range (U+1),a q := by linarith
  have hp := half_window_mass_bound a U (U-k) N K b hK hb hbN
    (by dsimp only [U] at *; omega) hnonneg hC (by
      intro r hr
      have hrN : r ≤ N := by nlinarith
      change scalarExact A R alpha t (U-(U-k))/2 ≤ scalarExact A R alpha t (U-(U-k+r))
      rw [show U-(U-k)=k by dsimp only [U] at *; omega,
        show U-(U-k+r)=k-r by dsimp only [U] at *; omega]
      exact scalar_exact_backward_half_window A R alpha t ha hW B K k N hB hBK hK hN hNk hk hend r hr)
  change scalarExact A R alpha t (U-(U-k))/(∑ q ∈ Finset.range (U+1),a q) ≤ (2*K:ℝ)/b at hp
  rw [show U-(U-k)=k by dsimp only [U] at *; omega,hsum] at hp
  exact hp

end ContingencyTables.RootedTreeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeFeasibleMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual feasible tables contribute unit selected-root fibre mass -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication ForestLiteralCount
open BalancedCellFibres EqualitySoftening
open TreeMarginalSignature (cellWidth tableAssignment tableAssignment_row tableAssignment_column
  tableAssignment_tree_index)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem tableAssignment_unit (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (Y : I → J → ℤ)
    (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i, (∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) :
    RootedPenalty.physicalWeight A R alpha
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY))=1 := by
  have hdev : ∀ g,deviation (lower A.T A.d A.b) (width A.T A.d A.b) A.r A.c
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) g=0 := by
    intro g
    cases g with
    | inl i =>
      simp only [deviation,Sum.elim_inl]
      simp_rw [tableAssignment_row]
      have hh : (∑ j,(Y i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast hr i
      rw [hh,sub_self]
    | inr j =>
      simp only [deviation,Sum.elim_inr]
      simp_rw [tableAssignment_column]
      have hh : (∑ i,(Y i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast hc j
      rw [hh,sub_self]
  have hlines : ∀ g,RootedPenalty.rootFlag R g=false →
      deviation (RootedPenalty.ell A) (RootedPenalty.widths A) A.r A.c
        (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) g=0 :=
    fun g _ => hdev g
  rw [RootedPenalty.exact_eq,ite_eq_left hlines]
  have hp : RootedPenalty.penalty A R
      (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY))=0 := by
    unfold RootedPenalty.penalty RootedPenalty.rootPenalty RootedPenalty.ell RootedPenalty.widths treePenalty
    simp only [hdev,abs_zero,ite_self,Finset.sum_const_zero,zero_add]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hy0 : (0:ℝ) ≤ Y i j := by exact_mod_cast (hY i j).1
    have hyb : (Y i j:ℝ) ≤ A.b i j := by exact_mod_cast (hY i j).2
    have hh := tableAssignment_row A Y hY i j
    unfold affineDistance
    simp only [mul_one]
    change (if A.T.Adj (.inl i) (.inr j) then
      max 0 (max (-(physicalRow (lower A.T A.d A.b)
        (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j))
        (physicalRow (lower A.T A.d A.b)
          (BalancedCellFibres.profile (cellWidth A) (tableAssignment A Y hY)) i j-A.b i j)) /
        (A.b i j:ℝ) else 0)=0
    rw [hh,max_eq_left (max_le (neg_nonpos.mpr hy0) (sub_nonpos.mpr hyb))]
    simp
  rw [hp,mul_zero,Real.rpow_zero]

/-- A feasible table supplies an actual unit summand at its retained
physical coordinate. No endpoint-mass oracle is assumed. -/
theorem scalar_exact_ge_one_at_table (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j) (t : I×J) :
    1 ≤ scalarExact A R alpha t (tableAssignment A Y hY t).val := by
  rw [exact_eq_fibre]
  have hh := Finset.single_le_sum
    (f := fun a : Profiles (cellWidth A) =>
      if a t=tableAssignment A Y hY t then
        RootedPenalty.physicalWeight A R alpha
          (BalancedCellFibres.profile (cellWidth A) a) else 0)
    (fun a _ => by split_ifs; exact RootedPenalty.physicalWeight_nonnegative A R alpha _; exact le_rfl)
    (Finset.mem_univ (tableAssignment A Y hY))
  simp only [ite_true, if_true,tableAssignment_unit A R alpha Y hY hr hc] at hh
  apply hh.trans_eq
  unfold fibre
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl

/-- Tight upper-cell attainment supplies the endpoint on the right of
every lower exterior tree value. -/
theorem upper_tree_endpoint (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=(A.b t.1 t.2:ℤ)) :
    1 ≤ scalarExact A R alpha t (10*A.d*A.b t.1 t.2+A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy] at hi
  push_cast at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2+A.b t.1 t.2 := by
    exact_mod_cast (show ((tableAssignment A Y hY t).val:ℤ)=
      ((10*A.d*A.b t.1 t.2+A.b t.1 t.2:ℕ):ℤ) by push_cast; omega)
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A R alpha Y hY hr hc t

/-- Tight lower-cell attainment supplies the endpoint on the left of
every upper exterior tree value. -/
theorem lower_tree_endpoint (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2))
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=0) :
    1 ≤ scalarExact A R alpha t (10*A.d*A.b t.1 t.2) := by
  have hi := tableAssignment_tree_index A Y hY t ht
  rw [hy,zero_add] at hi
  have hindex : (tableAssignment A Y hY t).val=10*A.d*A.b t.1 t.2 := by exact_mod_cast hi
  rw [← hindex]
  exact scalar_exact_ge_one_at_table A R alpha Y hY hr hc t

end ContingencyTables.RootedTreeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeExteriorMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root exterior fibres normalized by their actual physical mass -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedPhysicalNormalizer BalancedCellFibres
open ForestPenaltyApplication ForestLiteralCount
open TreeMarginalSignature (cellWidth)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma scalar_sum_eq_physicalMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) :
    (∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q)=physicalMass A R alpha := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [exact_eq_fibre]
  exact sum_fibre (cellWidth A)
    (RootedPenalty.physicalWeight A R alpha) t

/-- A lower exterior tree position is controlled by the actual feasible
table attaining its upper bound, exactly as in the manuscript. -/
theorem lower_exterior_point (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=(A.b t.1 t.2:ℤ)) (k : ℕ) (hk : k < 10*A.d*A.b t.1 t.2) :
    scalarExact A R alpha t k/physicalMass A R alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
  let N := 10*A.d*A.b t.1 t.2+A.b t.1 t.2-k
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hend := upper_tree_endpoint A R alpha t ht Y hY hr hc hy
  have hkN : k+N=10*A.d*A.b t.1 t.2+A.b t.1 t.2 := by dsimp only [N]; omega
  have hwidth : cellWidth A t=20*A.d*A.b t.1 t.2 := by simp only [cellWidth,width,ht,ite_true, if_true]
  have hprod : A.b t.1 t.2 ≤ A.d*A.b t.1 t.2 := by have hd := A.hd; nlinarith
  have hh := scalar_exact_forward_point_bound A R alpha t ha hW B K k N (A.b t.1 t.2) hB hBK hK
    (by dsimp only [N]; omega) hb (by dsimp only [N]; omega)
    (by rw [hkN,hwidth]; nlinarith) (by rw [hkN]; exact hend)
  rwa [scalar_sum_eq_physicalMass] at hh

theorem upper_exterior_point (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=0) (k : ℕ)
    (hk : 10*A.d*A.b t.1 t.2+A.b t.1 t.2 < k) (hkU : k ≤ cellWidth A t) :
    scalarExact A R alpha t k/physicalMass A R alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
  let N := k-10*A.d*A.b t.1 t.2
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hend := lower_tree_endpoint A R alpha t ht Y hY hr hc hy
  have hkN : k-N=10*A.d*A.b t.1 t.2 := by dsimp only [N]; omega
  have hh := scalar_exact_backward_point_bound A R alpha t ha hW B K k N (A.b t.1 t.2) hB hBK hK
    (by dsimp only [N]; omega) hb (by dsimp only [N]; omega) (by dsimp only [N]; omega)
    hkU (by rw [hkN]; exact hend)
  rwa [scalar_sum_eq_physicalMass] at hh

end ContingencyTables.RootedTreeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedNearMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root mass in the actual narrow exterior tree region -/

namespace ContingencyTables.RootedNearMass

open scoped BigOperators Classical
open CompanionFactorialApplication RootedPhysicalNormalizer RootedFarMass
open RootedTreeMarginal TreeExteriorPositions BalancedCellFibres
open TreeMarginalSignature (cellWidth)
open CompanionNearMass (cellPositions)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma nearMass_eq_fibres (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (gamma : ℝ) :
    nearMass A R alpha t gamma=∑ k ∈ cellPositions A t gamma,scalarExact A R alpha t k.val := by
  have hh := weighted_fibre_sum (cellWidth A)
    (RootedPenalty.physicalWeight A R alpha) t
    (fun k => if k ∈ cellPositions A t gamma then 1 else 0)
  have hs : (∑ k : Fin (cellWidth A t+1),
      if k ∈ cellPositions A t gamma then scalarExact A R alpha t k.val else 0)=nearMass A R alpha t gamma := by
    simp_rw [exact_eq_fibre]
    simpa only [nearMass,actualWeight,mul_ite,mul_one,mul_zero] using hh
  rw [← hs]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using
    (Finset.sum_filter (s := Finset.univ) (fun k => k ∈ cellPositions A t gamma)
      (fun k => scalarExact A R alpha t k.val)).symm

/-- This uses actual feasible endpoint tables, the proved raw marginal
signature and equality limit, and the exact count normalizer. -/
theorem near_mass_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha gamma : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha) (hg : 0 < gamma)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y0 Y1 : I → J → ℤ)
    (hY0 : ∀ i j,0 ≤ Y0 i j ∧ Y0 i j ≤ A.b i j)
    (hY1 : ∀ i j,0 ≤ Y1 i j ∧ Y1 i j ≤ A.b i j)
    (hr0 : ∀ i,(∑ j,Y0 i j)=A.r i) (hc0 : ∀ j,(∑ i,Y0 i j)=A.c j)
    (hr1 : ∀ i,(∑ j,Y1 i j)=A.r i) (hc1 : ∀ j,(∑ i,Y1 i j)=A.c j)
    (hy0 : Y0 t.1 t.2=0) (hy1 : Y1 t.1 t.2=(A.b t.1 t.2:ℤ)) :
    nearMass A R alpha t gamma/physicalMass A R alpha ≤ 4*gamma*K := by
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hbR : (0:ℝ) < A.b t.1 t.2 := by exact_mod_cast hb
  have hpoint (k : Fin (cellWidth A t+1)) (hk : k ∈ cellPositions A t gamma) :
      scalarExact A R alpha t k.val/physicalMass A R alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
    have hh := (Finset.mem_filter.mp hk).2
    change (((ForestLiteralCount.lower A.T A.d A.b t.1 t.2+(k.val:ℤ)<0) ∧ _) ∨
      (((A.b t.1 t.2:ℤ)<ForestLiteralCount.lower A.T A.d A.b t.1 t.2+(k.val:ℤ)) ∧ _)) at hh
    simp only [ForestLiteralCount.lower,ht,ite_true, if_true] at hh
    rcases hh with hh|hh
    · apply lower_exterior_point A R alpha t ht ha hW B K hB hBK hK Y1 hY1 hr1 hc1 hy1
      exact_mod_cast (show (k.val:ℤ) < (10*A.d*A.b t.1 t.2:ℕ) by omega)
    · apply upper_exterior_point A R alpha t ht ha hW B K hB hBK hK Y0 hY0 hr0 hc0 hy0
      · exact_mod_cast (show (10*A.d*A.b t.1 t.2+A.b t.1 t.2:ℕ) < (k.val:ℤ) by omega)
      · exact Nat.le_of_lt_succ k.isLt
  have hcard := card_positions_le (ForestLiteralCount.lower A.T A.d A.b t.1 t.2)
    (A.b t.1 t.2) (cellWidth A t) (gamma*A.b t.1 t.2) (mul_pos hg hbR)
  calc
    _ = ∑ k ∈ cellPositions A t gamma,scalarExact A R alpha t k.val/physicalMass A R alpha := by
      rw [nearMass_eq_fibres,Finset.sum_div]
    _ ≤ ∑ _k ∈ cellPositions A t gamma,(2*K:ℝ)/A.b t.1 t.2 :=
      Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = ((cellPositions A t gamma).card:ℝ)*((2*K:ℝ)/A.b t.1 t.2) := by simp
    _ ≤ (2*(gamma*A.b t.1 t.2))*((2*K:ℝ)/A.b t.1 t.2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp [hbR.ne']; ring

end ContingencyTables.RootedNearMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalTables
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Feasible physical tables retain unit mass for the selected roots -/

namespace ContingencyTables.RootedPhysicalTables

open scoped BigOperators Classical
open CompanionFactorialApplication TreeMarginalSignature BalancedCellFibres
open CompanionPhysicalTables (Feasible PhysicalTables physicalTable assignment_physicalTable cardinality_eq)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem feasible_weight_one (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (a : Profiles (cellWidth A))
    (ha : Feasible A a) :
    RootedPenalty.physicalWeight A R alpha (BalancedCellFibres.profile (cellWidth A) a)=1 := by
  have hh := RootedTreeMarginal.tableAssignment_unit A R alpha (physicalTable A a) ha.1 ha.2.1 ha.2.2
  rwa [assignment_physicalTable A a ha.1] at hh

/-- Every original bounded table contributes exactly one unit, so the
actual normalizer always dominates the table count. -/
theorem table_count_le_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    (Fintype.card (BoundedTable (fun i => (A.r i).toNat) (fun j => (A.c j).toNat) A.b):ℝ) ≤
      RootedPhysicalNormalizer.physicalMass A R alpha := by
  have hcount : (∑ a : Profiles (cellWidth A),if Feasible A a then (1:ℝ) else 0)=
      (Fintype.card (PhysicalTables A):ℝ) := by
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [Fintype.card_subtype]
  rw [← cardinality_eq,← hcount]
  unfold RootedPhysicalNormalizer.physicalMass
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · rw [feasible_weight_one A R alpha a ha]
  · exact RootedPenalty.physicalWeight_nonnegative A R alpha _

end ContingencyTables.RootedPhysicalTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTerminalRegions
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root infeasibility lies in the literal far or near region -/

namespace ContingencyTables.RootedTerminalRegions

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables RootedFarMass RootedNearMass
open ForestPenaltyApplication TreeMarginalSignature BalancedCellFibres EqualitySoftening
open CompanionTerminalRegions (integerDeviation deviation_eq_integer nonTree_bounded
  treePenalty_nonnegative physicalRow_eq_table)
open CompanionNearMass (cellPositions)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootPenalty_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) :
    0 ≤ RootedPenalty.rootPenalty A R (BalancedCellFibres.profile (cellWidth A) a) := by
  unfold RootedPenalty.rootPenalty
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> first | exact abs_nonneg _ | exact le_rfl

lemma root_deviation_le_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) (v : I⊕J)
    (hv : RootedPenalty.rootFlag R v=true) : |(integerDeviation A a v:ℝ)| ≤ actualPenalty A R a := by
  have hh := Finset.single_le_sum
    (f := fun g => if RootedPenalty.rootFlag R g then
      |deviation (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
        A.r A.c (BalancedCellFibres.profile (cellWidth A) a) g| else 0)
    (fun g _ => by split_ifs <;> first | exact abs_nonneg _ | exact le_rfl)
    (Finset.mem_univ v)
  simp only [hv,ite_true, if_true,deviation_eq_integer] at hh
  exact hh.trans (by
    unfold actualPenalty RootedPenalty.penalty RootedPenalty.rootPenalty RootedPenalty.ell RootedPenalty.widths
    simp_rw [deviation_eq_integer]
    linarith [treePenalty_nonnegative A a])

lemma tree_distance_le_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (a : Profiles (cellWidth A)) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) :
    max 0 (max (-(physicalTable A a t.1 t.2:ℝ))
      ((physicalTable A a t.1 t.2:ℝ)-A.b t.1 t.2))/(A.b t.1 t.2:ℝ) ≤ actualPenalty A R a := by
  let z := BalancedCellFibres.profile (cellWidth A) a
  let D : I → J → ℝ := fun i j => if A.T.Adj (.inl i) (.inr j) then
    affineDistance (ForestLiteralCount.lower A.T A.d A.b i j) 1 (A.b i j) (z ((i,j),false)) /
      (A.b i j:ℝ) else 0
  have hD (i : I) (j : J) : 0 ≤ D i j := by
    dsimp only [D]
    split_ifs
    · exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
    · exact le_rfl
  have hinner := Finset.single_le_sum (fun j _ => hD t.1 j) (Finset.mem_univ t.2)
  have houter := Finset.single_le_sum
    (f := fun i => ∑ j,D i j)
    (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)) (Finset.mem_univ t.1)
  have hh : D t.1 t.2 ≤ treePenalty A.T A.b (ForestLiteralCount.lower A.T A.d A.b) z :=
    hinner.trans houter
  dsimp only [D] at hh
  rw [ite_eq_left ht] at hh
  simp only [affineDistance,mul_one] at hh
  have hrow := physicalRow_eq_table A a t.1 t.2
  change (ForestLiteralCount.lower A.T A.d A.b t.1 t.2:ℝ)+(z ((t.1,t.2),false):ℝ)=_ at hrow
  rw [hrow] at hh
  exact hh.trans (by
    unfold actualPenalty RootedPenalty.penalty RootedPenalty.ell
    linarith [rootPenalty_nonnegative A R a])

/-- Positive mass and penalty below one force every literal margin to
hold: nonroots are exact indicators and root discrepancies are integral. -/
lemma margins_of_small_penalty (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A R alpha a)
    (hp : actualPenalty A R a < 1) :
    (∀ i,(∑ j,physicalTable A a i j)=A.r i) ∧
      (∀ j,(∑ i,physicalTable A a i j)=A.c j) := by
  have hnonroot : ∀ v,RootedPenalty.rootFlag R v=false → integerDeviation A a v=0 := by
    have hh := hw
    unfold actualWeight at hh
    rw [RootedPenalty.exact_eq] at hh
    by_cases h : ∀ g,RootedPenalty.rootFlag R g=false →
        deviation (RootedPenalty.ell A) (RootedPenalty.widths A)
          A.r A.c (BalancedCellFibres.profile (cellWidth A) a) g=0
    · intro v hv
      have hz := h v hv
      change deviation (ForestLiteralCount.lower A.T A.d A.b)
        (ForestLiteralCount.width A.T A.d A.b) A.r A.c
        (BalancedCellFibres.profile (cellWidth A) a) v=0 at hz
      rw [deviation_eq_integer] at hz
      exact_mod_cast hz
    · rw [ite_eq_right h] at hh
      exact False.elim ((lt_irrefl (0:ℝ)) hh)
  have hall (v : I⊕J) : integerDeviation A a v=0 := by
    cases hv : RootedPenalty.rootFlag R v
    · exact hnonroot v hv
    · have hh := (root_deviation_le_penalty A R a v hv).trans_lt hp
      have hz : |integerDeviation A a v| < (1:ℤ) := by exact_mod_cast hh
      have hz' := abs_lt.mp hz
      omega
  constructor
  · intro i
    have hh := hall (.inl i)
    simpa only [integerDeviation,Sum.elim_inl,sub_eq_zero] using hh
  · intro j
    have hh := hall (.inr j)
    simpa only [integerDeviation,Sum.elim_inr,sub_eq_zero] using hh

theorem infeasible_in_far_or_near (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma)
    (a : Profiles (cellWidth A)) (hw : 0 < actualWeight A R alpha a) (hbad : ¬Feasible A a) :
    4*(K:ℝ) ≤ alpha*actualPenalty A R a ∨
      ∃ t : I×J,A.T.Adj (.inl t.1) (.inr t.2) ∧ a t ∈ cellPositions A t gamma := by
  by_cases hfar : 4*(K:ℝ) ≤ alpha*actualPenalty A R a
  · exact Or.inl hfar
  right
  have hp : actualPenalty A R a < gamma := by
    have hh : alpha*actualPenalty A R a < alpha*gamma := (lt_of_not_ge hfar).trans_le hscale
    exact lt_of_mul_lt_mul_left hh ha.le
  have hm := margins_of_small_penalty A R alpha a hw (hp.trans_le hg1)
  have hcell : ¬∀ i j,0 ≤ physicalTable A a i j ∧ physicalTable A a i j ≤ A.b i j := by
    intro hc
    exact hbad ⟨hc,hm⟩
  obtain ⟨i,hi⟩ := not_forall.mp hcell
  obtain ⟨j,hviol⟩ := not_forall.mp hi
  have ht : A.T.Adj (.inl i) (.inr j) := by
    by_contra ht
    exact hviol (nonTree_bounded A a i j ht)
  refine ⟨(i,j),ht,?_⟩
  have hb : (0:ℝ) < A.b i j := by exact_mod_cast (A.hlarge i j (A.hTG ht)).2
  have hd := (tree_distance_le_penalty A R a (i,j) ht).trans_lt hp
  have hdist : max 0 (max (-(physicalTable A a i j:ℝ))
      ((physicalTable A a i j:ℝ)-A.b i j)) < gamma*A.b i j := (div_lt_iff₀ hb).mp hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change ((physicalTable A a i j<0) ∧ -(physicalTable A a i j:ℝ)<gamma*A.b i j) ∨
    (((A.b i j:ℤ)<physicalTable A a i j) ∧ (physicalTable A a i j:ℝ)-A.b i j<gamma*A.b i j)
  by_cases hlo : 0 ≤ physicalTable A a i j
  · right
    refine ⟨lt_of_not_ge (fun hhi => hviol ⟨hlo,hhi⟩),?_⟩
    exact (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hdist
  · left
    exact ⟨lt_of_not_ge hlo,(le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hdist⟩

end ContingencyTables.RootedTerminalRegions

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTerminalMass
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual selected-root terminal normalizer approximates the table count -/

namespace ContingencyTables.RootedTerminalMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalTables RootedPhysicalTables RootedPhysicalNormalizer
open RootedFarMass RootedNearMass RootedTerminalRegions BalancedCellFibres TreeMarginalSignature
open CompanionNearMass (cellPositions)
open CompanionTerminalMass (TreeCell Endpoints tableCount tableCount_ge_one treeCell_card_le
  feasible_sum_eq_tableCount)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Actual endpoint tables and the proved scalar signature estimates
control the entire union of narrow tree violations. -/
lemma total_near_mass_le (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A) (alpha gamma : ℝ)
    (ha : 0 ≤ alpha) (hg : 0 < gamma) (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K) :
    (∑ t : TreeCell A,nearMass A R alpha t.val gamma) ≤
      (4*A.d*gamma*K:ℝ)*physicalMass A R alpha := by
  have hM : 0 < physicalMass A R alpha := by
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
      ((tableCount_ge_one A).trans (table_count_le_mass A R alpha))
  have hh (t : TreeCell A) : nearMass A R alpha t.val gamma ≤
      (4*gamma*K:ℝ)*physicalMass A R alpha := by
    apply (div_le_iff₀ hM).mp
    exact near_mass_bound A R alpha gamma t.val t.property ha hg hW B K hB hBK hK
      (E.lowerTable t) (E.upperTable t) (E.lowerBounds t) (E.upperBounds t)
      (E.lowerRows t) (E.lowerColumns t) (E.upperRows t) (E.upperColumns t)
      (E.lowerAttains t) (E.upperAttains t)
  calc
    _ ≤ ∑ _t : TreeCell A,(4*gamma*K:ℝ)*physicalMass A R alpha :=
      Finset.sum_le_sum (fun t _ => hh t)
    _ = (Fintype.card (TreeCell A):ℝ)*((4*gamma*K:ℝ)*physicalMass A R alpha) := by simp
    _ ≤ (A.d:ℝ)*((4*gamma*K:ℝ)*physicalMass A R alpha) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast treeCell_card_le A) (by positivity)
    _ = _ := by ring

lemma mass_le_table_far_near (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha gamma : ℝ) (K : ℕ)
    (ha : 0 < alpha) (hg1 : gamma ≤ 1) (hscale : 4*(K:ℝ) ≤ alpha*gamma) :
    physicalMass A R alpha ≤ tableCount A+
      (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
        then actualWeight A R alpha a else 0)+
      ∑ t : TreeCell A,nearMass A R alpha t.val gamma := by
  have hh := TerminalMassCover.mass_le_cover (actualWeight A R alpha) (Feasible A)
    (fun a => 4*(K:ℝ) ≤ alpha*actualPenalty A R a)
    (fun t : TreeCell A => fun a => a t.val ∈ cellPositions A t.val gamma)
    (fun a => RootedPenalty.physicalWeight_nonnegative A R alpha _)
    (fun a ha => feasible_weight_one A R alpha a ha)
    (by
      intro a hw hbad
      rcases infeasible_in_far_or_near A R alpha gamma K ha hg1 hscale a hw hbad with hf|⟨t,ht,hn⟩
      · exact Or.inl hf
      · exact Or.inr ⟨⟨t,ht⟩,hn⟩)
  change physicalMass A R alpha ≤ _ at hh
  rw [feasible_sum_eq_tableCount] at hh
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold nearMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a t.val∈cellPositions A t.val gamma <;> simp only [ha,ite_true, if_true,ite_false]

/-- The terminal normalizer estimate follows from the finite table
bijection, root integrality, far bound and tree-marginal estimates.
The manuscript's explicit choices of K, gamma and the final coefficient
satisfy its arithmetic conditions. -/
theorem terminal_count_estimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A)
    (alpha gamma epsilon : ℝ) (B K : ℕ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hscale : 4*(K:ℝ) ≤ alpha*gamma) (hnear : 4*(A.d:ℝ)*gamma*K ≤ epsilon/128)
    (hfar : (2:ℝ)^(-(3*K:ℕ):ℝ) ≤ epsilon/128)
    (hW : 20*A.d ≤ A.W) (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B)
    (hBK : 2*B ≤ K) (hK : 0 < K) :
    tableCount A ≤ CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (RootedFactorialApplication.f A R alpha) ∅ ∧
      CommonBasesFPRAS.slotTotal TwoLiftStates.pairs (RootedFactorialApplication.f A R alpha) ∅ ≤ (1+epsilon/32)*tableCount A := by
  rw [normalizer_eq_physical_mass]
  have hZM : tableCount A ≤ physicalMass A R alpha := table_count_le_mass A R alpha
  have hM1 := (tableCount_ge_one A).trans hZM
  have hM : 0 ≤ physicalMass A R alpha := by linarith
  have hcover := mass_le_table_far_near A R alpha gamma K ha hg1 hscale
  have hfarMass := (far_mass_le A R alpha B K hW hB hBK).trans hfar
  have hfarScaled : (∑ a : Profiles (cellWidth A),if 4*(K:ℝ) ≤ alpha*actualPenalty A R a
      then actualWeight A R alpha a else 0) ≤ (epsilon/128)*physicalMass A R alpha := by
    exact hfarMass.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM1
        (show 0 ≤ epsilon/128 by positivity))
  have hnearMass := total_near_mass_le A R E alpha gamma ha.le hg hW B K hB hBK hK
  have hnearScaled : (∑ t : TreeCell A,nearMass A R alpha t.val gamma) ≤
      (epsilon/128)*physicalMass A R alpha :=
    hnearMass.trans (mul_le_mul_of_nonneg_right hnear hM)
  have hbad : physicalMass A R alpha ≤ tableCount A+(epsilon/64)*physicalMass A R alpha := by
    linarith
  exact TerminalMassCover.relative_count_bound (tableCount A) (physicalMass A R alpha) epsilon
    (by linarith [tableCount_ge_one A]) he he1 hZM hbad

end ContingencyTables.RootedTerminalMass

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTerminalApplication
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root terminal counts and successful phase histories -/

namespace ContingencyTables.RootedTerminalApplication

open scoped BigOperators Classical
open CompanionFactorialApplication RootedTerminalMass CompanionTerminalParameters
open RootedAnnealing RootedWarmStart
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase final_parameter)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem terminal_normalizer (A : Instance I J) (R : RootedCompletion.Selection A.T) (E : Endpoints A) (L : ℕ) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L) :
    tableCount A ≤ total A R (finalPhase A L epsilon) ∧
      total A R (finalPhase A L epsilon) ≤ (1+epsilon/32)*tableCount A := by
  have hh := terminal_count_estimate A R E (coefficient L A.d epsilon)
    (gamma L A.d epsilon) epsilon L (allowance L A.d epsilon)
    (by exact_mod_cast coefficient_positive L A.d epsilon A.hd he)
    (gamma_positive L A.d epsilon A.hd he) (gamma_le_one L A.d epsilon A.hd he1)
    he he1 (terminal_scale L A.d epsilon A.hd he)
    (near_fraction L A.d epsilon A.hd).le (far_fraction L A.d epsilon he)
    hW hL (allowance_bits L A.d epsilon) (allowance_positive L A.d epsilon)
  simpa only [total,weight,final_parameter] using hh

end ContingencyTables.RootedTerminalApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredEstimate
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Soundness of the actual stored rational count estimate -/

namespace ContingencyTables.RootedStoredEstimate

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedWarmStart RootedPhaseTrial
open CompanionReferenceAccuracy (relative_of_log_error)
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma initialTotal_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (initialTotal A:ℝ)=total A R 0 := by
  rw [total,total_zero]
  simp only [initialTotal,CompanionInitialization.freeTotal,Rat.cast_mul,Rat.cast_prod,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Nat.cast_add,Nat.cast_one]

lemma initialStored_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (∀ p q,0 < (initialStored A).multiplier p q) ∧ 0 < (initialStored A).estimate := by
  constructor
  · exact initial_positive A
  · have h : (0:ℝ) < (initialTotal A:ℝ) := by
      rw [initialTotal_cast A R]
      exact total_positive A R 0
    exact_mod_cast h

/-- The actual rational estimates telescope through their proved
per-phase multiplicative errors, including every weight-oracle error. -/
theorem stored_log_error (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (stored : ℕ → Stored A) (hinit : stored 0=initialStored A)
    (xi : ℚ) (eta : ℝ) (H : ℕ)
    (hstep : ∀ j,j < H → ValidOutput A R j (stored j) xi eta (stored (j+1))) :
    0 < (stored H).estimate ∧
      |Real.log (((stored H).estimate:ℝ)/total A R H)| ≤
        (H:ℝ)*(4*(xi:ℝ)+4*eta) := by
  induction H with
  | zero =>
    rw [hinit]
    refine ⟨(initialStored_positive A R).2,?_⟩
    have he : ((initialStored A).estimate:ℝ)=total A R 0 := initialTotal_cast A R
    rw [he,div_self (total_positive A R 0).ne']
    simp
  | succ H ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    have hnext := hstep H (by omega)
    have hold : (0:ℝ) < ((stored H).estimate:ℝ) := by exact_mod_cast hprev.1
    have hnew : (0:ℝ) < ((stored (H+1)).estimate:ℝ) := by exact_mod_cast hnext.2.1
    have hT := total_positive A R H
    have hT' := total_positive A R (H+1)
    have heq : ((stored (H+1)).estimate:ℝ)/total A R (H+1)=
        (((stored H).estimate:ℝ)/total A R H)*
          (((stored (H+1)).estimate:ℝ)/
            (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H))) := by
      field_simp [hold.ne',hT.ne',hT'.ne']
    refine ⟨hnext.2.1,?_⟩
    rw [heq,Real.log_mul (div_ne_zero hold.ne' hT.ne')
      (div_ne_zero hnew.ne' (mul_ne_zero hold.ne' (div_ne_zero hT'.ne' hT.ne')))]
    have hb := abs_add_le
      (Real.log (((stored H).estimate:ℝ)/total A R H))
      (Real.log (((stored (H+1)).estimate:ℝ)/
        (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H))))
    have hs : |Real.log (((stored (H+1)).estimate:ℝ)/
        (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H)))| ≤
        4*(xi:ℝ)+4*eta := hnext.2.2.2
    push_cast
    nlinarith [hprev.2]

theorem stored_count_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (E : Endpoints A) (L : ℕ) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (stored : ℕ → Stored A) (hinit : stored 0=initialStored A)
    (xi : ℚ) (eta : ℝ)
    (herr : (finalPhase A L epsilon:ℝ)*(4*(xi:ℝ)+4*eta) ≤ epsilon/50)
    (hstep : ∀ j,j < finalPhase A L epsilon →
      ValidOutput A R j (stored j) xi eta (stored (j+1))) :
    (1-epsilon)*tableCount A ≤ ((stored (finalPhase A L epsilon)).estimate:ℝ) ∧
      ((stored (finalPhase A L epsilon)).estimate:ℝ) ≤ (1+epsilon)*tableCount A := by
  have hs := stored_log_error A R stored hinit xi eta (finalPhase A L epsilon) hstep
  have hZ := total_positive A R (finalPhase A L epsilon)
  have hratio := relative_of_log_error epsilon
    (((stored (finalPhase A L epsilon)).estimate:ℝ)/total A R (finalPhase A L epsilon))
    he0 he1 (div_pos (by exact_mod_cast hs.1) hZ) (hs.2.trans herr)
  have hb : (1-epsilon/4)*total A R (finalPhase A L epsilon) ≤
        ((stored (finalPhase A L epsilon)).estimate:ℝ) ∧
      ((stored (finalPhase A L epsilon)).estimate:ℝ) ≤
        (1+epsilon/4)*total A R (finalPhase A L epsilon) :=
    ⟨(le_div_iff₀ hZ).mp hratio.1,(div_le_iff₀ hZ).mp hratio.2⟩
  apply final_estimate_accuracy epsilon (tableCount A) (total A R (finalPhase A L epsilon))
    ((stored (finalPhase A L epsilon)).estimate:ℝ) he0 he1 (by linarith [tableCount_ge_one A])
  · have ht := RootedTerminalApplication.terminal_normalizer A R E L epsilon he0 he1 hW hL
    refine ⟨ht.1,ht.2.trans ?_⟩
    nlinarith [tableCount_ge_one A]
  · exact hb

end
end ContingencyTables.RootedStoredEstimate

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedStoredHistory
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stored rational outputs of the actual outer phases

The initial record is at index zero. Later records are the outputs
stored in the finite history; the initial record also supplies every
unused future entry to the restart's multiplier function.
-/

namespace ContingencyTables.RootedStoredHistory

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedStoredEstimate RootedPhaseTrial
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- The rational value actually stored at the terminal history index
has the counting guarantee whenever every executed update is valid. -/
theorem count_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (E : Endpoints A) (L : ℕ) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (xi : ℚ) (eta : ℝ)
    (herr : (finalPhase A L epsilon:ℝ)*(4*(xi:ℝ)+4*eta) ≤ epsilon/50)
    (history : List (Stored A)) (hlen : history.length=finalPhase A L epsilon)
    (hg : Good A R xi eta history) :
    (1-epsilon)*tableCount A ≤ ((lookup A history history.length).estimate:ℝ) ∧
      ((lookup A history history.length).estimate:ℝ) ≤ (1+epsilon)*tableCount A := by
  rw [hlen]
  exact stored_count_accuracy A R E L epsilon he0 he1 hW hL (lookup A history) rfl xi eta
    herr (fun j hj => hg j (by simpa only [hlen] using hj))

end
end ContingencyTables.RootedStoredHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive phases on a common finite Boolean word space -/

namespace ContingencyTables.RootedPhaseHistory

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (stepBits)
open RootedStoredHistory
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

private lemma fold_length {X Y : Type*} (f : List Y → X → Y) (xs : List X) (ys : List Y) :
    (xs.foldl (fun history x => history++[f history x]) ys).length=ys.length+xs.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]
    omega

lemma decoded_length (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) : (decoded A R s words).length=words.length := by
  simpa only [decoded,List.length_nil,Nat.zero_add] using fold_length (step A R s) words []

end
end ContingencyTables.RootedPhaseHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

lemma tolerance_pos (H : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < tolerance H epsilon := by
  unfold tolerance
  positivity

lemma tolerance_le_quarter (H : ℕ) (epsilon : ℚ) (he0 : 0 < epsilon)
    (he1 : epsilon < 1) : tolerance H epsilon ≤ 1/4 := by
  unfold tolerance
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 800*(H+1))).mpr
  have hH : (1:ℚ) ≤ H+1 := by have h0 := Nat.cast_nonneg (α := ℚ) H; linarith
  nlinarith

lemma returnCap_pos (p H tau : ℕ) : 0 < returnCap p H tau := by
  unfold returnCap
  positivity

lemma precision_pos (H tau N n : ℕ) (eta : ℚ) : 0 < precision H tau N n eta := by
  unfold precision
  omega

lemma noise_pos (H tau N n : ℕ) (eta : ℚ) : 0 < noise H tau N n eta := by
  unfold noise
  exact one_div_pos.mpr (by exact_mod_cast precision_pos H tau N n eta)

lemma noise_le_tolerance (H tau N n : ℕ) (eta : ℚ) (he : 0 < eta) :
    noise H tau N n eta ≤ eta := by
  have hceil := Nat.le_ceil (1/eta)
  have hbound : (1/eta:ℚ) ≤ precision H tau N n eta := by
    apply hceil.trans
    exact_mod_cast (show ⌈1/eta⌉₊ ≤ precision H tau N n eta by unfold precision; omega)
  have hp : (0:ℚ) < precision H tau N n eta := by
    exact_mod_cast precision_pos H tau N n eta
  unfold noise
  apply (div_le_iff₀ hp).mpr
  have hb := (div_le_iff₀ he).mp hbound
  nlinarith

lemma reciprocal_two_pow (k : ℕ) (hk : 0 < k) :
    1/(2:ℝ)^k ≤ 1/(k:ℝ) := by
  have hnat : k ≤ 2^k := Nat.lt_two_pow_self.le
  exact one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast hnat)

lemma precision_error (H tau N n : ℕ) (eta : ℚ) :
    1/(2:ℝ)^(precision H tau N n eta) ≤ (noise H tau N n eta:ℝ) := by
  simpa only [noise,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using
    reciprocal_two_pow (precision H tau N n eta) (precision_pos H tau N n eta)

lemma initial_error (H : ℕ) :
    2/(2:ℝ)^(initialPrecision H) ≤ 1/(1024*((H:ℝ)+1)) := by
  have hk : 0 < initialPrecision H := by unfold initialPrecision; positivity
  have hp := mul_le_mul_of_nonneg_left (reciprocal_two_pow (initialPrecision H) hk)
    (show (0:ℝ) ≤ 2 by norm_num)
  have he : 2*(1/(initialPrecision H:ℝ))=1/(1024*((H:ℝ)+1)) := by
    simp only [initialPrecision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  calc
    2/(2:ℝ)^(initialPrecision H)=2*(1/(2:ℝ)^(initialPrecision H)) := by ring
    _ ≤ 2*(1/(initialPrecision H:ℝ)) := hp
    _ = _ := he

lemma observations_error (p W H : ℕ) (eta : ℚ) (he : 0 < eta) :
    (observationCoefficient p W:ℝ)/
      (((observations p W H eta+1:ℕ):ℝ)*(eta:ℝ)^2) ≤
        1/(1024*((H:ℝ)+1)) := by
  have heta : (0:ℝ) < eta := by exact_mod_cast he
  have hceil := Nat.le_ceil ((1024:ℚ)*(H+1)*observationCoefficient p W/eta^2)
  have hraw : (1024:ℝ)*((H:ℝ)+1)*observationCoefficient p W/(eta:ℝ)^2 ≤
      observations p W H eta+1 := by
    have hn : ⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊ ≤
        observations p W H eta+1 := by unfold observations; omega
    have hh := hceil.trans (show
        (⌈(1024:ℚ)*(H+1)*observationCoefficient p W/eta^2⌉₊:ℚ) ≤
          observations p W H eta+1 by exact_mod_cast hn)
    exact_mod_cast hh
  have hmul := (div_le_iff₀ (sq_pos_of_pos heta)).mp hraw
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

lemma cap_error (p H tau : ℕ) :
    40*(H:ℝ)*tau*p^2/(returnCap p H tau:ℝ) ≤ 1/(1024*((H:ℝ)+1)) := by
  have hnat : 40960*H*tau*p^2*(H+1) ≤ returnCap p H tau := by
    unfold returnCap
    calc
      _ = 40960*(H*(H+1))*tau*p^2 := by ring
      _ ≤ 65536*((H+1)^2)*(tau+1)*(p^2+1) := by
        have hHH : H*(H+1) ≤ (H+1)^2 := by nlinarith
        exact Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul (by decide : 40960 ≤ 65536) hHH)
            (Nat.le_succ tau)) (Nat.le_succ (p^2))
  have hr : (0:ℝ) < returnCap p H tau := by exact_mod_cast returnCap_pos p H tau
  rw [div_le_div_iff₀ hr (by positivity)]
  have hb : ((40960*H*tau*p^2*(H+1):ℕ):ℝ) ≤ returnCap p H tau := by exact_mod_cast hnat
  push_cast at hb
  nlinarith

lemma noise_error (H tau N n : ℕ) (eta : ℚ) :
    (noiseCoefficient H tau N n:ℝ)*(noise H tau N n eta:ℝ) ≤
      1/(1024*((H:ℝ)+1)) := by
  have hnat : 1024*(H+1)*noiseCoefficient H tau N n ≤ precision H tau N n eta := by
    unfold precision
    omega
  have hp : (0:ℝ) < precision H tau N n eta := by
    exact_mod_cast precision_pos H tau N n eta
  simp only [noise,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,mul_one_div]
  rw [div_le_div_iff₀ hp (by positivity)]
  have hb : ((1024*(H+1)*noiseCoefficient H tau N n:ℕ):ℝ) ≤
      precision H tau N n eta := by exact_mod_cast hnat
  push_cast at hb
  nlinarith

lemma logarithmic_error (H tau N n : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (H:ℝ)*(4*(noise H tau N n (tolerance H epsilon):ℝ)+
      4*(tolerance H epsilon:ℝ)) ≤ (epsilon:ℝ)/50 := by
  have hxi := noise_le_tolerance H tau N n (tolerance H epsilon) (tolerance_pos H epsilon he)
  have hxiR : (noise H tau N n (tolerance H epsilon):ℝ) ≤ tolerance H epsilon := by
    exact_mod_cast hxi
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he
  have heq : (tolerance H epsilon:ℝ)=(epsilon:ℝ)/(800*((H:ℝ)+1)) := by
    simp only [tolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_one]
  have hm : (H:ℝ)+1 > 0 := by positivity
  have ht : (tolerance H epsilon:ℝ)*(800*((H:ℝ)+1))=(epsilon:ℝ) := by
    rw [heq]
    exact div_mul_cancel₀ _ (by positivity)
  have htol : (0:ℝ) < tolerance H epsilon := by exact_mod_cast tolerance_pos H epsilon he
  nlinarith

/-- The four error terms correspond to empirical observations,
initialization, restart caps and the accumulated query/transition error. -/
lemma combine_error (p H tau N n k h : ℕ) (c eta xi allowance : ℝ)
    (hxi : 0 ≤ xi) (hprec : 1/(2:ℝ)^k ≤ xi)
    (hobs : c/(((N+1:ℕ):ℝ)*eta^2) ≤ allowance)
    (hinit : 2/(2:ℝ)^h ≤ allowance)
    (hcap : 40*(H:ℝ)*tau*p^2/(n:ℝ) ≤ allowance)
    (hnoise : (noiseCoefficient H tau N n:ℝ)*xi ≤ allowance) :
    c/(((N+1:ℕ):ℝ)*eta^2)+
      (N:ℝ)*((6*xi+1/(2:ℝ)^k)/2)+
      2*(1/(2:ℝ)^h+(H:ℝ)*((tau:ℝ)*
        (20*(p:ℝ)^2/n+((n+1:ℕ):ℝ)*((6*xi+1/(2:ℝ)^k)/2))))+
      2*((N+1:ℕ):ℝ)*xi ≤ 4*allowance := by
  let e := (6*xi+1/(2:ℝ)^k)/2
  have he : e ≤ 4*xi := by dsimp only [e]; linarith
  have hrow : (N:ℝ)*e+2*(H:ℝ)*tau*((n+1:ℕ):ℝ)*e+
      2*((N+1:ℕ):ℝ)*xi ≤ (noiseCoefficient H tau N n:ℝ)*xi := by
    calc
      _ = ((N:ℝ)+2*(H:ℝ)*tau*((n+1:ℕ):ℝ))*e+
          2*((N+1:ℕ):ℝ)*xi := by ring
      _ ≤ ((N:ℝ)+2*(H:ℝ)*tau*((n+1:ℕ):ℝ))*(4*xi)+
          2*((N+1:ℕ):ℝ)*xi := by
        exact _root_.add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) (le_refl _)
      _ ≤ (noiseCoefficient H tau N n:ℝ)*xi := by
        simp only [noiseCoefficient,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
        nlinarith [mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hxi]
  have heq : c/(((N+1:ℕ):ℝ)*eta^2)+
      (N:ℝ)*((6*xi+1/(2:ℝ)^k)/2)+
      2*(1/(2:ℝ)^h+(H:ℝ)*((tau:ℝ)*
        (20*(p:ℝ)^2/n+((n+1:ℕ):ℝ)*((6*xi+1/(2:ℝ)^k)/2))))+
      2*((N+1:ℕ):ℝ)*xi =
        c/(((N+1:ℕ):ℝ)*eta^2)+2/(2:ℝ)^h+
          40*(H:ℝ)*tau*p^2/n+
          ((N:ℝ)*e+2*(H:ℝ)*tau*((n+1:ℕ):ℝ)*e+2*((N+1:ℕ):ℝ)*xi) := by
    dsimp only [e]
    ring
  rw [heq]
  linarith

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive finite-word counting output and its accuracy -/

namespace ContingencyTables.RootedCountingWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open RootedHistoryConfidence
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma estimate_accurate (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (E : Endpoints A) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^s.L)
    (hfinal : s.H=finalPhase A s.L epsilon) (eta : ℝ)
    (herr : (s.H:ℝ)*(4*(s.xi:ℝ)+4*eta) ≤ epsilon/50)
    (words : Fin s.H → Word A s) (hg : GoodWords A R s eta (List.ofFn words)) :
    (1-epsilon)*tableCount A ≤ (estimate A R s words:ℝ) ∧
      (estimate A R s words:ℝ) ≤ (1+epsilon)*tableCount A := by
  have hlen : (decoded A R s (List.ofFn words)).length=s.H := by
    rw [decoded_length,List.length_ofFn]
  have h := count_accuracy A R E s.L epsilon he0 he1 hW hL s.xi eta
    (by simpa only [hfinal] using herr) (decoded A R s (List.ofFn words))
    (hlen.trans hfinal) hg
  simpa only [hlen,estimate] using h

/-- The actual stored rational value has the stated error probability.
No equality to an ideal empirical-ratio estimator is assumed. -/
theorem accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (E : Endpoints A) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^s.L)
    (hfinal : s.H=finalPhase A s.L epsilon)
    (hC : 0 < s.C) (hB : (s.K:ℝ)=binWidth A s.C)
    (hH : s.H ≤ rationalHeight A s.C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^s.L)
    (hx0 : 0 < s.xi) (hx1 : s.xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) s.K))
    (hp : 0 < Fintype.card (Labels A)) (hn : 0 < s.n)
    (eta : ℝ) (he0' : 0 < eta) (he1' : eta ≤ 1/4)
    (herr : (s.H:ℝ)*(4*(s.xi:ℝ)+4*eta) ≤ epsilon/50) :
    1-(s.H:ℝ)*error A s eta s.H ≤
      uniformAverage (fun words : Fin s.H → Word A s =>
        if (1-epsilon)*tableCount A ≤ (estimate A R s words:ℝ) ∧
          (estimate A R s words:ℝ) ≤ (1+epsilon)*tableCount A then (1:ℝ) else 0) := by
  have hg := history_success A R s hC hB hH hbox hx0 hx1 hPL hCheeger hp hn eta he0' he1'
  apply hg.trans
  apply uniformAverage_mono
  intro words
  by_cases h : GoodWords A R s eta (List.ofFn words)
  · have ha := estimate_accurate A R s E epsilon he0 he1 hW hL hfinal eta herr words h
    simp [h,ha]
  · simp only [h,ite_false]
    split_ifs <;> norm_num

lemma flatEstimate_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (P : ℚ → Prop) :
    uniformAverage (fun bits : Fin (bitCount A s) → Bool =>
      if P (flatEstimate A R s bits) then (1:ℝ) else 0)=
      uniformAverage (fun words : Fin s.H → Word A s =>
        if P (estimate A R s words) then (1:ℝ) else 0) := by
  have he := uniformAverage_equiv (gridWordEquiv s.H (totalWidth A s))
    (fun words : Fin s.H → Word A s =>
      if P (estimate A R s words) then (1:ℝ) else 0)
  refine (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_).trans
    (he.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_))
  · intro bits
    rfl
  · intro words
    rfl

end
end ContingencyTables.RootedCountingWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingSchedule
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit constant-confidence schedule for the actual counting words -/

namespace ContingencyTables.RootedCountingSchedule

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedHistoryStep
open CompanionTargetMixing (restartTime)
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma settings_positive (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K) :
    0 < (settings A C K H L hK hW epsilon v).xi ∧
      (settings A C K H L hK hW epsilon v).xi ≤ 1/4 ∧
      0 < (settings A C K H L hK hW epsilon v).n := by
  dsimp only [settings]
  refine ⟨noise_pos _ _ _ _ _,?_,returnCap_pos _ _ _⟩
  exact (noise_le_tolerance _ _ _ _ _ (tolerance_pos H epsilon he0)).trans
    (tolerance_le_quarter H epsilon he0 he1)

lemma observable_cast (p W : ℕ) :
    (observable p W:ℝ)=ObservableBounds.observableConstant (p:ℝ) ((W:ℝ)^2) := by
  simp only [observable,ObservableBounds.observableConstant,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  ring

lemma error_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    error A (settings A C K H L hK hW epsilon v) (tolerance H epsilon:ℝ) H ≤
      1/(256*((H:ℝ)+1)) := by
  let p := Fintype.card (Labels A)
  let tau := restartTime A H L
  let eta := tolerance H epsilon
  let N := observations p A.W H eta
  let n := returnCap p H tau
  let k := precision H tau N n eta
  let xi := noise H tau N n eta
  have he : 0 < eta := tolerance_pos H epsilon he
  have hc : (observationCoefficient p A.W:ℝ)=32000*(p:ℝ)^8*
      ObservableBounds.observableConstant p ((A.W:ℝ)^2) := by
    simp only [observationCoefficient,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,
      observable_cast]
  have hb := combine_error p H tau N n k (initialPrecision H)
    (observationCoefficient p A.W) eta xi (1/(1024*((H:ℝ)+1)))
    (by exact_mod_cast (noise_pos H tau N n eta).le)
    (precision_error H tau N n eta)
    (observations_error p A.W H eta he)
    (initial_error H)
    (cap_error p H tau)
    (noise_error H tau N n eta)
  have hfour : (4:ℝ)*(1/(1024*((H:ℝ)+1)))=1/(256*((H:ℝ)+1)) := by
    field_simp
    ring
  rw [hfour] at hb
  simpa only [error,settings,hc,p,tau,eta,N,n,k,xi] using hb

lemma total_error_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    (H:ℝ)*error A (settings A C K H L hK hW epsilon v)
      (tolerance H epsilon:ℝ) H ≤ 1/256 := by
  have hb := mul_le_mul_of_nonneg_left (error_bound A C K H L hK hW epsilon he v)
    (Nat.cast_nonneg H : (0:ℝ) ≤ H)
  refine hb.trans ?_
  rw [mul_one_div,div_le_iff₀ (by positivity : (0:ℝ) < 256*((H:ℝ)+1))]
  linarith

lemma logarithmic_bound (A : Instance I J) (C K H L : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (epsilon : ℚ) (he : 0 < epsilon)
    (v : Grid (I := Fin (dimension A)) K) :
    (H:ℝ)*(4*((settings A C K H L hK hW epsilon v).xi:ℝ)+
      4*(tolerance H epsilon:ℝ)) ≤ (epsilon:ℝ)/50 :=
  logarithmic_error H (restartTime A H L)
    (observations (Fintype.card (Labels A)) A.W H (tolerance H epsilon))
    (returnCap (Fintype.card (Labels A)) H (restartTime A H L)) epsilon he

/-- Constant success for the actual finite Boolean estimator. The
binary confidence parameter is handled by independent medians afterward. -/
theorem constant_success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (epsilon : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K) (E : Endpoints A)
    (hW' : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hfinal : H=finalPhase A L (epsilon:ℝ))
    (hC : 0 < C) (hB : (K:ℝ)=binWidth A C) (hH : H ≤ rationalHeight A C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (hp : 0 < Fintype.card (Labels A)) :
    255/256 ≤ uniformAverage (fun bits :
      Fin (RootedCountingWords.bitCount A (settings A C K H L hK hW epsilon v)) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤
            (RootedCountingWords.flatEstimate A R (settings A C K H L hK hW epsilon v) bits:ℝ) ∧
          (RootedCountingWords.flatEstimate A R (settings A C K H L hK hW epsilon v) bits:ℝ) ≤
            (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  let s := settings A C K H L hK hW epsilon v
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have heR1 : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  have hs := settings_positive A C K H L hK hW epsilon he0 he1 v
  have htR : (tolerance H epsilon:ℝ) ≤ 1/4 := by
    have ht := tolerance_le_quarter H epsilon he0 he1
    have ht' : (tolerance H epsilon:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr ht
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at ht'
    exact ht'
  have hprob := RootedCountingWords.accuracy A R s E epsilon heR heR1 hW' hL hfinal
    hC hB hH hbox hs.1 hs.2.1 hPL hCheeger hp hs.2.2
    (tolerance H epsilon) (by exact_mod_cast tolerance_pos H epsilon he0)
    htR
    (logarithmic_bound A C K H L hK hW epsilon he0 v)
  have hb := total_error_bound A C K H L hK hW epsilon he0 v
  have hlaw := RootedCountingWords.flatEstimate_law A R s (fun estimate =>
    (1-(epsilon:ℝ))*tableCount A ≤ (estimate:ℝ) ∧
      (estimate:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A)
  apply ((show (255/256:ℝ) ≤ 1-(H:ℝ)*error A s (tolerance H epsilon:ℝ) H by
    linarith).trans hprob).trans_eq
  refine (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_).trans
    (hlaw.symm.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_))
  · intro words
    split_ifs <;> rfl
  · intro bits
    split_ifs <;> rfl

end
end ContingencyTables.RootedCountingSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalSchedule
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

lemma capacity_product_bound (A : Instance I J) :
    (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^capacityBits A := by
  calc
    _ ≤ ∏ a : I×J,2^(A.b a.1 a.2+1).size :=
      Finset.prod_le_prod' (fun a _ => (Nat.lt_size_self (A.b a.1 a.2+1)).le)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

lemma small_product_bound (A : Instance I J) :
    (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤
      (2:ℝ)^capacityBits A := by
  have he := Fintype.prod_subtype_mul_prod_subtype
    (fun a : I×J => A.small a.1 a.2=true) (fun a => A.b a.1 a.2+1)
  have hr : 1 ≤ ∏ a : {a : I×J // ¬A.small a.1 a.2=true},(A.b a.val.1 a.val.2+1) := by
    apply Finset.one_le_prod'
    intro a _
    omega
  have hs : (∏ a : SmallCell A,(A.b a.val.1 a.val.2+1)) ≤
      ∏ a : I×J,(A.b a.1 a.2+1) := by
    rw [←he]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact_mod_cast hs.trans (capacity_product_bound A)

lemma finalPhase_eq (A : Instance I J) (L : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    CompanionTerminalApplication.finalPhase A L (epsilon:ℝ)=
      rationalHeight A (coefficient L A.d epsilon) := by
  rw [CompanionTerminalApplication.finalPhase,←coefficient_eq L A.d A.hd epsilon he]
  rfl

end
end ContingencyTables.CountingTerminalSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma ceiling_val (e : Fraction) : ceiling e=⌈TreeFraction.val e⌉₊ := by
  by_cases h : e.2=0
  · simp only [ceiling,OffsetCountPrograms.ceilQuotient,TreeFraction.val,h,Nat.div_zero,
      Nat.cast_zero,div_zero,Nat.ceil_zero]
  · exact OffsetCountPrograms.ceilQuotient_eq e.1 e.2 (Nat.pos_of_ne_zero h)

lemma natural_val (n : ℕ) : TreeFraction.val (natural n)=(n:ℚ) := by
  simp only [natural,TreeFraction.val,Nat.cast_one,div_one]

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma Expr.eval_pow (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a.pow n).eval xs=(a.eval xs)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Expr.pow,Expr.eval,ih,pow_succ]


@[simp] lemma Expr.eval_power (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a^n).eval xs=(a.eval xs)^n := Expr.eval_pow a n xs


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma observationNumerator_value (P W H T N R L : ℕ) :
    observationNumerator.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.observationCoefficient P W := by
  simp [observationNumerator,observable,p,w,h,Expr.eval,
    CountingPhaseSchedule.observationCoefficient,CountingPhaseSchedule.observable]

end ContingencyTables.CountingPhaseScalarProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

lemma tolerance_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (tolerance ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.tolerance H (TreeFraction.val e) := by
  rw [tolerance,TreeFraction.div_val,scalarFraction,natural_val]
  simp [scalar,toleranceDenominator,CountingPhaseScalarProgram.h,Expr.eval,
    CountingPhaseSchedule.tolerance]

lemma observations_val (P W H T N R L : ℕ) (e : Fraction) :
    observations ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [observations,ceiling_val,observationRatio,TreeFraction.div_val,
    scalarFraction,natural_val,toleranceSquare,TreeFraction.mul_val,tolerance_val]
  change ⌈((CountingPhaseScalarProgram.observationNumerator.eval [P,W,H,T,N,R,L]:ℕ):ℚ)/
    (CountingPhaseSchedule.tolerance H (TreeFraction.val e)*
      CountingPhaseSchedule.tolerance H (TreeFraction.val e))⌉₊+1= _
  rw [CountingPhaseScalarProgram.observationNumerator_value]
  simp only [CountingPhaseSchedule.observations,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,pow_two]

end ContingencyTables.CountingPhaseParametersProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

lemma insert_fold (q : Fraction) (xs : List Fraction) :
    xs.reverse.foldl (fun s x => step (x,s)) (q,([],[q])) = (q,(xs,insertRaw q xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    rfl

lemma insert_eq (q : Fraction) (xs : List Fraction) : insert (q,xs)=insertRaw q xs := by
  unfold insert
  rw [insert_fold]

lemma insert_pos (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) : ∀ y∈insertRaw q xs,0 < y.2 := by
  induction xs with
  | nil => simpa only [insertRaw,List.mem_singleton] using fun y hy => hy ▸ hq
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw]
    split <;> intro y hy <;> simp only [List.mem_cons] at hy
    · rcases hy with rfl|hy
      · exact hxx
      · exact ht y hy
    · rcases hy with rfl|rfl|hy
      · exact hq
      · exact hxx
      · exact hx y (by simp [hy])

lemma insert_map (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) :
    (insertRaw q xs).map val=(xs.map val).orderedInsert (·≤·) (val q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw,List.map_cons,List.orderedInsert_cons,TreeFraction.less_val x q hxx hq]
    by_cases h : val x < val q
    · simp [h,not_le.mpr h,ht]
    · simp [h,le_of_not_gt h]

lemma sort_cons (x : Fraction) (xs : List Fraction) : sort (x::xs)=insert (x,sort xs) := by
  simp only [sort,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma sort_pos (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) : ∀ y∈sort xs,0 < y.2 := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    rw [sort_cons,insert_eq]
    exact insert_pos x (sort xs) (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

lemma sort_map (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) :
    (sort xs).map val=(xs.map val).mergeSort (·≤·) := by
  rw [List.mergeSort_eq_insertionSort]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ y∈xs,0 < y.2 := fun y hy => hx y (by simp [hy])
    rw [sort_cons,insert_eq,insert_map x (sort xs) (hx x (by simp)) (sort_pos xs ht),ih ht]
    rfl

lemma median_val (xs : List Fraction) :
    val (median xs)=CommonBasesFPRAS.rationalMedian (xs.map val) := by
  have hs := sort_map (xs.map TreeFraction.normalize) (by
    intro y hy
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
    exact normalize_den_pos x)
  have hm : (xs.map TreeFraction.normalize).map val=xs.map val := by
    simp only [List.map_map,Function.comp_def,normalize_val]
  rw [hm] at hs
  unfold median CommonBasesFPRAS.rationalMedian
  rw [←hs,List.length_map]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (sort (xs.map TreeFraction.normalize))[xs.length/2]? <;> simp only [Option.getD_none,Option.map_none,Option.getD_some,Option.map_some,val, Nat.cast_zero,zero_div]

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

lemma SameLaw.map {f : X → Z} {g : Y → Z} (h : SameLaw f g) (F : Z → W) :
    SameLaw (fun x => F (f x)) (fun y => F (g y)) := by
  intro phi
  exact h (fun z => phi (F z))

lemma SameLaw.independent {f : X → Z} {g : Y → Z} (h : SameLaw f g) (N : ℕ) :
    SameLaw (fun xs : Fin N → X => fun i => f (xs i))
      (fun ys : Fin N → Y => fun i => g (ys i)) := by
  intro phi
  exact uniformAverage_independent_eq f g h N phi

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

theorem width_value (z : Input) :
    width z=CountingWordsBound.wordPolynomial.eval (measure z)+
      CountingMarkerBounds.paddingPolynomial.eval (measure z)+2*measure z+1 := by
  simp only [width,widthExpression,phaseExpression,initialExpression,stageExpression,stepExpression,
    medianExpression,estimatorExpression,sampleExpression,timeExpression,binExpression,innerExpression,x,
    Expr.eval_power,Expr.eval,CountingWordsBound.wordPolynomial,CountingWordsBound.phasePolynomial,
    CountingWordsBound.initialPolynomial,CountingWordsBound.stagePolynomial,CountingWordsBound.stepPolynomial,
    CountingOracleWordBounds.medianPolynomial,CountingOracleWordBounds.estimatorPolynomial,
    CountingOracleWordBounds.samplePolynomial,CountingOracleWordBounds.timePolynomial,
    CountingOracleWordBounds.binPolynomial,CountingOracleWordBounds.innerPolynomial,
    CountingMarkerBounds.paddingPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,List.getD_cons_zero]

theorem width_pos (z : Input) : 0 < width z := by rw [width_value]; omega

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingAmplification
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence for the actual adaptive counting estimator -/

namespace ContingencyTables.RootedCountingAmplification

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedCountingSchedule
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary FiniteMedianConfidence
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- The confidence parameter changes only the number of independent
complete runs, never the internal per-oracle failure allowance. -/
theorem success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (v : Grid (I := Fin (dimension A)) K) (E : Endpoints A)
    (hW' : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hfinal : H=finalPhase A L ((epsilon/2:ℚ):ℝ))
    (hC : 0 < C) (hB : (K:ℝ)=binWidth A C) (hH : H ≤ rationalHeight A C)
    (hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤ (2:ℝ)^L)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (hp : 0 < Fintype.card (Labels A)) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits :
      Fin (bitCount A (settings A C K H L hK hW (epsilon/2) v) delta) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤
            (estimate A R (settings A C K H L hK hW (epsilon/2) v) delta bits:ℝ) ∧
          (estimate A R (settings A C K H L hK hW (epsilon/2) v) delta bits:ℝ) ≤
            (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  let s := settings A C K H L hK hW (epsilon/2) v
  let f := RootedCountingWords.flatEstimate A R s
  have heh0 : (0:ℚ) < epsilon/2 := by positivity
  have heh1 : epsilon/2 < 1 := by linarith
  have hbase := constant_success A R C K H L hK hW (epsilon/2) heh0 heh1 v E
    hW' hL hfinal hC hB hH hbox hPL hCheeger hp
  have hbase' : 1-(1/256:ℝ) ≤ uniformAverage
      (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
        if (1-((epsilon/2:ℚ):ℝ))*tableCount A ≤ (f bits:ℝ) ∧
          (f bits:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*tableCount A then (1:ℝ) else 0) := by
    refine (show 1-(1/256:ℝ) ≤ 255/256 by norm_num).trans (hbase.trans_eq ?_)
    exact CompanionPhaseWords.average_ext_instances _ _ _ _ (fun bits => by split_ifs <;> rfl)
  have hfailure := CompanionPhaseWords.failure_of_success
    (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
      (1-((epsilon/2:ℚ):ℝ))*tableCount A ≤ (f bits:ℝ) ∧
        (f bits:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*tableCount A)
    (1/256) (hbase'.trans_eq
      (CompanionPhaseWords.average_ext_instances _ _ _ _ (fun bits => by split_ifs <;> rfl)))
  have hbad : uniformAverage (fun bits : Fin (RootedCountingWords.bitCount A s) → Bool =>
      if (f bits:ℝ) < (1-(epsilon:ℝ)/2)*tableCount A ∨
        (1+(epsilon:ℝ)/2)*tableCount A < (f bits:ℝ) then (1:ℝ) else 0) ≤ 5/16 := by
    have hh : (1/256:ℝ) ≤ 5/16 := by norm_num
    apply le_trans ?_ hh
    simpa only [not_and_or,not_le,Rat.cast_div,Rat.cast_ofNat] using hfailure
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hZ : (0:ℝ) < tableCount A := by linarith [tableCount_ge_one A]
  have hm := median_confidence_real f
    ((1-(epsilon:ℝ))*tableCount A) ((1-(epsilon:ℝ)/2)*tableCount A)
    ((1+(epsilon:ℝ)/2)*tableCount A) ((1+(epsilon:ℝ))*tableCount A)
    (by nlinarith) (by nlinarith) delta hd hbad
  let test := fun words : Fin (repetitionCount delta) →
      (Fin (RootedCountingWords.bitCount A s) → Bool) =>
    if (1-(epsilon:ℝ))*tableCount A ≤
        (rationalMedian (List.ofFn (fun i => f (words i))):ℝ) ∧
      (rationalMedian (List.ofFn (fun i => f (words i))):ℝ) ≤
        (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0
  have heq := uniformAverage_equiv
    (gridWordEquiv (repetitionCount delta) (RootedCountingWords.bitCount A s)) test
  have htransport : uniformAverage test = uniformAverage
      (fun bits : Fin (bitCount A s delta) → Bool =>
        if (1-(epsilon:ℝ))*tableCount A ≤ (estimate A R s delta bits:ℝ) ∧
          (estimate A R s delta bits:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A
        then (1:ℝ) else 0) := by
    refine heq.symm.trans (CompanionPhaseWords.average_ext_instances _ _ _ _ ?_)
    intro bits
    rfl
  exact hm.trans_eq htransport

end
end ContingencyTables.RootedCountingAmplification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComputedTableTightening
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact table bijection for the computed attained endpoints

The endpoint hypotheses of the translation lemma are discharged by the
executed minimum and maximum searches, conditional only on EK1972.
-/

namespace ContingencyTables.ComputedTableTightening

open TableTightening
open scoped Classical

variable {m n : ℕ}

variable (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
  (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
  (hne : ∃ X,Feasible r c b X)

include hEK hne

theorem count_eq : Fintype.card (BoundedTable r c b)=
    Fintype.card (BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b)) :=
  Fintype.card_congr (tighteningEquiv hEK r c b hne)

end ContingencyTables.ComputedTableTightening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComputedCompanionInstance
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A literal companion instance from binary bounded margins

All operational data are read from the executed endpoint, flow, and
maximum-forest programs. The existential endpoint witnesses are used
only in the terminal-mass proof, never to define an executed output.
-/

namespace ContingencyTables.ComputedCompanionInstance

open CompanionFactorialApplication ComputedTableTightening
open scoped BigOperators Classical

variable {m n : ℕ}

/-- Tightening preserves the count consumed by the terminal estimator. -/
theorem original_count (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    CompanionTerminalMass.tableCount (instanceData hEK r c b hne W hW)=
      (Fintype.card (BoundedTable r c b):ℝ) := by
  unfold CompanionTerminalMass.tableCount
  have he := (ComputedTableTightening.count_eq hEK r c b hne).symm
  calc
    _ = (Fintype.card (BoundedTable (newRows r c b) (newColumns r c b)
        (newBounds r c b)):ℝ) := by
      apply congrArg (fun k : ℕ=>(k:ℝ))
      exact Fintype.card_congr (Equiv.refl _)
    _ = _ := congrArg (fun k : ℕ=>(k:ℝ)) he

end ContingencyTables.ComputedCompanionInstance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma data_dimension (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).d=dimensionAllowance (m:=m) (n:=n) := rfl

lemma data_capacityBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    CountingTerminalSchedule.capacityBits (data hEK r c b hne epsilon he)=capacityBits r c b := rfl

lemma binCount_cast (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (binCount r c b epsilon:ℝ)=binWidth (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := by
  simp only [binCount,binWidth,data_dimension,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma phases_final (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=CompanionTerminalApplication.finalPhase
      (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ) := by
  rw [CountingTerminalSchedule.finalPhase_eq _ _ (epsilon/2) (by positivity)]
  rfl

lemma phases_height (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=rationalHeight (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := rfl

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual counting experiment on original bounded-table inputs

This is the positive-label branch of the computed-input experiment.
Its output is the stored adaptive rational estimate, after independent
median amplification. Only the cited analytic/flow inputs are external.
-/

namespace ContingencyTables.ComputedCountingWords

open CompanionFactorialApplication CommonBasesFPRAS GridBoundary
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

/-- The computed preprocessing and schedule satisfy every input of the
proved adaptive-history theorem. There is no supplied forest, baseline,
endpoint table, or oracle-error assumption in this statement. -/
theorem positive_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hp : 0<Fintype.card (Labels (data hEK r c b hne epsilon he))) :
    1-(delta:ℝ)≤uniformAverage (fun bits : Fin (bitCount hEK r c b hne epsilon he delta)→Bool =>
      if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (estimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (estimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := by
  let A:=data hEK r c b hne epsilon he
  let K:=binCount r c b epsilon
  have hK : 1≤K:=binCount_pos r c b epsilon he
  have hW : 100*A.d*K≤A.W:=(cutoff_eq hEK r c b hne epsilon he).ge
  have hW' : 20*A.d≤A.W := by
    have hh:=Nat.mul_le_mul_left (100*A.d) hK
    simp only [Nat.mul_one] at hh
    exact (show 20*A.d≤100*A.d by omega).trans (hh.trans hW)
  have hL : (∏ a : Fin m×Fin n,(A.b a.1 a.2+1))≤2^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.capacity_product_bound A
  have hbox : (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1))≤
      (2:ℝ)^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.small_product_bound A
  have hcount : CompanionTerminalMass.tableCount A=(Fintype.card (BoundedTable r c b):ℝ) :=
    ComputedCompanionInstance.original_count hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)
  have hs:=RootedCountingAmplification.success A (root hEK r c b hne epsilon he)
    (coefficient r c b epsilon) K (phases r c b epsilon) (capacityBits r c b)
    hK hW epsilon delta he he1 hd (start hEK r c b hne epsilon he)
    (ComputedCompanionInstance.endpoints hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)) hW' hL
    (phases_final hEK r c b hne epsilon he) (coefficient_pos r c b epsilon he)
    (binCount_cast hEK r c b hne epsilon he) (phases_height hEK r c b hne epsilon he).le
    hbox (hPL _) (hCheeger _ _) hp
  rw [hcount] at hs
  exact hs

end
end ContingencyTables.ComputedCountingWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

open CompanionFactorialApplication
open scoped BigOperators Classical
variable {m n : ℕ}

lemma catalogInput_data (A : Instance (Fin m) (Fin n)) :
    catalogInput (RootedForestCatalog.data A)=CompanionCellCatalog.input A := rfl

lemma count_data (A : Instance (Fin m) (Fin n)) :
    count (RootedForestCatalog.data A)=Fintype.card (Labels A) := by
  rw [count,capacities,catalogInput_data,CompanionCellCatalog.capacities_eq,List.sum_ofFn]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fintype.sum_equiv (CompanionCellCatalog.cellEquiv A) _ _ (fun _ => rfl)

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

lemma precision_val (e : Fraction) (hn : 0 < e.1) :
    precision e=CountingTerminalSchedule.precision (val e) := by
  unfold precision CountingTerminalSchedule.precision
  rw [ceilQuotient_eq e.2 e.1 hn]
  congr 2
  simp only [val,one_div,inv_div]

lemma allowance_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) :
    allowance ((L,d),e)=CountingTerminalSchedule.allowance L d (val e) := by
  simp only [allowance,CountingTerminalSchedule.allowance,precision_val e hn]

lemma coefficient_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) (hd : 0 < e.2) :
    coefficient ((L,d),e)=CountingTerminalSchedule.coefficient L d (val e) := by
  unfold coefficient
  rw [ceilQuotient_eq _ _ hn]
  unfold CountingTerminalSchedule.coefficient
  rw [←allowance_val L d e hn]
  congr 1
  simp only [numerator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,val]
  field_simp

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

lemma half_val (e : TreeFraction.Fraction) : TreeFraction.val (half e)=TreeFraction.val e/2 := by
  simp only [half,TreeFraction.val,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma capacityBits_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    capacityBits (data r c b)=ComputedCountingParameters.capacityBits r c b := by
  unfold capacityBits
  rw [TightenedInputProgram.compute_code]
  simp only [data,ResidualGraphProgram.natCode,List.map_flatten,List.map_ofFn,Function.comp_def,
    List.sum_flatten,List.sum_ofFn,cellBits,ComputedCountingParameters.capacityBits,
    Fintype.sum_prod_type]

lemma dimension_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    dimension (data r c b)=ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) := by
  simp only [dimension,data,List.length_ofFn,ComputedCountingParameters.dimensionAllowance]

lemma coefficient_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient (data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.coefficient r c b epsilon := by
  unfold coefficient frame
  rw [capacityBits_data,dimension_data]
  have hn : 0 < (half (TreeFraction.repr epsilon)).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  have hd : 0 < (half (TreeFraction.repr epsilon)).2 := by
    change 0 < 2*epsilon.den
    exact Nat.mul_pos (by decide) epsilon.pos
  rw [CountingCoefficientProgram.coefficient_val _ _ _ hn hd,half_val,
    TreeFraction.val_repr he.le]
  rfl

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma binCount_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    binCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.binCount r c b epsilon := by
  unfold binCount base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data]
  unfold ComputedCountingParameters.binCount
  ring

lemma cutoff_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    cutoff (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.cutoff r c b epsilon := by
  unfold cutoff
  rw [CountingBaseProgram.dimension_data,binCount_data r c b epsilon he]
  rfl

lemma phases_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    phases (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.phases r c b epsilon := by
  unfold phases base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data,cutoff_data r c b epsilon he]
  unfold ComputedCountingParameters.phases
  ring

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedForestCode
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed forest retains its literal adjacency-list code -/

namespace ContingencyTables.ComputedLargeForest
open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped Classical

variable {m n : ℕ}

private lemma code_congr {N : ℕ} (G H : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G=H) : graphCode G=graphCode H := by
  subst H
  apply congrArg (@graphCode N G)
  exact Subsingleton.elim _ _

lemma computed_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1 ≤ W) :
    graphCode ((computed r c b W).comap finSumFinEquiv.symm)=
      ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W) := by
  obtain ⟨F,hF,_⟩ := iterate_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
    ((m+n)*(m+n)) (by
      have hb := unordered_pair_budget (n:=m+n)
      omega)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  have hout : ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)=graphCode F := by
    unfold ForestGreedyProgram.forest ForestGreedyProgram.prepare
    rw [←hzero (fun a b => Classical.propDecidable _),execute_iterate,graphCode_length]
    exact congrArg Prod.fst hF
  have hc : (computed r c b W).comap finSumFinEquiv.symm=
      decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)) := by
    ext u v
    change (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).Adj
      (vertexEquiv (finSumFinEquiv.symm u)) (vertexEquiv (finSumFinEquiv.symm v)) ↔ _
    simp only [vertexEquiv,Equiv.apply_symm_apply]
  have he : (computed r c b W).comap finSumFinEquiv.symm=F := by
    simpa only [hout,decoded_graphCode] using hc
  exact (code_congr _ _ he).trans hout.symm

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

open scoped Classical
variable {m n : ℕ}

lemma catalogData_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    catalogData (data r c b,W)=RootedForestCatalog.data
      (ComputedCompanionInstance.instanceData hEK r c b hne W hW) := by
  unfold catalogData forestFrame
  rw [TightenedInputProgram.compute_code]
  unfold RootedForestCatalog.data ComputedCompanionInstance.instanceData
  rw [ComputedLargeForest.computed_code _ _ _ W (by omega)]
  simp only [data,Int.toNat_natCast,ResidualGraphProgram.natCode,matrixCode]

lemma baseline_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    TightenedInputProgram.baseline (data r c b)=matrixCode
      (fun i j => ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat) := by
  obtain ⟨Y,hY,_,_⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  rw [hY]
  unfold matrixCode
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [ComputedCompanionInstance.instanceData,ComputedCompanionInstance.baseline,
    hY,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Int.toNat_natCast]

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma catalog_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedForestCatalog.data (ComputedCountingParameters.data hEK r c b hne epsilon he) := by
  unfold catalog
  rw [CountingTerminalProgram.cutoff_data r c b epsilon he]
  exact ComputedRootedInput.catalogData_instance hEK r c b hne _ _

lemma labelCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    labelCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) := by
  rw [labelCount,catalog_data hEK r c b hne epsilon he,CountingLabelCountProgram.count_data]

lemma basic_values (P W H L : ℕ) :
    vector controlExpressions [P,W,H,0,0,0,L]=
      [P,W,H,4*CountingPhaseSchedule.observable P W*(H+P+L+5),0,
        CountingPhaseSchedule.returnCap P H (4*CountingPhaseSchedule.observable P W*(H+P+L+5)),L] := by
  simp [vector,controlExpressions,CountingPhaseScalarProgram.p,CountingPhaseScalarProgram.w,
    CountingPhaseScalarProgram.h,capacityBits,restartTime,observable,fullReturnCap,Expr.eval,
    CountingPhaseSchedule.observable,CountingPhaseSchedule.returnCap]

lemma fillObservations_values (P W H T N R L : ℕ) (e : CountingOracleScheduleProgram.Fraction) :
    fillObservations ([P,W,H,T,N,R,L],e)=
      ([P,W,H,T,CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)),R,L],e) := by
  simp [fillObservations,CountingPhaseParametersProgram.observations_val]

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingSettingsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed controls are the proven counting schedule -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS CompanionFactorialApplication
open CountingPhaseParametersProgram
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parameters_values (z : Input) (P W H L : ℕ)
    (hz : preliminary z=[P,W,H,0,0,0,L]) :
    parameters z=
      (let T := 4*CountingPhaseSchedule.observable P W*(H+P+L+5)
       let eta := CountingPhaseSchedule.tolerance H (TreeFraction.val z.2/2)
       ([P,W,H,T,CountingPhaseSchedule.observations P W H eta,
         CountingPhaseSchedule.returnCap P H T,L],CountingBaseProgram.half z.2)) := by
  unfold parameters basic
  rw [hz,basic_values,fillObservations_values,CountingBaseProgram.half_val]

lemma parameters_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,
        s.N,s.n,s.L],CountingBaseProgram.half (TreeFraction.repr epsilon)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hp : preliminary (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      [Fintype.card (Labels A),A.W,H,0,0,0,L] := by
    unfold preliminary
    rw [labelCount_data hEK r c b hne epsilon he,
      CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingTerminalProgram.phases_data r c b epsilon he,CountingBaseProgram.capacityBits_data]
    rfl
  rw [parameters_values _ _ _ _ _ hp,TreeFraction.val_repr he.le]
  have ht : 4*CountingPhaseSchedule.observable (Fintype.card (Labels A)) A.W*
      (H+Fintype.card (Labels A)+L+5)=CompanionTargetMixing.restartTime A H L := by
    simp only [CountingPhaseSchedule.observable,CompanionTargetMixing.restartTime,
      CompanionTrace.time,CompanionTrace.integerConstant]
    ring
  dsimp only
  rw [ht]
  rfl

end
end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

lemma demand_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    demand (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedDemandProgram.data (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (fun _ _ => 0) (ComputedCountingParameters.data hEK r c b hne epsilon he).b := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hc : catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hb : baseline (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      matrixCode (fun i j => (A.X i j).toNat) := by
    exact ComputedRootedInput.baseline_instance hEK r c b hne _ (ComputedCountingParameters.cutoff_two r c b epsilon he)
  have hcap : capacity (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode A.b := by
    rw [capacity,hc]
    rfl
  have hz : zeroMatrix (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode (fun (_ : Fin m) (_ : Fin n) => 0) := by
    rw [zeroMatrix,hcap]
    simp only [matrixCode,List.map_ofFn,Function.comp_def]
  unfold demand RootedDemandProgram.data
  rw [hc,hb,hz,hcap]

lemma state_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    state (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedOracleWalkProgram.data A C 0 K (fun _ => 0)
        (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hp : parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)) := by
    unfold parameters
    rw [CountingBaseProgram.dimension_data,CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingBaseProgram.coefficient_data r c b epsilon he]
    rfl
  have hz : ForestCountIdentification.smallX A.small (fun _ => 0)=(fun _ _ => 0) := by
    funext i j
    simp [ForestCountIdentification.smallX]
  have hq : (fun i j => A.b i j-ForestCountIdentification.smallY A.small (fun _ => 0) i j)=A.b := by
    funext i j
    simp [ForestCountIdentification.smallY]
  unfold state RootedOracleWalkProgram.data
  rw [CountingTerminalProgram.binCount_data r c b epsilon he,hp,hz,hq,demand_data hEK r c b hne epsilon he]
  apply congrArg (fun coords => ((ComputedCountingParameters.binCount r c b epsilon,
    (((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)),
      RootedDemandProgram.data A (fun _ _ => 0) A.b)),coords))
  unfold zeroGrid catalog
  rw [CountingComputedSettings.catalog_data hEK r c b hne epsilon he]
  simp [DensePrograms.gridNatCode,start,GridBoundary.corner,RootedCatalogGrid.freeCount]

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionRepetitionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma count_val (x : TreeFraction.Fraction) : count x=CommonBasesFPRAS.repetitionCount (TreeFraction.val x) := by
  simp only [count,TreeFraction.normalize_repr,TreeFraction.repr,CommonBasesFPRAS.repetitionCount]
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed initial record is the literal adaptive counting record -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionMultiplierMatrixProgram TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (reserve : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),reserve)=
      CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  unfold prepared CountingPreparedState.output
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingComputedSettings.parameters_data hEK r c b hne epsilon he]
  rfl

end
end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RepeatedFractionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type} [Codec X]

variable {f : X×List Bool→TreeFraction.Fraction}

attribute [local irreducible] samples

open GridBoundary CommonBasesFPRAS

omit [Codec X] in
theorem output_ofFn (x : X) (r w : ℕ) (hw : 0 < w) (bits : Fin (r*w)→Bool) :
    TreeFraction.val (output f ((x,(r,w)),List.ofFn bits))=
      rationalMedian (List.ofFn (fun i : Fin r =>
        TreeFraction.val (f (x,List.ofFn (gridWordEquiv r w bits i))))) := by
  rw [output,MedianFractionProgram.median_val]
  have hwords : words ((x,(r,w)),List.ofFn bits)=
      List.ofFn (fun i : Fin r => List.ofFn (gridWordEquiv r w bits i)) := by
    change (wordChunks (w,List.ofFn bits)).take r=_
    rw [wordChunks_ofFn hw]
    exact List.take_of_length_le (by simp)
  unfold samples
  rw [hwords]
  simp only [List.map_ofFn]
  rfl

end ContingencyTables.RepeatedFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer confidence repetition of the executed counting program -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped CommonBasesFPRAS GridBoundary

variable (single : Input→TreeFraction.Fraction) (F : Realizer single)
variable (width : Request→ℕ) (N : Realizer width)

attribute [local irreducible] prepared

lemma output_ofFn (req : Request) (hw : 0 < width req)
    (bits : Fin (budget width req)→Bool) :
    TreeFraction.val (output single width (req,List.ofFn bits))=
      rationalMedian (List.ofFn (fun i : Fin (repeats req) =>
        TreeFraction.val (single (req,List.ofFn (gridWordEquiv (repeats req) (width req) bits i))))) := by
  unfold output prepared
  exact RepeatedFractionProgram.output_ofFn (f := single) req (repeats req) (width req) hw bits

end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and public word budget of outer confidence repetition -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS GridBoundary CommonBasesFPRAS FiniteObservableTransport Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section

variable (single : Input→TreeFraction.Fraction) (width : Request→ℕ)

theorem sameLaw (req : Request) (hw : 0 < width req) (K : ℕ) (g : (Fin K→Bool)→ℚ)
    (hs : SameLaw (fun bits : Fin (width req)→Bool => TreeFraction.val (single (req,List.ofFn bits))) g) :
    SameLaw (fun bits : Fin (budget width req)→Bool =>
      TreeFraction.val (output single width (req,List.ofFn bits)))
      (fun bits : Fin (repeats req*K)→Bool =>
        rationalMedian (List.ofFn (fun i => g (gridWordEquiv (repeats req) K bits i)))) := by
  let R := repeats req
  let f := fun bits : Fin (width req)→Bool => TreeFraction.val (single (req,List.ofFn bits))
  have hp := (hs.independent R).map (fun xs : Fin R→ℚ => rationalMedian (List.ofFn xs))
  intro phi
  have hleft := uniformAverage_equiv (gridWordEquiv R (width req))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => f (xs i)))))
  have hright := uniformAverage_equiv (gridWordEquiv R K)
    (fun xs => phi (rationalMedian (List.ofFn (fun i => g (xs i)))))
  have hout : uniformAverage (fun bits : Fin (budget width req)→Bool =>
      phi (TreeFraction.val (output single width (req,List.ofFn bits)) ))=
      uniformAverage (fun bits : Fin (R*width req)→Bool =>
        phi (rationalMedian (List.ofFn (fun i => f (gridWordEquiv R (width req) bits i))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (output_ofFn single width req hw bits)
  exact hout.trans (hleft.trans ((hp phi).trans hright.symm))

variable {m n : ℕ}

lemma repeats_request (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (hd : 0 < delta) :
    repeats (CountingDirectProgram.request r c b epsilon delta)=repetitionCount delta := by
  change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
  rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]

end
end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] historyInput

theorem phaseWidth_pos (req : Request) : 0 < phaseWidth req :=
  CompanionUniformPhaseWidth.width_pos _

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input semantics of the positive counting adapter -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      CompanionUniformPhaseWidth.data A s
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  exact CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he []

theorem phaseCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    phaseCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  unfold phaseCount
  rw [prepared_data hEK r c b hne epsilon he delta]
  rfl

theorem phases_pos (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  have hC := ComputedCountingParameters.coefficient_pos r c b epsilon he
  have hd : 0 < ComputedCountingParameters.dimensionAllowance (m := m) (n := n) := by
    unfold ComputedCountingParameters.dimensionAllowance
    omega
  change 0 < ComputedCountingParameters.phases r c b epsilon
  unfold ComputedCountingParameters.phases
  positivity

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedSourceLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence amplification preserves the executed source law -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem positive_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) (hd : 0<delta)
    (hs : SameLaw
      (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (CountingPositiveProgram.output
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    SameLaw (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
      TreeFraction.val (positive (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (ComputedCountingWords.estimate hEK r c b hne epsilon he delta) := by
  have hpos : 0<CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta) := by
    unfold CountingPositiveProgram.bitCount CountingDirectProgram.request
    rw [CountingPositiveProgram.phaseCount_data hEK r c b hne epsilon he]
    exact Nat.mul_pos (CountingPositiveProgram.phases_pos hEK r c b hne epsilon he)
      (CountingPositiveProgram.phaseWidth_pos _)
  have h := CountingAmplifiedProgram.sameLaw CountingPositiveProgram.output CountingPositiveProgram.bitCount
    (CountingDirectProgram.request r c b epsilon delta) hpos _ _ hs
  rw [CountingAmplifiedProgram.repeats_request r c b epsilon delta hd] at h
  exact h

theorem positive_success_oai (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hp : 0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)))
    (hs : SameLaw
      (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (CountingPositiveProgram.output
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0) := by
  have hl := positive_sameLaw hEK r c b hne epsilon delta he hd hs
  have ha := ComputedCountingWords.positive_success hEK hPL hCheeger r c b hne epsilon delta he he1 hd hp
  exact ha.trans_eq (hl (fun q => if CountingBranchProgram.Accurate r c b epsilon q then (1:ℝ) else 0)).symm

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CountingExecutedMachine.positive_success_oai := @OAI.ContingencyTables.CountingExecutedMachine.positive_success_oai

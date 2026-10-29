-- Prove2me | solution 1 for OAI.ContingencyTables.ComputedCountingZero.zero_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:19:56.402684+00:00
-- url     : https://prove2.me/submissions/93c6e71f-b14b-44fe-a96a-6912b42f8ac5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_RootedOracleDensity_goodEstimate_failure

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_AnnealingMultipliers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The companion's multiplier update from empirical type counts

The old multiplier cancels from the update relative to the current ideal
multiplier. Relative accuracy of two positive type means, followed by the
proved adjacent-parameter factor two, gives the required factor four at
the next parameter. This is deterministic algebra of the actual update.
-/

namespace ContingencyTables.AnnealingMultipliers

variable {eta p q ph qh w ideal nextIdeal : ℝ}

theorem empirical_positive (hp : 0<p) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph) : 0<ph := by
  have h : 0<(1-eta)*p := mul_pos (by linarith) hp
  exact h.trans_le hph

/-- The normalized ratio of two empirically observed positive means. -/
theorem relative_ratio (hp : 0<p) (hq : 0<q) (he0 : 0≤eta) (he : eta≤1/4)
    (hph : (1-eta)*p≤ph ∧ ph≤(1+eta)*p)
    (hqh : (1-eta)*q≤qh ∧ qh≤(1+eta)*q) :
    0<ph*q/(qh*p) ∧
      1/2≤ph*q/(qh*p) ∧ ph*q/(qh*p)≤2 ∧
      |Real.log (ph*q/(qh*p))|≤4*eta := by
  have hp' := empirical_positive hp he hph.1
  have hq' := empirical_positive hq he hqh.1
  have hden : 0<qh*p := mul_pos hq' hp
  have hr : 0<ph*q/(qh*p) := div_pos (mul_pos hp' hq) hden
  have hlow : (1-eta)*(p*q)≤ph*q := by nlinarith [mul_le_mul_of_nonneg_right hph.1 hq.le]
  have hupp : ph*q≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hph.2 hq.le]
  have dlow : (1-eta)*(p*q)≤qh*p := by nlinarith [mul_le_mul_of_nonneg_right hqh.1 hp.le]
  have dupp : qh*p≤(1+eta)*(p*q) := by nlinarith [mul_le_mul_of_nonneg_right hqh.2 hp.le]
  have hpq : 0≤p*q := (mul_pos hp hq).le
  have htwice : (1+eta)*(p*q)≤2*((1-eta)*(p*q)) := by
    have := mul_nonneg (show 1-3*eta≥0 by linarith) hpq
    nlinarith
  have hlo : 1/2≤ph*q/(qh*p) := by
    rw [le_div_iff₀ hden]
    linarith
  have hup : ph*q/(qh*p)≤2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hstretch : (1+eta)*(p*q)≤(1+4*eta)*((1-eta)*(p*q)) := by
    have hcoeff : 0≤2*eta-4*eta^2 := by nlinarith
    have := mul_nonneg hcoeff hpq
    nlinarith
  have hscale : 0≤1+4*eta := by linarith
  have hrup : ph*q/(qh*p)≤1+4*eta := by
    rw [div_le_iff₀ hden]
    have := mul_le_mul_of_nonneg_left dlow hscale
    nlinarith
  have hinvup : (ph*q/(qh*p))⁻¹≤1+4*eta := by
    rw [inv_div]
    rw [div_le_iff₀ (mul_pos hp' hq)]
    have := mul_le_mul_of_nonneg_left hlow hscale
    nlinarith
  have hlogup := Real.log_le_sub_one_of_pos hr
  have hloglo := Real.one_sub_inv_le_log_of_pos hr
  refine ⟨hr,hlo,hup,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

end ContingencyTables.AnnealingMultipliers

end OAI
end

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Absolute component totals sum to at most the total absolute demand.
Each vertex is counted in one component, including isolated vertices. -/
theorem sum_abs_componentTotal (root : V → V) (r : V → ℝ) :
    (∑ a, |∑ v, if root v=a then r v else 0|)≤∑ v, |r v| := by
  calc
    _ ≤ ∑ a, ∑ v, |if root v=a then r v else 0| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      have he (a v : V) : |if root v=a then r v else 0|=
          if root v=a then |r v| else 0 := by split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      simp

end Generic

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionAnnealing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent actual companion weights and ideal multipliers

The parameter step is 1/(H/A). Its factor-two bounds are proved from
the literal forest penalty bound, then passed to the actual labelled
weights and their exact transversal/defect totals.
-/

namespace ContingencyTables.CompanionAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The source's j*A/H parameter is exactly j/(H/A), for its literal
integer H=10*A*d²*(W+1). The arbitrary positive penalty coefficient
therefore cancels from every adjacent-phase estimate below. -/
lemma source_parameter (A : Instance I J) (coefficient j : ℕ) (hc : 0< coefficient) :
    (j:ℝ)*(coefficient:ℝ)/((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=
      (j:ℝ)/scale A := by
  have hcR : (coefficient:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  have hQ : scale A≠0 := (scale_positive A).ne'
  have he : ((10*coefficient*A.d^2*(A.W+1):ℕ):ℝ)=(coefficient:ℝ)*scale A := by
    unfold scale
    push_cast
    ring
  rw [he]
  field_simp [hcR,hQ]

end ContingencyTables.CompanionAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinPopulation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer bin populations for the companion weight evaluator -/

namespace ContingencyTables.CompanionBinPopulation

open scoped BigOperators Classical

variable {C : Type*} [Fintype C]

lemma assignment_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    Fintype.card (Assignments B N v)=∏ c,(FairBits.fiber B (N c) (v c)).card := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_coe]

/-- The product formula is exactly B^e times the integer bin population
divided by the total number of free assignments. -/
lemma population_eq_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    population B N v=(B:ℚ)^Fintype.card C*(Fintype.card (Assignments B N v):ℚ)/
      (∏ c,(N c:ℚ)) := by
  rw [assignment_card]
  simp only [population,coordinatePopulation,Finset.prod_div_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Nat.cast_prod]

private lemma reverse_bernoulli (u : ℚ) (hu : 0 ≤ u) (n : ℕ) :
    (1+u)^n*(1-(n:ℚ)*u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1+u)*(1-((n:ℚ)+1)*u) ≤ 1-(n:ℚ)*u := by
      nlinarith [mul_nonneg (show (0:ℚ) ≤ n+1 by positivity) (sq_nonneg u)]
    calc
      _ = (1+u)^n*((1+u)*(1-((n:ℚ)+1)*u)) := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        ring
      _ ≤ (1+u)^n*(1-(n:ℚ)*u) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
      _ ≤ 1 := ih

/-- The source's alpha_v lies between one half and two, including the
empty-coordinate product. No large interval is enumerated to establish
the bound; its exact cardinality is the proved ceiling difference. -/
theorem population_bounds (B d : ℕ) (N : C → ℕ) (v : C → ℕ)
    (hB : 0 < B) (hd : 1 ≤ d) (hcard : Fintype.card C ≤ d)
    (hN : ∀ c,100*d*B ≤ N c) (hv : ∀ c,v c < B) :
    1/2 ≤ population B N v ∧ population B N v ≤ 2 := by
  let u : ℚ := 1/(100*(d:ℚ))
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp only [u]
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hcountQ : (Fintype.card C:ℚ) ≤ d := by exact_mod_cast hcard
  have hsum : (Fintype.card C:ℚ)*u ≤ 1/100 := by
    dsimp only [u]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hfactor (c : C) : 1-u ≤ coordinatePopulation B (N c) (v c) ∧
      coordinatePopulation B (N c) (v c) ≤ 1+u := by
    have hh := abs_le.mp (coordinate_error B (N c) d (v c) hB hd (hN c) (hv c))
    constructor <;> linarith
  have hpos (c : C) : 0 ≤ coordinatePopulation B (N c) (v c) := by
    unfold coordinatePopulation
    positivity
  have hlo : (1-u)^Fintype.card C ≤ population B N v := by
    unfold population
    calc
      _ = ∏ _c : C,(1-u) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by linarith) (fun c _ => (hfactor c).1)
  have hup : population B N v ≤ (1+u)^Fintype.card C := by
    unfold population
    calc
      _ ≤ ∏ _c : C,(1+u) := Finset.prod_le_prod (fun c _ => hpos c) (fun c _ => (hfactor c).2)
      _ = _ := by simp
  have hbern := one_add_mul_le_pow (show (-2:ℚ) ≤ -u by linarith) (Fintype.card C)
  have hreverse := reverse_bernoulli u hu (Fintype.card C)
  have hpower : 0 ≤ (1+u)^Fintype.card C := by positivity
  constructor
  · have hh : 1-(Fintype.card C:ℚ)*u ≤ (1-u)^Fintype.card C := by
      simpa only [mul_neg,sub_eq_add_neg] using hbern
    linarith
  · nlinarith

end ContingencyTables.CompanionBinPopulation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_change (x y : ℝ) : |intervalCost x-intervalCost y| ≤ |x-y| := by
  have hsub (x y : ℝ) : intervalCost x ≤ intervalCost y+|x-y| := by
    unfold intervalCost
    apply max_le
    · linarith [le_max_left (0:ℝ) (max (-y) (y-1)),abs_nonneg (x-y)]
    · apply max_le
      · have hh : -y ≤ max 0 (max (-y) (y-1)) :=
          (le_max_left _ _).trans (le_max_right _ _)
        linarith [neg_le_abs (x-y)]
      · have hh : y-1 ≤ max 0 (max (-y) (y-1)) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith [le_abs_self (x-y)]
  apply abs_le.mpr
  constructor
  · have hh := hsub y x
    rw [abs_sub_comm y x] at hh
    linarith
  · linarith [hsub x y]

lemma tree_card_le (A : Instance I J) : Fintype.card (TreeCell A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer free assignments use the original scaled affine tree values -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_div (x b : ℝ) (hb : 0 < b) :
    intervalCost (x/b)=max 0 (max (-x) (x-b))/b := by
  unfold intervalCost
  have he : x/b-1=(x-b)/b := by field_simp [hb.ne']
  rw [he,← neg_div, max_div_div_right hb.le]
  simpa only [zero_div] using max_div_div_right hb.le (0:ℝ) (max (-x) (x-b))

lemma tree_sum_eq (A : Instance I J) (F : I×J → ℝ) :
    (∑ t : TreeCell A.T,F t.val)=
      ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then F (i,j) else 0 := by
  let p : I×J → Prop := fun a => A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _ = ∑ a ∈ Finset.univ.filter p,F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp) F).symm
    _ = ∑ a : I×J,if p a then F a else 0 := Finset.sum_filter _ _
    _ = _ := by rw [Fintype.sum_prod_type]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rowCounts_bounds (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (i : I) (j : J) (hs : A.small i j=true) :
    0 ≤ rowCounts A z i j ∧ rowCounts A z i j ≤ A.b i j := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have hh : smallX A.small z i j ≤ A.b i j := by
    simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  change (smallX A.small z i j:ℤ) ≤ (A.b i j:ℤ)
  exact_mod_cast hh

lemma columnCounts_bounds (A : Instance I J) (z : View A → ℕ) (i : I) (j : J) :
    0 ≤ columnCounts A z i j ∧ columnCounts A z i j ≤ A.b i j := by
  unfold columnCounts
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Nat.sub_le (A.b i j) (smallY A.small z i j)⟩

lemma integerCube_zero (A : Instance I J) (B : ℝ) : integerCube A B (zeroAssignment A)=0 := by
  funext a
  simp only [integerCube,zeroAssignment,Nat.cast_zero,mul_zero,zero_div,Pi.zero_apply]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binWidth_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < binWidth A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold binWidth
  positivity

lemma height_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < height A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold height
  positivity

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleMixing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative mixing for the companion's actual evaluator grid -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K)=K^q := by
  have hc : Fintype.card (Set.Icc (0:ℤ) ((K:ℤ)-1))=K := by
    have hh := Int.card_fintype_Icc_of_le 0 ((K:ℤ)-1)
      (show (0:ℤ) ≤ (K:ℤ)-1+1 by omega)
    omega
  simp only [Grid,Fintype.card_fun,Fintype.card_fin,hc]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma pull_integerPoint (A : Instance I J) (C : ℝ) (f : FreeIndex A.small A.T A.b) :
    pull A (integerPoint A C f)=integerCube A (binWidth A C) f := by
  funext t
  simp only [pull,integerPoint,Equiv.apply_symm_apply]

lemma ownFiber_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) :
    0 < (integerFiber A K hK (integerBin A K hK f)).card := by
  apply Finset.card_pos.mpr
  exact ⟨f,by simp [integerFiber]⟩

lemma assignmentCount_positive (A : Instance I J) : 0 < assignmentCount A := by
  let : Nonempty (FreeIndex A.small A.T A.b) := ⟨fun _ => 0⟩
  exact Fintype.card_pos


end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer bins have the manuscript's Cartesian populations -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem integerFiber_card (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).card=
      ∏ t : FreeCell A.small A.T,(FairBits.fiber K (freeRange A t) (naturalBin A v t)).card := by
  let : DecidableEq (FreeCell A.small A.T) := Classical.decEq _
  calc
    _ = Fintype.card {f // f∈integerFiber A K hK v} := (Fintype.card_coe _).symm
    _ = _ := Fintype.card_congr (integerFiberEquiv A K hK v)
    _ = _ := CompanionBinPopulation.assignment_card K (freeRange A) (naturalBin A v)

theorem integerFiber_nonempty (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).Nonempty := by
  have hpop (t : FreeCell A.small A.T) :
      (FairBits.fiber K (freeRange A t) (naturalBin A v t)).Nonempty := by
    apply CompanionBinPopulation.coordinate_nonempty K (freeRange A t) A.d _ hK A.hd
    · have hh := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega
    · exact naturalBin_lt A v t
  let x : CompanionBinPopulation.Assignments K (freeRange A) (naturalBin A v) :=
    fun t => ⟨(hpop t).choose,(hpop t).choose_spec⟩
  exact ⟨((integerFiberEquiv A K hK v).symm x).val,
    ((integerFiberEquiv A K hK v).symm x).property⟩

lemma assignmentCount_eq_prod (A : Instance I J) :
    assignmentCount A=∏ t : FreeCell A.small A.T,freeRange A t := by
  simp only [assignmentCount,FreeIndex,Fintype.card_pi,Fintype.card_fin,freeRange]

theorem population_eq_integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    CompanionBinPopulation.population K (freeRange A) (naturalBin A v)=
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A := by
  rw [CompanionBinPopulation.population_eq_card,CompanionBinPopulation.assignment_card,
    ←integerFiber_card A K hK,
    assignmentCount_eq_prod]
  simp only [dimension,Nat.cast_prod]

theorem actual_population_bounds (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ≤ 2 := by
  have hh := CompanionBinPopulation.population_bounds K A.d (freeRange A) (naturalBin A v)
    hK A.hd (ForestScaledPenalty.free_card_le A)
    (by
      intro t
      have hb := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega)
    (naturalBin_lt A v)
  simpa only [population_eq_integerFiber A K hK] using hh

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleJointLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of the actual bin-then-integer sampling law -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma integerPoint_distance (A : Instance I J) (C : ℝ) (K : ℕ) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    ∀ i,|integerPoint A C f i-realCorner (integerBin A K hK f) i| ≤ 1 := by
  intro i
  let t := index A i
  let N := freeRange A t
  let x := (f t).val
  have hq : (0:ℚ) ≤ (K:ℚ)*x/N := by positivity
  have hlo : (FairBits.scale K N x:ℚ) ≤ (K:ℚ)*x/N := Nat.floor_le hq
  have hhi : (K:ℚ)*x/N < (FairBits.scale K N x:ℚ)+1 := Nat.lt_floor_add_one _
  have hloR : (FairBits.scale K N x:ℝ) ≤ (K:ℝ)*x/N := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR : (K:ℝ)*x/N < (FairBits.scale K N x:ℝ)+1 := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr hhi
  have hN : (N:ℝ)=(A.b t.val.1 t.val.2:ℝ)+1 := by simp [N,freeRange]
  change |binWidth A C*(f t).val/((A.b t.val.1 t.val.2:ℝ)+1)-
    (FairBits.scale K N (f t).val:ℝ)| ≤ 1
  rw [←hB,←hN]
  change |(K:ℝ)*x/N-(FairBits.scale K N x:ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinIntervals
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer intervals inside the companion evaluator bins -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem exactBinLaw_mass (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (f : FreeIndex A.small A.T A.b) :
    (exactBinLaw A K hK hW v).mass f=
      if integerBin A K hK f=v then 1/((integerFiber A K hK v).card:ℚ) else 0 := by
  let : ∀ i : Fin (dimension A),Nonempty (Fin (binSize A K v i)) :=
    fun i => ⟨⟨0,binSize_positive A K hK hW v i⟩⟩
  let : Nonempty {f // f∈integerFiber A K hK v} :=
    ⟨⟨(integerFiber_nonempty A K hK hW v).choose,(integerFiber_nonempty A K hK hW v).choose_spec⟩⟩
  have hi (i : Fin (dimension A)) :
      FairBits.uniformIntLaw (binSize A K v i) (binSize_positive A K hK hW v i)=
        uniformLaw (α := Fin (binSize A K v i)) := by
    apply RationalLaw.ext
    funext x
    simp only [FairBits.uniformIntLaw,uniformLaw,uniformMass,Fintype.card_fin]
  unfold exactBinLaw
  simp_rw [hi]
  rw [pi_uniformLaw]
  change (mapLaw (uniformLaw (α := (i : Fin (dimension A)) → Fin (binSize A K v i)))
    (fun x => (binOffsetsEquiv A K hK v x).val)).mass f=_
  rw [←FairBits.map_equiv (binOffsetsEquiv A K hK v),FairBits.uniform_equiv]
  change (∑ x : {g // g∈integerFiber A K hK v},
    if x.val=f then (1:ℚ)/Fintype.card {g // g∈integerFiber A K hK v} else 0)=_
  rw [Fintype.card_coe]
  by_cases hf : integerBin A K hK f=v
  · rw [ite_eq_left hf]
    let g : {g // g∈integerFiber A K hK v} := ⟨f,by simp only [integerFiber,Finset.mem_filter,
      Finset.mem_univ,true_and,hf]⟩
    have he (x : {g // g∈integerFiber A K hK v}) : x.val=f ↔ x=g := by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp_rw [he]
    simp
  · rw [ite_eq_right hf]
    apply Finset.sum_eq_zero
    intro x _
    have hxf : x.val≠f := by
      intro he
      have hx := (Finset.mem_filter.mp x.property).2
      rw [he] at hx
      exact hf hx
    simp only [hxf,ite_false]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma expectation_bounds (p : RationalLaw X) (g : X → ℝ) (L U : ℝ)
    (hg : ∀ x,L ≤ g x ∧ g x ≤ U) : L ≤ expectation p g ∧ expectation p g ≤ U := by
  have htotal : ∑ x,(p.mass x:ℝ)=1 := by exact_mod_cast p.total
  unfold expectation
  constructor
  · calc
      L = ∑ x,(p.mass x:ℝ)*L := by rw [←Finset.sum_mul,htotal,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).1 (by exact_mod_cast p.nonnegative x))
  · calc
      _ ≤ ∑ x,(p.mass x:ℝ)*U := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).2 (by exact_mod_cast p.nonnegative x))
      _ = U := by rw [←Finset.sum_mul,htotal,one_mul]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

theorem denominator_eq (A : Instance I J) :
    CompanionFactorialApplication.denominator A=
      InitialTransversals.denominator (fun s : SmallCell A => A.b s.val.1 s.val.2) := by
  unfold CompanionFactorialApplication.denominator TwoLiftStates.denominator InitialTransversals.denominator
  simp_rw [label_width]

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteProductAccuracy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative accuracy of the finite product used by the weight oracle -/

namespace ContingencyTables.FiniteProductAccuracy

open scoped BigOperators Classical

variable {J : Type*} [Fintype J]

lemma relative_log (x y delta : ℝ) (hy : 0 < y) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4)
    (herr : |x-y| ≤ delta*y) : 0 < x ∧ |Real.log (x/y)| ≤ 4*delta := by
  have hh := abs_le.mp herr
  have hx : (1-delta)*y ≤ x ∧ x ≤ (1+delta)*y := by constructor <;> nlinarith
  have h1 : (1-delta)*(1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ (1+delta)*1 := by constructor <;> nlinarith
  have hp := AnnealingMultipliers.relative_ratio hy (by norm_num : (0:ℝ)<1) hd0 hd hx h1
  refine ⟨AnnealingMultipliers.empirical_positive hy hd hx.1,?_⟩
  simpa only [mul_one,one_mul] using hp.2.2.2

lemma product_log (x y : J → ℝ) (hy : ∀ j,0 < y j) (delta : ℝ)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1/4) (herr : ∀ j,|x j-y j| ≤ delta*y j) :
    0 < ∏ j,x j ∧ |Real.log ((∏ j,x j)/(∏ j,y j))| ≤ 4*(Fintype.card J:ℝ)*delta := by
  have hstep := fun j => relative_log (x j) (y j) delta (hy j) hd0 hd (herr j)
  refine ⟨Finset.prod_pos (fun j _ => (hstep j).1),?_⟩
  rw [←Finset.prod_div_distrib,Real.log_prod (fun j _ => div_ne_zero (hstep j).1.ne' (hy j).ne')]
  calc
    _ ≤ ∑ j,|Real.log (x j/y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J,4*delta := Finset.sum_le_sum (fun j _ => (hstep j).2)
    _ = _ := by simp; ring

/-- The source has j+1 factors, each observed to the same tolerance.
This scalar budget is sufficient for its requested relative interval. -/
theorem product_relative (x y : J → ℝ) (hy : ∀ j,0 < y j) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (herr : ∀ j,|x j-y j| ≤ (epsilon/(200*(Fintype.card J:ℝ)))*y j)
    (hcard : 0 < Fintype.card J) :
    (1-epsilon/4)*(∏ j,y j) ≤ ∏ j,x j ∧
      (∏ j,x j) ≤ (1+epsilon/4)*(∏ j,y j) := by
  have hc : (0:ℝ) < Fintype.card J := by exact_mod_cast hcard
  have hc1 : (1:ℝ) ≤ Fintype.card J := by exact_mod_cast hcard
  have hd0 : 0 ≤ epsilon/(200*(Fintype.card J:ℝ)) := by positivity
  have hd : epsilon/(200*(Fintype.card J:ℝ)) ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ)<200*(Fintype.card J:ℝ))]
    linarith
  have hh := product_log x y hy _ hd0 hd herr
  have hb : 4*(Fintype.card J:ℝ)*(epsilon/(200*(Fintype.card J:ℝ)))=epsilon/50 := by
    field_simp [hc.ne']
    ring
  have ht := Finset.prod_pos (s := Finset.univ) (fun j _ => hy j)
  have hr := CompanionReferenceAccuracy.relative_of_log_error epsilon
    ((∏ j,x j)/(∏ j,y j)) he0 he1 (div_pos hh.1 ht) (hh.2.trans_eq hb)
  exact ⟨(le_div_iff₀ ht).mp hr.1,(div_le_iff₀ ht).mp hr.2⟩

end ContingencyTables.FiniteProductAccuracy

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma innerTolerance_pos (epsilon : ℚ) (j : ℕ) (he : 0 < epsilon) :
    0 < innerTolerance epsilon j := by unfold innerTolerance; positivity

lemma innerTolerance_lt_one (epsilon : ℚ) (j : ℕ) (he : epsilon < 1) :
    innerTolerance epsilon j < 1 := by
  unfold innerTolerance
  rw [div_lt_iff₀ (by positivity : (0:ℚ)<200*(j+1))]
  have hj : (0:ℚ) ≤ j := Nat.cast_nonneg _
  nlinarith

end

end ContingencyTables.CompanionOracleDensity

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWeightOracle
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma factorialRatio_cast (A : Instance I J) (S : Set (Labels A×Bool)) :
    (factorialRatio A S:ℝ)=
      FactorialSignatures.factorialProduct (profile A S)/CompanionFactorialApplication.denominator A := by
  simp only [factorialRatio,factorialNumerator,factorialDenominator,Rat.cast_div,Rat.cast_prod,
    Rat.cast_natCast,Nat.cast_prod,FactorialSignatures.factorialProduct,CompanionFactorialApplication.denominator,
    TwoLiftStates.denominator,label_width]

end

end ContingencyTables.CompanionWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

theorem selected_nonroot (T : SimpleGraph V) (S : Selection T) (hT : T.IsAcyclic)
    {u v a : V} (ht : T.Adj u v) (ha : cut T u v (S.root u) a=true) : a≠S.root a := by
  intro he
  have hp := away_properties T hT ht (S.root u) (S.reachable u).symm
  have hreach : (T.deleteEdges {s(u,v)}).Reachable (away T u v (S.root u)) a := by
    simpa only [cut,side,decide_eq_true_eq] using ha
  have hcomp := hp.1.trans (hreach.mono (T.deleteEdges_le {s(u,v)}))
  have hsame : S.root a=S.root u :=
    (S.constant hcomp).symm.trans (S.idempotent u)
  have hae : a=S.root u := he.trans hsame
  have hbad : cut T u v (S.root u) (S.root u)=true := by simpa only [hae] using ha
  exact Bool.false_ne_true (hp.2.1.symm.trans hbad)

variable {I J : Type*}

lemma treeCut_nonroot (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) (v : I⊕J) (hv : treeCut T S t v=true) : v≠S.root v :=
  selected_nonroot T S hT t.property hv

lemma sign_abs_le_one (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : |sign T S t a|≤1 := by
  unfold sign
  cases treeCut T S t (.inl a.1) <;> cases treeCut T S t (.inr a.2) <;>
    norm_num [indicator]

lemma other_tree_sign_zero (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) (ha : T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) :
    sign T S t a=0 := by
  have hh := side_eq_of_tree_edge T (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (away T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1))) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAffine
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut coefficients for an explicitly selected forest root

The same signed cut calculation applies to the executed root selector.
In particular, coefficient size and the maximum-forest capacity bound
do not depend on a classical choice of cut representative.
-/

namespace ContingencyTables.RootedAffine

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedCut GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

lemma coefficient_abs_le_one (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : |coefficient A S t a|≤1 := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,sign_abs_self A.T S A.hT,div_one]
    exact sign_abs_le_one A.T S t a
  · norm_num

lemma capacity_le_of_coefficient_ne_zero (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (ha : coefficient A S t a≠0) :
    A.b a.1 a.2≤A.b t.val.1 t.val.2 := by
  have hf : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2) := by
    by_contra hn
    exact ha (by simp only [coefficient,hn,ite_false])
  have hcross : treeCut A.T S t (.inl a.1)≠treeCut A.T S t (.inr a.2) := by
    intro he
    apply ha
    simp [coefficient,hf,sign,he]
  have h := crossing_free_edge_le (cellGraph A.small) A.T (capacity A.b)
    A.hTG A.hT A.hmax (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (by simpa using t.property)
    (away A.T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)))
    (show (cellGraph A.small).Adj (.inl a.1) (.inr a.2) from hf.1) hf.2 hcross
  simpa only [capacity_cell] using h

theorem normalized_coefficient_bound (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (B : ℝ) (hB : 0<B) :
    |coefficient A S t a*((A.b a.1 a.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)|≤2/B := by
  have hb : (1:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
  by_cases ha : coefficient A S t a=0
  · simp only [ha,zero_mul,zero_div,abs_zero]
    positivity
  have hcap : (A.b a.1 a.2:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast capacity_le_of_coefficient_ne_zero A S t a ha
  rw [abs_div,abs_div,abs_mul,abs_of_pos hB,
    abs_of_pos (by linarith : (0:ℝ)<A.b t.val.1 t.val.2),
    abs_of_nonneg (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<A.b t.val.1 t.val.2)).mpr
  rw [div_le_iff₀ hB]
  have hh := mul_le_mul_of_nonneg_right (coefficient_abs_le_one A S t a)
    (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)
  field_simp [hB.ne']
  nlinarith

theorem affine_of_nonroot_equations (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q z : I → J → ℝ)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) →
      rowDifference A.small x z (fun i j => (A.X i j:ℝ)) i=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) →
      columnDifference A.small q z (fun i j => (A.X i j:ℝ)) j=0) :
    z t.val.1 t.val.2=affineTree A S t x q (fun a => z a.1 a.2) := by
  let f : I×J → ℝ := fun a => cutTerm A.small
    (fun i => treeCut A.T S t (.inl i)) (fun j => treeCut A.T S t (.inr j))
    x q z (fun i j => (A.X i j:ℝ)) a.1 a.2
  have hsum : (∑ a,f a)=0 := by
    rw [Fintype.sum_prod_type]
    exact cut_sum_zero A.small _ _ x q z _
      (fun i hi => hr i (treeCut_nonroot A.T S A.hT t (.inl i) hi))
      (fun j hj => hc j (treeCut_nonroot A.T S A.hT t (.inr j) hj))
  have hterm (a : I×J) : f a=
      (if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)+
      (if A.small a.1 a.2 then
        indicator (treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          indicator (treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0)-
      sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2) := by
    by_cases he : a=t.val
    · subst a
      have hs : A.small t.val.1 t.val.2=false := A.hTG t.property
      simp only [f,cutTerm,hs,Bool.false_eq_true,ite_false,ite_true, if_true,coefficient,t.property,
        not_true_eq_false,and_false,sign,mul_zero,zero_mul,add_zero,sub_zero]
    · by_cases hs : A.small a.1 a.2=true
      · simp [f,cutTerm,hs,he,coefficient]
      · have hs' : A.small a.1 a.2=false := Bool.eq_false_iff.mpr hs
        by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
        · have hz := other_tree_sign_zero A.T S t a ht he
          simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_true_eq_false,and_false,zero_add,mul_zero,zero_mul,sub_zero]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=0
          rw [hz,zero_mul]
        · simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_false_eq_true,and_self,ite_true, if_true,zero_add,zero_sub]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=
            -(sign A.T S t t.val*(-sign A.T S t a/sign A.T S t t.val)*
              (z a.1 a.2-A.X a.1 a.2))
          field_simp [sign_self_ne_zero A.T S A.hT t]
  simp_rw [hterm] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  have hsingle : (∑ a : I×J,
      if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)=
      sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2) := by simp
  rw [hsingle] at hsum
  change sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2)+
    smallContribution A S t x q-
    (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=0 at hsum
  have hprod : (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=
      sign A.T S t t.val*((∑ a : I×J,coefficient A S t a*z a.1 a.2)-
        ∑ a : I×J,coefficient A S t a*(A.X a.1 a.2:ℝ)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hprod] at hsum
  unfold affineTree AffinePenalty.affineValue offset
  apply mul_left_cancel₀ (sign_self_ne_zero A.T S A.hT t)
  rw [mul_add,mul_sub,mul_sub,←mul_div_assoc,
    mul_div_cancel_left₀ _ (sign_self_ne_zero A.T S A.hT t)]
  nlinarith [hsum]

end ContingencyTables.RootedAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The cut-defined coefficients evaluate the actual integral solution
for this root convention, including every unbalanced small profile. -/
theorem solved_eq_affine (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A S x q free t.val.1 t.val.2:ℝ)=
      affineTree A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A S x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A S t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A S x q free i hi
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self]) (by
      intro j hj
      have hc := column_completed_sum A S x q free j hj
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self])
  have hz : z t.val.1 t.val.2=(solved A S x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true, if_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.RootedPhysicalCompletion

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)
open ForestRootPenalty (residualDemand smallDemand)

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma componentSum_decidable (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) :
    (∑ v,@ite ℤ (S.root v=a) (Classical.propDecidable _) (d v) 0)=
      ∑ v,if S.root v=a then d v else 0 := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : S.root v=a <;> simp only [h,ite_true, if_true,ite_false]

lemma root_eq_large (A : Instance I J) (S : Selection A.T) (i : I) (j : J)
    (hs : A.small i j=false) : S.root (.inl i)=S.root (.inr j) := by
  have hcap : ∀ e∈(ForestCapacity.cellGraph A.small).edgeSet,0<ForestCapacity.capacity A.b e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hg : (ForestCapacity.cellGraph A.small).Adj u v := by simpa using he
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim hg
      | inr j => exact (A.hlarge i j hg).2
    | inr j =>
      cases v with
      | inl i => exact (A.hlarge i j hg).2
      | inr j' => exact False.elim hg
  have hspans := MaximumForest.maximum_spans (ForestCapacity.cellGraph A.small) A.T
    (ForestCapacity.capacity A.b) A.hTG A.hT A.hmax hcap
  apply S.constant
  rw [hspans]
  exact (show (ForestCapacity.cellGraph A.small).Adj (.inl i) (.inr j) from hs).reachable

lemma componentTotal_residual (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a=
      componentTotal A S (smallDemand A.small A.X x q) a := by
  let R : I → ℤ := fun i => if S.root (.inl i)=a then 1 else 0
  let C : J → ℤ := fun j => if S.root (.inr j)=a then 1 else 0
  have hrow (i : I) : R i*rowResidual A.small A.T A.r x free i=
      ∑ j,R i*(A.X i j-fixedRow A.small A.T x free i j) := by
    rw [rowResidual,←A.hXr i,←Finset.sum_sub_distrib,Finset.mul_sum]
  have hcol (j : J) : C j*(-columnResidual A.small A.T A.c q free j)=
      ∑ i,C j*(fixedColumn A.small A.T q free i j-A.X i j) := by
    rw [columnResidual,←A.hXc j,neg_sub,←Finset.sum_sub_distrib,Finset.mul_sum]
  unfold componentTotal residualDemand smallDemand
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  change (∑ i,R i*rowResidual A.small A.T A.r x free i)+
      (∑ j,C j*(-columnResidual A.small A.T A.c q free j))=
    (∑ i,R i*(∑ j,if A.small i j then A.X i j-x i j else 0))+
      ∑ j,C j*(∑ i,if A.small i j then q i j-A.X i j else 0)
  simp_rw [hrow,hcol,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => C j*(fixedColumn A.small A.T q free i j-A.X i j)),
    Finset.sum_comm (f := fun j i => C j*(if A.small i j then q i j-A.X i j else 0)),
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : A.small i j=true
  · simp [fixedRow,fixedColumn,hs]
  · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
    have he : R i=C j := by unfold R C; rw [root_eq_large A S i j hs']
    rw [he]
    simp only [fixedRow,fixedColumn,hs',Bool.false_eq_true,ite_false]
    ring

lemma table_row_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (i : I) :
    (∑ j,table A.T S r c i j)=
      r i-∑ v,if S.root v=Sum.inl i then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inl i)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact A.hTG h
  simp only [hz,zero_add,Sum.elim_inl] at hs
  rw [componentSum_decidable] at hs
  simpa only [table] using hs

lemma table_column_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (j : J) :
    -(∑ i,table A.T S r c i j)=
      -c j-∑ v,if S.root v=Sum.inr j then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inr j)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact A.hTG h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table A.T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simp only [hz,add_zero,Sum.elim_inr,hskew] at hs
  rw [componentSum_decidable] at hs
  exact hs

theorem signedResidual_eq_small (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    signedResidual A S x q free a=-componentTotal A S (smallDemand A.small A.X x q) a := by
  suffices he : signedResidual A S x q free a=
      -componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a by
    rw [he,componentTotal_residual]
  have htotal : ∀ d : I⊕J → ℤ,
      (∑ v,if S.root v=a then d v else 0)=componentTotal A S d a := by
    intro d
    simp [componentTotal,ite_mul]
  cases a with
  | inl i =>
    simp only [signedResidual,Sum.elim_inl]
    simp_rw [row_pointwise]
    rw [Finset.sum_add_distrib]
    have hr := table_row_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) i
    change (∑ j,solved A S x q free i j)=_ at hr
    rw [hr,htotal]
    unfold residualDemand rowResidual columnResidual
    ring
  | inr j =>
    simp only [signedResidual,Sum.elim_inr]
    simp_rw [column_pointwise]
    rw [Finset.sum_add_distrib]
    have hc := table_column_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) j
    change -(∑ i,solved A S x q free i j)=_ at hc
    have hc' : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j+
        ∑ v,if S.root v=Sum.inr j then
          Sum.elim (rowResidual A.small A.T A.r x free)
            (fun j => -columnResidual A.small A.T A.c q free j) v else 0 := by linarith
    rw [hc',htotal]
    unfold residualDemand rowResidual columnResidual
    ring

theorem signedResidual_independent (A : Instance I J) (S : Selection A.T)
    (x q free free' : I → J → ℤ) :
    signedResidual A S x q free=signedResidual A S x q free' := by
  funext a
  rw [signedResidual_eq_small,signedResidual_eq_small]

lemma abs_actualDeviation_solved (A : Instance I J) (S : Selection A.T)
    (x y free : I → J → ℕ) (a : I⊕J) :
    |ForestLiteralCount.actualDeviation A.small A.T A.b x y free A.r A.c
      (solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
        (fun i j => (free i j:ℤ))) a|=
    |(signedResidual A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
      (fun i j => (free i j:ℤ)) a:ℝ)| := by
  cases a with
  | inl i =>
    simp only [ForestLiteralCount.actualDeviation,signedResidual,Sum.elim_inl,completed,
      ForestLiteralCount.largeValue]
    push_cast
    rfl
  | inr j =>
    simp only [ForestLiteralCount.actualDeviation,signedResidual,Sum.elim_inr,completed,
      ForestLiteralCount.largeValue]
    push_cast
    rw [abs_neg]

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative intervalCost_change
  free_card_le tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem penalty_change (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (x q : I → J → ℤ)
    (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ f,|v f-w f|≤ r) :
    |penalty A S C B x q v-penalty A S C B x q w|≤(2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A S B x q v t)-intervalCost (scaledTree A S B x q w t)|≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A S t x q)
      (normalizedCoefficient A S B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A S t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ)≤2/B)) hr)
  have he : penalty A S C B x q v-penalty A S C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A S B x q v t)-
        intervalCost (scaledTree A S B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A S B x q v t)-
      intervalCost (scaledTree A S B x q w t)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _=C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _=_ := by ring

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root geometric density is the literal completion weight -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedPhysicalCompletion RootedRootPenalty
open ForestScaledPenalty (integerCube intervalCost intervalCost_div tree_sum_eq)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma free_coefficient_sum (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (F : I×J → ℝ) :
    (∑ f : FreeCell A.small A.T,coefficient A S t f.val*F f.val)=
      ∑ a : I×J,coefficient A S t a*F a := by
  let p : I×J → Prop := fun a => A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _=∑ a ∈ Finset.univ.filter p,coefficient A S t a*F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp)
        (fun a => coefficient A S t a*F a)).symm
    _=_ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hp : ¬p a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using ha
      change ¬(A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) at hp
      simp only [coefficient,hp,ite_false,zero_mul]

theorem scaledTree_integer (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (x q : I → J → ℤ) (f : FreeIndex A.small A.T A.b) (t : TreeCell A.T) :
    scaledTree A S B x q (integerCube A B f) t=
      (solved A S x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
        t.val.1 t.val.2:ℝ)/(A.b t.val.1 t.val.2:ℝ) := by
  let F : I×J → ℝ := fun a => (freeTable A.small A.T A.b f a.1 a.2:ℝ)
  have hterm (a : FreeCell A.small A.T) :
      normalizedCoefficient A S B t a*integerCube A B f a=
        coefficient A S t a.val*F a.val/(A.b t.val.1 t.val.2:ℝ) := by
    have hN : (A.b a.val.1 a.val.2:ℝ)+1≠0 := by positivity
    have hbt : (A.b t.val.1 t.val.2:ℝ)≠0 := by
      exact_mod_cast (Nat.ne_of_gt (A.hlarge _ _ (A.hTG t.property)).2)
    have hF : F a.val=(f a).val := by simp [F,freeTable,a.property]
    rw [hF]
    unfold normalizedCoefficient integerCube
    field_simp [hB.ne',hN,hbt]
  unfold scaledTree AffinePenalty.affineValue normalizedOffset
  simp_rw [hterm]
  rw [←Finset.sum_div,free_coefficient_sum,←add_div]
  have hh := solved_eq_affine A S t x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
  unfold affineTree AffinePenalty.affineValue at hh
  apply congrArg (fun z : ℝ => z/(A.b t.val.1 t.val.2:ℝ))
  simpa only [F,Int.cast_natCast] using hh.symm

theorem rootConstant_eq_assignment (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) :
    rootConstant A S x q=
      ∑ a,if RootedPenalty.rootFlag S a then |(signedResidual A S x q free a:ℝ)| else 0 := by
  have hh := signedResidual_independent A S x q free 0
  unfold rootConstant
  apply Finset.sum_congr rfl
  intro a _
  rw [hh]

theorem penalty_at_integer (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hB : 0<B) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    penalty A S C B (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))
      (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))
      (integerCube A B f)=C*RootedLiteralCount.actualPenalty A S
        (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
        (freeTable A.small A.T A.b f)
        (solved A S (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))
          (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))
          (fun i j => (freeTable A.small A.T A.b f i j:ℤ))) := by
  let x := ForestCountIdentification.smallX A.small z
  let y := ForestCountIdentification.smallY A.small z
  let free := freeTable A.small A.T A.b f
  let tree := solved A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))
    (fun i j => (free i j:ℤ))
  have hroot : rootConstant A S (fun i j => (x i j:ℤ)) (fun i j => ((A.b i j-y i j:ℕ):ℤ))=
      ∑ a,if RootedPenalty.rootFlag S a then
        |ForestLiteralCount.actualDeviation A.small A.T A.b x y free A.r A.c tree a| else 0 := by
    rw [rootConstant_eq_assignment A S _ _ (fun i j => (free i j:ℤ))]
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_actualDeviation_solved]
  have htree : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (fun i j => (x i j:ℤ))
      (fun i j => ((A.b i j-y i j:ℕ):ℤ)) (integerCube A B f) t))=
      ∑ i,∑ j,if A.T.Adj (.inl i) (.inr j) then
        max 0 (max (-(tree i j:ℝ)) ((tree i j:ℝ)-A.b i j))/(A.b i j:ℝ) else 0 := by
    calc
      _=∑ t : TreeCell A.T,
          max 0 (max (-(tree t.val.1 t.val.2:ℝ)) ((tree t.val.1 t.val.2:ℝ)-A.b t.val.1 t.val.2))/
            (A.b t.val.1 t.val.2:ℝ) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [scaledTree_integer A S B hB]
        exact intervalCost_div _ _ (by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2)
      _=_ := tree_sum_eq A (fun a =>
        max 0 (max (-(tree a.1 a.2:ℝ)) ((tree a.1 a.2:ℝ)-A.b a.1 a.2))/(A.b a.1 a.2:ℝ))
  unfold penalty
  change C*(rootConstant A S (fun i j => (x i j:ℤ))
    (fun i j => ((A.b i j-y i j:ℕ):ℤ))+_)=_
  rw [hroot,htree]
  rfl

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source height bounds the entire selected-root density cube -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedRootPenalty RootedPhysicalCompletion BalancedBox
open ForestScaledPenalty (rowCounts columnCounts rowCounts_bounds columnCounts_bounds
  intervalCost intervalCost_div integerCube integerCube_zero zeroAssignment tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootConstant_bound (A : Instance I J) (S : Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    rootConstant A S (rowCounts A z) (columnCounts A z)≤2*(A.d:ℝ)*A.W := by
  let d := ForestRootPenalty.smallDemand A.small A.X (rowCounts A z) (columnCounts A z)
  have he (a : I⊕J) : (signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)=
      -(∑ v,if S.root v=a then (d v:ℝ) else 0) := by
    rw [signedResidual_eq_small]
    unfold componentTotal
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : S.root v=a <;> simp [hv,d]
  have hrow (i : I) : |((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|≤
      ∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |A.X i j-rowCounts A z i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(rowCounts_bounds A z hz i j hs).1,
          (rowCounts_bounds A z hz i j hs).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hcol (j : J) : |((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|≤
      ∑ i,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |columnCounts A z i j-A.X i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(columnCounts_bounds A z i j).1,
          (columnCounts_bounds A z i j).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hdemand : (∑ a,|(d a:ℝ)|)≤2*∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ i,|((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|)+
      (∑ j,|((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|)≤_
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
    rw [Finset.sum_comm] at hc
    linarith
  have hsmall : (∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0)≤(A.d:ℝ)*A.W := by
    calc
      _≤∑ _i : I,∑ _j : J,(A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        cases hs : A.small i j
        · simp only [Bool.false_eq_true,ite_false]
          positivity
        · simp only [ite_true, if_true]
          exact_mod_cast (A.hsmall i j hs).le
      _=(Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  unfold rootConstant
  calc
    _≤∑ a,|(signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _=∑ a,|∑ v,if S.root v=a then (d v:ℝ) else 0| := by simp_rw [he,abs_neg]
    _≤∑ v,|(d v:ℝ)| := ForestRootPenalty.sum_abs_componentTotal S.root (fun v => (d v:ℝ))
    _≤_ := hdemand.trans (by linarith)

lemma zero_tree_bound (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (z : View A → ℕ) (hz : InBox (bounds A) z) (t : TreeCell A.T) :
    intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t)≤10*(A.d:ℝ) := by
  have hzero : (fun i j => (freeTable A.small A.T A.b (zeroAssignment A) i j:ℤ))=0 := by
    funext i j
    unfold freeTable zeroAssignment
    split_ifs <;> rfl
  have hinterval := RootedIntervals.solved_in_intervals A S
    (rowCounts A z) (columnCounts A z) 0
    (by intro i j hs; exact ⟨rowCounts_bounds A z hz i j hs,columnCounts_bounds A z i j⟩)
    (by intro i j _ _; exact ⟨le_rfl,Nat.cast_nonneg _⟩)
    t.val.1 t.val.2 t.property
  rw [←integerCube_zero A B,scaledTree_integer A S B hB,hzero,intervalCost_div]
  · have hb : (0:ℝ)<A.b t.val.1 t.val.2 := by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
    rw [div_le_iff₀ hb]
    have hlo : -(10*(A.d:ℝ)*A.b t.val.1 t.val.2)≤
        (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) := by
      exact_mod_cast hinterval.1
    have hup : (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ)≤
        10*(A.d:ℝ)*A.b t.val.1 t.val.2 := by exact_mod_cast hinterval.2
    apply max_le
    · positivity
    · apply max_le <;> linarith
  · exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2

theorem penalty_cube_bound (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (v : FreeCell A.small A.T → ℝ) (hv : ∀ f,0≤ v f ∧ v f≤ B) :
    0≤ penalty A S C B (rowCounts A z) (columnCounts A z) v ∧
      penalty A S C B (rowCounts A z) (columnCounts A z) v≤ C*(10*(A.d:ℝ)^2*((A.W:ℝ)+1)) := by
  have hzero : penalty A S C B (rowCounts A z) (columnCounts A z) 0≤
      C*(2*(A.d:ℝ)*A.W+10*(A.d:ℝ)^2) := by
    unfold penalty
    apply mul_le_mul_of_nonneg_left _ hC
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => zero_tree_bound A S B hB z hz t)
    have ht : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t))≤
        10*(A.d:ℝ)^2 := by
      calc
        _≤(Fintype.card (TreeCell A.T):ℝ)*(10*(A.d:ℝ)) := by simpa using hsum
        _≤(A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast tree_card_le A) (by positivity)
        _=_ := by ring
    linarith [rootConstant_bound A S z hz]
  have hchange := (le_abs_self _).trans (penalty_change A S C B hC hB
    (rowCounts A z) (columnCounts A z) v 0 B hB.le (by
      intro f
      simpa only [Pi.zero_apply,sub_zero,abs_of_nonneg (hv f).1] using (hv f).2))
  have hcancel : (2*C*(A.d:ℝ)^2/B)*B=2*C*(A.d:ℝ)^2 := div_mul_cancel₀ _ hB.ne'
  rw [hcancel] at hchange
  have hd : (1:ℝ)≤ A.d := by exact_mod_cast A.hd
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  have hscalar : 2*(A.d:ℝ)*A.W+12*(A.d:ℝ)^2≤10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
    have hdd : (A.d:ℝ)≤(A.d:ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hdd (by positivity : (0:ℝ)≤ A.W)
    have hp' := mul_le_mul_of_nonneg_left hW (sq_nonneg (A.d:ℝ))
    nlinarith
  refine ⟨penalty_nonnegative A S C B hC _ _ v,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hscalar hC]

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root evaluator density on its actual finite bin cube -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit
open CompanionOracleDensity (dimension index pull binWidth height)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem D_bounds (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Fin (dimension A) → ℝ) (hv : ∀ i,0≤ v i ∧ v i≤ binWidth A C) :
    0≤ D A S C z v ∧ D A S C z v≤ height A C := by
  have hh := RootedScaledPenalty.penalty_cube_bound A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC) z hz (pull A v)
    (fun f => hv ((index A).symm f))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  unfold height
  ring

theorem D_change (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) : |D A S C z v-D A S C z w|≤ r/8 := by
  have hh := RootedScaledPenalty.penalty_change A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
    (pull A v) (pull A w) r hr (fun f => hvw ((index A).symm f))
  have hd : (A.d:ℝ)≠0 := by exact_mod_cast (show A.d≠0 by have hh := A.hd; omega)
  have he : (2*C*(A.d:ℝ)^2/binWidth A C)*r=r/8 := by
    unfold binWidth
    field_simp [hC.ne',hd]
    ring
  simpa only [D,he] using hh

theorem exponent_change (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) :
    |(a/height A C)*D A S C z v-(a/height A C)*D A S C z w|≤ r/8 := by
  have hH := CompanionOracleDensity.height_positive A C hC
  have hf0 : 0≤ a/height A C := div_nonneg ha hH.le
  have hf1 : a/height A C≤1 := (div_le_one hH).mpr haH
  rw [←mul_sub,abs_mul,abs_of_nonneg hf0]
  exact (mul_le_mul_of_nonneg_left (D_change A S C hC z v w r hr hvw) hf0).trans
    (mul_le_of_le_one_left (by positivity) hf1)

theorem bin_comparison (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (hvw : ∀ i,|v i-w i|≤1) :
    V A S C a z v/4≤ rho A S C a z w ∧ rho A S C a z w≤2*V A S C a z v := by
  have hh := exponent_change A S C a hC ha haH z w v 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using hvw i)
  exact DenseWeights.bin_density_comparison _ _ w v (hh.trans (by norm_num))

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the computed-root completion count

Integer bins and their executable interval draws are the existing
physical bins.  Only their positive density weights change with the
explicit root selector.  All normalizer identities are finite sums.
-/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GridBoundary
open CompanionOracleDensity (dimension index pull binWidth height integerPoint integerBin integerFiber
  assignmentCount ownFiber_positive assignmentCount_positive integerFiber_nonempty)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma gridWeight_positive (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    0<gridWeight A S C a z v := DenseWeights.binWeight_pos _ _ _

lemma density_at_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    rho A S C a z (integerPoint A C f)=
      (2:ℝ)^(-(a*C/height A C)*RootedLiteralCount.actualPenalty A S
        (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
        (freeTable A.small A.T A.b f)
        (RootedPhysicalCompletion.solved A S (ForestScaledPenalty.rowCounts A z)
          (ForestScaledPenalty.columnCounts A z) (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))) := by
  unfold rho DenseWeights.density D
  rw [CompanionOracleDensity.pull_integerPoint]
  have hp := RootedScaledPenalty.penalty_at_integer A S C (binWidth A C)
    (CompanionOracleDensity.binWidth_positive A C hC) z f
  have hr : (fun i j => (ForestCountIdentification.smallX A.small z i j:ℤ))=
      ForestScaledPenalty.rowCounts A z := rfl
  have hc : (fun i j => ((A.b i j-ForestCountIdentification.smallY A.small z i j:ℕ):ℤ))=
      ForestScaledPenalty.columnCounts A z := rfl
  rw [hr,hc] at hp
  rw [hp]
  congr 1
  ring

lemma sum_density_integer (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) :
    (∑ f : FreeIndex A.small A.T A.b,rho A S C a z (integerPoint A C f))=
      RootedCountIdentification.h A S (a*C/height A C) z := by
  unfold RootedCountIdentification.h
  apply Finset.sum_congr rfl
  intro f _
  exact density_at_integer A S C a hC z f

lemma binSum_positive (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) : 0<binSum A S C a z K := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact Finset.sum_pos (fun _ _ => gridWeight_positive _ _ _ _ _ _) Finset.univ_nonempty

theorem correction_bounds (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0<K) (hW : 100*A.d*K≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (f : FreeIndex A.small A.T A.b) :
    1/8≤ correction A S C a z K hK f ∧ correction A S C a z K hK f≤4 := by
  let v := integerBin A K hK f
  have hpQ := CompanionOracleDensity.actual_population_bounds A K hK hW v
  have hp : (1/2:ℝ)≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A≤2 := by
    constructor
    · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.2
  have hdist : ∀ i,|realCorner v i-integerPoint A C f i|≤1 := by
    intro i
    simpa only [abs_sub_comm] using CompanionOracleDensity.integerPoint_distance A C K hK hB f i
  have hb := bin_comparison A S C a hC ha haH z (realCorner v) (integerPoint A C f) hdist
  have hw := gridWeight_positive A S C a z v
  have hr : (1/4:ℝ)≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v ∧
      rho A S C a z (integerPoint A C f)/gridWeight A S C a z v≤2 := by
    constructor
    · apply (le_div_iff₀ hw).mpr
      simpa only [gridWeight,div_eq_mul_inv,mul_comm,one_mul] using hb.1
    · exact (div_le_iff₀ hw).mpr (by simpa only [gridWeight] using hb.2)
  have he : correction A S C a z K hK f=
      ((K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)*
        (rho A S C a z (integerPoint A C f)/gridWeight A S C a z v) := by
    unfold correction
    ring
  rw [he]
  constructor
  · have hh := mul_le_mul hp.1 hr.1 (by norm_num : (0:ℝ)≤1/4) (by linarith :
        0≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)
    norm_num at hh ⊢
    exact hh
  · have hh := mul_le_mul hp.2 hr.2 (by linarith [hr.1] :
        0≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v)
      (by norm_num : (0:ℝ)≤2)
    norm_num at hh ⊢
    exact hh

lemma corrected_mass_product (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) :
    correctedMass A S C a z K hK f*correction A S C a z K hK f=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        rho A S C a z (integerPoint A C f) := by
  have hw := (gridWeight_positive A S C a z (integerBin A K hK f)).ne'
  have hf : ((integerFiber A K hK (integerBin A K hK f)).card:ℝ)≠0 := by
    exact_mod_cast (ownFiber_positive A K hK f).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold correctedMass correction
  field_simp [hw,hf,hc,hz]

theorem corrected_expectation (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    (∑ f : FreeIndex A.small A.T A.b,
      correctedMass A S C a z K hK f*correction A S C a z K hK f)=
      ((K:ℝ)^dimension A/(assignmentCount A*binSum A S C a z K))*
        RootedCountIdentification.h A S (a*C/height A C) z := by
  simp_rw [corrected_mass_product]
  rw [←Finset.mul_sum,sum_density_integer A S C a hC]

lemma ratioMean_eq (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) :
    ratioMean A S C a z K=binSum A S C (a+1) z K/binSum A S C a z K := by
  unfold ratioMean binSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  have hv := (gridWeight_positive A S C a z v).ne'
  have hz := (binSum_positive A S C a z K hK).ne'
  unfold ratioObservable
  change (gridWeight A S C a z v/binSum A S C a z K)*
    (gridWeight A S C (a+1) z v/gridWeight A S C a z v)=
      gridWeight A S C (a+1) z v/binSum A S C a z K
  field_simp [hv,hz]

lemma binSum_zero (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) : binSum A S C 0 z K=(K:ℝ)^dimension A := by
  simp only [binSum,gridWeight,V,DenseWeights.binWeight,zero_div,zero_mul,Int.floor_zero,
    Int.cast_zero,neg_zero,Real.rpow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    mul_one,CompanionOracleDensity.oracle_grid_card,Nat.cast_pow]

lemma ratio_telescope (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (∏ a∈Finset.range j,ratioMean A S C a z K)=binSum A S C j z K/(K:ℝ)^dimension A := by
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  induction j with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,Nat.cast_zero,binSum_zero,div_self hp]
  | succ j ih =>
    rw [Finset.prod_range_succ,ih,ratioMean_eq A S C j z K hK]
    have hz := (binSum_positive A S C j z K hK).ne'
    push_cast
    field_simp [hp,hz]

theorem oracle_telescope (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (K : ℕ) (hK : 0<K) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ a∈Finset.range j,ratioMean A S C a z K)*
      (∑ f : FreeIndex A.small A.T A.b,
        correctedMass A S C j z K hK f*correction A S C j z K hK f)=
      RootedCountIdentification.h A S ((j:ℝ)*C/height A C) z := by
  rw [ratio_telescope A S C z K hK j,corrected_expectation A S C j hC z K hK]
  have hp : (K:ℝ)^dimension A≠0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  have hz := (binSum_positive A S C j z K hK).ne'
  have hc : (assignmentCount A:ℝ)≠0 := by exact_mod_cast (assignmentCount_positive A).ne'
  field_simp [hp,hz,hc]

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleChain
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bin chain for the computed-root forest penalty

All cut geometry is proved from the selected-root density. The only
conditional inputs are the same finite-box Prékopa–Leindler inequality
and finite reversible-chain Cheeger theorem used by the original chain.
-/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height proposal_bounds proposal_degree cutConstant)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracleChain_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    (oracleChain A R C a z hK).π v = gridWeight A R C a z v/
      ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w := rfl

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth height_positive oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem oracleStationaryLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    ((oracleStationaryLaw A R C a z hK).mass v:ℝ)=(oracleChain A R C a z hK).π v := by
  change ((rationalGridWeight A R C a z v/
    ∑ w : Grid (I := Fin (dimension A)) K,rationalGridWeight A R C a z w:ℚ):ℝ)=_
  simp only [Rat.cast_div,Rat.cast_sum,rationalGridWeight_cast]
  rfl

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The stationary bin draw followed by the actual uniform integer
interval draw is precisely the corrected mass used in the exact h identity. -/
theorem stationaryIntegerLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (f : FreeIndex A.small A.T A.b) :
    ((stationaryIntegerLaw A R C a z K hK hW).mass f:ℝ)=correctedMass A R C a z K (by omega) f := by
  change ((∑ v,(oracleStationaryLaw A R C a z hK).mass v*
    (exactBinLaw A K (by omega) hW v).mass f:ℚ):ℝ)=_
  simp only [Rat.cast_sum,Rat.cast_mul,exactBinLaw_mass,oracleStationaryLaw_cast,
    oracleChain_pi,apply_ite,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_zero]
  calc
    _ = ∑ v : Grid (I := Fin (dimension A)) K,
        if integerBin A K (by omega) f=v then
          gridWeight A R C a z v/binSum A R C a z K/(integerFiber A K (by omega) v).card else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [binSum,div_eq_mul_inv,one_mul,mul_zero]
    _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,correctedMass]

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma correctionMean_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) :
    correctionMean A R C a z K hK hW=
      ∑ f : FreeIndex A.small A.T A.b,
        correctedMass A R C a z K (by omega) f*correction A R C a z K (by omega) f := by
  unfold correctionMean expectation
  simp_rw [stationaryIntegerLaw_cast]

lemma correctionMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) :
    1/8 ≤ correctionMean A R C a z K hK hW ∧ correctionMean A R C a z K hK hW ≤ 4 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  exact expectation_bounds _ _ _ _ (correction_bounds A R C a (by exact_mod_cast hC)
    (Nat.cast_nonneg _) haHR z K (by omega) hW hB)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma floor_step (x q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  omega

/-- The actual phase observable takes exactly the two source values,
since one annealing step changes its integer exponent by zero or one. -/
theorem ratioObservable_cases (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    ratioObservable A R C a z v=1 ∨ ratioObservable A R C a z v=1/2 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  let q := D A R C z (realCorner v)/height A C
  have hq0 : 0 ≤ q := div_nonneg hD.1 (height_positive A C hC).le
  have hq1 : q ≤ 1 := (div_le_one (height_positive A C hC)).mpr hD.2
  let x := (a:ℝ)/height A C*D A R C z (realCorner v)
  have he : ((a:ℝ)+1)/height A C*D A R C z (realCorner v)=x+q := by
    dsimp only [x,q]
    ring
  have hr : ratioObservable A R C a z v=(2:ℝ)^(-((⌊x+q⌋:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)) := by
    unfold ratioObservable gridWeight V DenseWeights.binWeight
    rw [he,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    change -((⌊x+q⌋:ℤ):ℝ)- -((⌊x⌋:ℤ):ℝ)=_
    ring
  rcases floor_step x q hq0 hq1 with hf|hf
  · left
    rw [hr,hf]
    simp
  · right
    rw [hr,hf]
    have hh : -(((⌊x⌋:ℤ)+1:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)=(-1:ℝ) := by
      push_cast
      ring
    rw [hh]
    norm_num

lemma ratioObservable_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ ratioObservable A R C a z v ∧ ratioObservable A R C a z v ≤ 1 := by
  rcases ratioObservable_cases A R C hC a z hz hKB v with h|h <;> rw [h] <;> norm_num

lemma ratioMean_stationary (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    expectation (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z)=ratioMean A R C a z K := by
  unfold expectation ratioMean
  apply Finset.sum_congr rfl
  intro v _
  rw [oracleStationaryLaw_cast,oracleChain_pi]
  rfl

lemma ratioMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C) :
    1/2 ≤ ratioMean A R C a z K ∧ ratioMean A R C a z K ≤ 1 := by
  rw [←ratioMean_stationary A R C a z hK]
  exact expectation_bounds _ _ _ _ (ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleEstimator
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The exact means appearing in the implemented product telescope to
h, including the integer-population correction and the free-assignment count. -/
theorem targetFactor_product (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ i,targetFactor A R C z K hK hW j i)=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := by
  have hp : (∏ a : Fin j,ratioMean A R C a.val z K)=
      ∏ a∈Finset.range j,ratioMean A R C a z K :=
    Fin.prod_univ_eq_prod_range (fun a : ℕ => ratioMean A R (C:ℝ) a z K) j
  rw [Fintype.prod_option]
  simp only [targetFactor]
  rw [hp,correctionMean_eq]
  have ht := oracle_telescope A R C (by exact_mod_cast hC) z K (by omega) j
  convert ht using 1 <;> first | rfl | ring

lemma targetFactor_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C) (i : Option (Fin j)) :
    0 < targetFactor A R C z K hK hW j i := by
  cases i with
  | none =>
    have hh := (correctionMean_bounds A R C j hC hj z K hK hW hB).1
    change 0 < correctionMean A R C j z K hK hW
    linarith
  | some a =>
    have hh := (ratioMean_bounds A R C a.val hC z hz hK hB.le).1
    change 0 < ratioMean A R C a.val z K
    linarith

/-- On the event certified by the actual independent block experiments,
the returned rational product estimates the literal original h-value. -/
theorem goodEstimate_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K)
    (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure)
    (hgood : GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws) :
    (1-(epsilon:ℝ)/4)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
        (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ∧
      (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ≤
        (1+(epsilon:ℝ)/4)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := by
  have htol : (innerTolerance epsilon j:ℝ)=
      (epsilon:ℝ)/(200*(Fintype.card (Option (Fin j)):ℝ)) := by
    simp only [innerTolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_one,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have hprod := FiniteProductAccuracy.product_relative
    (fun i => (observedFactor A R C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ))
    (targetFactor A R C z K hK hW j) (targetFactor_positive A R C hC z hz K hK hW hB j hj)
    epsilon (by exact_mod_cast he0) (by exact_mod_cast he1)
    (by intro i; rw [←htol]; exact hgood i) (by simp)
  have hcount : (0:ℝ) ≤ assignmentCount A := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hprod.1 hcount
  have hupp := mul_le_mul_of_nonneg_left hprod.2 hcount
  have htarget := targetFactor_product A R C hC z K hK hW j
  have hvalue : (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)=
      (assignmentCount A:ℝ)*∏ i,
        (observedFactor A R C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ) := by
    simp only [estimateValue,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod]
  rw [hvalue]
  rw [←htarget]
  constructor
  · simpa only [mul_left_comm] using hlow
  · simpa only [mul_left_comm] using hupp

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A concrete rational estimator with bounded independent Boolean input
has the required relative-error guarantee for the original h-value. -/
theorem estimateValue_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have ht : 0 ≤ RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := (RootedCountIdentification.h_positive A R _ _).le
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hp (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure) :
      (if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤
        if ¬GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws then 1 else 0 := by
    by_cases hg : GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws
    · have ha := goodEstimate_accuracy A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 v draws hg
      have hn : ¬((estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)) := by
        rintro (hb|hb) <;> nlinarith
      simp only [hn,hg,not_true_eq_false,ite_false,le_refl]
    · simp only [hg,not_false_eq_true,ite_true, if_true]
      split_ifs <;> norm_num
  exact (uniformAverage_mono _ _ hp).trans
    (goodEstimate_failure A R C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
      (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf hPL hCheeger v)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWords
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The single fixed-length word has exactly the previously analyzed
independent-product law. -/
theorem wordEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool =>
      if (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let test := fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure) test
  change uniformAverage (fun bits => test
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)) ≤ _
  exact he.trans_le
    (estimateValue_failure A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 hf hPL hCheeger v)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorAmplification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence amplification of the actual weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteMedianConfidence
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem medianEstimate_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool =>
      if (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
          (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ∧
        (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ≤
          (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0) := by
  have heh0 : 0 < epsilon/2 := by positivity
  have heh1 : epsilon/2 < 1 := by linarith
  have ht : 0 < RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := RootedCountIdentification.h_positive A R _ _
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hbase := wordEstimate_failure A R C hC z hz K hK hW hB j hj (epsilon/2) 1 heh0 heh1
    (by norm_num) hPL hCheeger v
  have hbad : uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool =>
      if (wordEstimate A R C z K hK hW j (epsilon/2) 1 v bits:ℝ) <
          (1-(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (wordEstimate A R C z K hK hW j (epsilon/2) 1 v bits:ℝ)
      then (1:ℝ) else 0) ≤ 5/16 := by
    have hh : (1:ℝ)/4 ≤ 5/16 := by norm_num
    apply le_trans ?_ hh
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hbase
  have hm := median_confidence_real
    (wordEstimate A R C z K hK hW j (epsilon/2) 1 v)
    ((1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1-(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ)/2)*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z)
    (by nlinarith) (by nlinarith) delta hd hbad
  let test := fun xs : Fin (repetitionCount delta) →
      (Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool) =>
      if (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ≤
          (rationalMedian (List.ofFn (fun i => wordEstimate A R C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => wordEstimate A R C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ≤
          (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1)) test
  change 1-(delta:ℝ) ≤ uniformAverage (fun bits => test
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits))
  exact hm.trans_eq he.symm


end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWeightOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.RootedWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open CompanionWeightOracle
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem weight_source (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (j : ℕ)
    (S : Set (Labels A×Bool)) :
    RootedAnnealing.weight A R j S=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S)*(factorialRatio A S:ℝ) := by
  rw [factorialRatio_cast]
  have he : (j:ℝ)*(C:ℝ)/height A C=(j:ℝ)/CompanionAnnealing.scale A := by
    simpa only [height,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using
      CompanionAnnealing.source_parameter A C j hC
  rw [he]
  simp only [RootedAnnealing.weight,RootedFactorialApplication.f,firstLift,profile,mul_div_assoc]

end

end ContingencyTables.RootedWeightOracle

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedZeroLabels
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting when the retained small cells have no positive capacities

The paired transversal space then has one state. The terminal total is
one actual free-assignment weight, so the bounded-word
weight estimator applies directly; no Markov restart is needed.
-/

namespace ContingencyTables.RootedZeroLabels

open CommonBasesFPRAS CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CompanionWeightOracle CompanionTerminalMass CompanionTerminalApplication
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma small_capacity_zero (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (s : SmallCell A) : A.b s.val.1 s.val.2=0 := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  by_contra hn
  exact isEmptyElim (⟨s,⟨0,Nat.pos_of_ne_zero hn⟩⟩ : Labels A)

lemma profile_zero (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (S : Set (Labels A×Bool)) : profile A S=fun _ => 0 := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  funext u
  simp only [profile,LabelledFactorial.groupCount,Finset.univ_eq_empty,
    Finset.filter_empty,Finset.card_empty]

lemma factorialRatio_one (A : Instance I J) (hzero : Fintype.card (Labels A)=0)
    (S : Set (Labels A×Bool)) : factorialRatio A S=1 := by
  simp only [factorialRatio,factorialNumerator,factorialDenominator,profile_zero A hzero]
  have hz (s : SmallCell A) : A.b s.val.1 s.val.2=0 := small_capacity_zero A hzero s
  simp only [hz,Nat.factorial_zero,Finset.prod_const_one,Nat.cast_one,div_self (one_ne_zero : (1:ℚ) ≠ 0)]

lemma total_eq_h (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (hzero : Fintype.card (Labels A)=0) (C : ℕ) (hC : 0 < C) (j : ℕ) :
    RootedWarmStart.total A R j=
      RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (fun _ => 0) := by
  let : IsEmpty (Labels A) := Fintype.card_eq_zero_iff.mp hzero
  have hp : (pairs : List (Pair A))=[] := by
    simp only [pairs,Finset.univ_eq_empty,Finset.toList_empty,List.map_nil]
  rw [RootedWarmStart.total,hp,slotTotal_nil,RootedWeightOracle.weight_source A R C hC,
    profile_zero A hzero,factorialRatio_one A hzero]
  simp only [Rat.cast_one,mul_one]

/-- The direct all-large branch has arbitrary confidence using the
same actual finite-word evaluator, with no positive-label premise. -/
theorem success (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (hzero : Fintype.card (Labels A)=0) (E : Endpoints A)
    (C K L : ℕ) (hC : 0 < C) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (hW' : 20*A.d ≤ A.W)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (hH : finalPhase A L (epsilon:ℝ) ≤ rationalHeight A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits :
      Fin (medianEstimatorBits A C K (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta) → Bool =>
        let value := RootedOracleDensity.medianEstimate A R C (fun _ => 0) K hK hW
          (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta v bits
        if (1-(epsilon:ℝ))*tableCount A ≤ (value:ℝ) ∧
          (value:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A then (1:ℝ) else 0) := by
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have heR1 : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  have hterminal := RootedTerminalApplication.terminal_normalizer A R E L epsilon
    heR heR1 hW' hL
  have ht := total_eq_h A R hzero C hC (finalPhase A L (epsilon:ℝ))
  rw [ht] at hterminal
  have hm := RootedOracleDensity.medianEstimate_success A R C hC (fun _ => 0)
    (by intro u; exact Nat.zero_le _) K hK hW hB
    (finalPhase A L (epsilon:ℝ)) hH (epsilon/2) delta
    (by positivity) (by linarith) hd hPL hCheeger v
  apply hm.trans
  apply uniformAverage_mono
  intro bits
  let value := RootedOracleDensity.medianEstimate A R C (fun _ => 0) K hK hW
    (finalPhase A L (epsilon:ℝ)) (epsilon/2) delta v bits
  by_cases hgood :
      (1-((epsilon/2:ℚ):ℝ))*RootedCountIdentification.h A R
        ((finalPhase A L (epsilon:ℝ):ℝ)*C/height A C) (fun _ => 0) ≤ (value:ℝ) ∧
      (value:ℝ) ≤ (1+((epsilon/2:ℚ):ℝ))*RootedCountIdentification.h A R
        ((finalPhase A L (epsilon:ℝ):ℝ)*C/height A C) (fun _ => 0)
  · have hlo := mul_le_mul_of_nonneg_left hterminal.1
      (show 0 ≤ 1-(epsilon:ℝ)/2 by linarith)
    have hhi := mul_le_mul_of_nonneg_left hterminal.2
      (show 0 ≤ 1+(epsilon:ℝ)/2 by linarith)
    have hZ := tableCount_ge_one A
    have hout : (1-(epsilon:ℝ))*tableCount A ≤ (value:ℝ) ∧
        (value:ℝ) ≤ (1+(epsilon:ℝ))*tableCount A := by
      simp only [Rat.cast_div,Rat.cast_ofNat] at hgood
      constructor
      · nlinarith
      · nlinarith [mul_nonneg heR.le (show 0 ≤ tableCount A by linarith)]
    dsimp only [value] at hgood hout
    simp only [hgood,hout,le_refl]
  · dsimp only [value] at hgood
    simp only [hgood,ite_false]
    split_ifs <;> norm_num

end
end ContingencyTables.RootedZeroLabels

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingZero
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed zero-label counting branch

When all retained capacities vanish, the actual direct weight estimator
replaces the phase walk. Its target is still the original bounded-table
count, transported through the executed endpoint translation.
-/

namespace ContingencyTables.ComputedCountingZero

open CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open CompanionOracleDensity CompanionTerminalApplication
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem zero_success_oai (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I:=Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hzero : Fintype.card (Labels (data hEK r c b hne epsilon he))=0) :
    1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
      if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := by
  let A:=data hEK r c b hne epsilon he
  let K:=binCount r c b epsilon
  have hK: 1≤K:=binCount_pos r c b epsilon he
  have hW: 100*A.d*K≤A.W:=(cutoff_eq hEK r c b hne epsilon he).ge
  have hW': 20*A.d≤A.W := by
    have hh:=Nat.mul_le_mul_left (100*A.d) hK
    simp only [Nat.mul_one] at hh
    exact (show 20*A.d≤100*A.d by omega).trans (hh.trans hW)
  have hL: (∏ a : Fin m×Fin n,(A.b a.1 a.2+1))≤2^capacityBits r c b := by
    simpa only [A,data_capacityBits] using CountingTerminalSchedule.capacity_product_bound A
  have hH: finalPhase A (capacityBits r c b) ((epsilon/2:ℚ):ℝ)≤
      rationalHeight A (coefficient r c b epsilon) :=
    (phases_final hEK r c b hne epsilon he).symm.trans_le
      (phases_height hEK r c b hne epsilon he).le
  have hcount: CompanionTerminalMass.tableCount A=(Fintype.card (BoundedTable r c b):ℝ) :=
    ComputedCompanionInstance.original_count hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)
  have hs:=RootedZeroLabels.success A (ComputedCountingWords.root hEK r c b hne epsilon he)
    hzero (ComputedCompanionInstance.endpoints hEK r c b hne (cutoff r c b epsilon)
      (cutoff_two r c b epsilon he)) (coefficient r c b epsilon) K (capacityBits r c b)
    (coefficient_pos r c b epsilon he) hK hW (binCount_cast hEK r c b hne epsilon he) hW'
    (epsilon/2) delta (by positivity) (by linarith) hd hL hH
    (hPL _) (hCheeger _ _) (start hEK r c b hne epsilon he)
  rw [hcount] at hs
  dsimp only [A,K] at hs
  have hs': 1-(delta:ℝ)≤uniformAverage (fun bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool =>
      if (1-((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
      then (1:ℝ) else 0) := hs
  apply hs'.trans
  apply uniformAverage_mono
  intro bits
  have hZ: (0:ℝ)≤Fintype.card (BoundedTable r c b):=Nat.cast_nonneg _
  have heR: (0:ℝ)<epsilon:=by exact_mod_cast he
  by_cases hh:
      (1-((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
        (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
          (1+((epsilon/2:ℚ):ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
  · have hout:
        (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)≤
            (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ) ∧
          (zeroEstimate hEK r c b hne epsilon he delta bits:ℝ)≤
            (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) := by
      simp only [Rat.cast_div,Rat.cast_ofNat] at hh
      constructor <;> nlinarith [mul_nonneg heR.le hZ]
    simp only [hh,hout,le_refl]
  · simp only [hh,ite_false]
    split_ifs <;> norm_num

end
end ContingencyTables.ComputedCountingZero

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.ComputedCountingZero.zero_success_oai := @OAI.ContingencyTables.ComputedCountingZero.zero_success_oai

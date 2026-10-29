-- Prove2me | solution 1 for OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:37:17.143988+00:00
-- url     : https://prove2.me/submissions/64f0440b-a9d8-4acd-aae3-07eaf6ec9cd3

import Mathlib
import Lean.Elab.Tactic.Omega
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
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

namespace FiniteChain
variable {X : Type*} [sectionInstance56 : Fintype X] (C : FiniteChain X)

lemma pathExpectation_const (N : ℕ) (x : X) (a : ℝ) : C.pathExpectation N x (fun _ => a) = a := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih => simp [pathExpectation,ih,← Finset.sum_mul,C.stochastic]

end FiniteChain

open Set

open scoped BigOperators Classical

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
lemma uniformAverage_sub_const {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (r : ℝ) :
    uniformAverage (fun x => f x-r)=uniformAverage f-r := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib,sub_div]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  field_simp

section MetropolisSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance110 : Fintype Γ] [sectionInstance111 : DecidableEq Γ]
omit sectionInstance110 in
lemma exchangedSet_adjacent [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    ExchangeAdjacent S (exchangedSet S a) := by
  refine ⟨S\{a.1.val},a.1.val,a.2.val,?_,?_,?_,?_,rfl⟩
  · intro he
    exact a.2.property (he ▸ a.1.property)
  · simp
  · intro hx; exact a.2.property hx.1
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · intro hx; by_cases he : x=a.1.val
      · exact Or.inl he
      · exact Or.inr ⟨hx,he⟩
    · rintro (rfl|⟨hx,_⟩)
      · exact a.1.property
      · exact hx
omit sectionInstance110 in
lemma exchangedSet_left_difference [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    S\exchangedSet S a={a.1.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or,not_and]
  constructor
  · rintro ⟨hx,_,ha⟩
    by_contra hh
    exact ha hx hh
  · intro he
    subst x
    refine ⟨a.1.property,?_,fun _ hn => hn rfl⟩
    intro he
    exact a.2.property (he ▸ a.1.property)
omit sectionInstance110 sectionInstance111 in
lemma exchangedSet_right_difference [Fintype Γ] [DecidableEq Γ] (S : Set Γ) (a : ExchangeChoice S) :
    exchangedSet S a\S={a.2.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hh,hn⟩
    exact hh.resolve_right (fun h => hn h.1)
  · intro he; subst x
    exact ⟨Or.inl rfl,a.2.property⟩
lemma exchangedSet_injective (S : Set Γ) : Function.Injective (exchangedSet S) := by
  intro a b he
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg (fun T => S\T) he
    rw [exchangedSet_left_difference,exchangedSet_left_difference] at h
    exact Set.singleton_injective h
  · apply Subtype.ext
    have h := congrArg (fun T => T\S) he
    rw [exchangedSet_right_difference,exchangedSet_right_difference] at h
    exact Set.singleton_injective h
end MetropolisSampling
section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
omit sectionInstance113 in
lemma rationalMultiplier_cast [DecidableEq Γ] (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (S : Set Γ) :
    (rationalMultiplier gs w S:ℝ)=chainMultiplier gs (fun p r => (w p r:ℝ)) S := by
  unfold rationalMultiplier chainMultiplier
  split_ifs <;> simp
end RationalSampling

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalRootBisection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth rational bisection for the correction power of two -/

namespace ContingencyTables.RationalRootBisection

noncomputable section

/-- The target is used only in correctness, never by the algorithm. -/
theorem interval_contains (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    0 ≤ ((interval c s n).1:ℝ) ∧ ((interval c s n).1:ℝ) ≤ t ∧
      t ≤ ((interval c s n).2:ℝ) ∧ ((interval c s n).2:ℝ) ≤ 8 := by
  induction n with
  | zero => simpa only [interval,Rat.cast_zero,Rat.cast_ofNat] using ⟨le_refl 0,ht,ht8,le_refl 8⟩
  | succ n ih =>
    let ab := interval c s n
    let m : ℚ := (ab.1+ab.2)/2
    have hm0 : (0:ℝ) ≤ m := by
      dsimp only [m]
      push_cast
      change 0 ≤ (((interval c s n).1:ℝ)+((interval c s n).2:ℝ))/2
      linarith [ih.1,ih.2.1,ih.2.2.1]
    have hml : ((ab.1:ℚ):ℝ) ≤ m := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    have hmu : (m:ℝ) ≤ ab.2 := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    change 0 ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ≤ t ∧
      t ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ≤ 8
    by_cases h : m^s ≤ c
    · simp only [h,ite_true, if_true]
      have hp : (m:ℝ)^s ≤ t^s := by rw [hroot]; exact_mod_cast h
      exact ⟨hm0,le_of_pow_le_pow_left₀ hs.ne' ht hp,ih.2.2.1,ih.2.2.2⟩
    · simp only [h,ite_false]
      have hp : t^s < (m:ℝ)^s := by rw [hroot]; exact_mod_cast (lt_of_not_ge h)
      exact ⟨ih.1,ih.2.1,(lt_of_pow_lt_pow_left₀ s hm0 hp).le,hmu.trans ih.2.2.2⟩

lemma interval_width (c : ℚ) (s n : ℕ) :
    (interval c s n).2-(interval c s n).1=8/(2:ℚ)^n := by
  induction n with
  | zero => norm_num [interval]
  | succ n ih =>
    simp only [interval,pow_succ]
    split_ifs <;> dsimp only
    all_goals
      have hn : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
      field_simp [hn] at ih ⊢
      nlinarith

/-- A fixed depth yields an absolute error certificate for every rational
power comparison path. -/
theorem midpoint_error (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    |(midpoint c s n:ℝ)-t| ≤ 8/(2:ℝ)^n := by
  have hb := interval_contains c s hs t ht ht8 hroot n
  have hw : ((interval c s n).2:ℝ)-((interval c s n).1:ℝ)=8/(2:ℝ)^n := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (interval_width c s n)
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hh
  unfold midpoint
  push_cast
  exact abs_le.mpr ⟨by linarith [hb.2.1,hb.2.2.1],by linarith [hb.2.1,hb.2.2.1]⟩

end

end ContingencyTables.RationalRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PowerOfTwoApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded rational approximation to the evaluator's power of two -/

namespace ContingencyTables.PowerOfTwoApproximation

open RationalRootBisection

noncomputable section

lemma rounded_bounds (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    rounded beta s ≤ (beta:ℝ) ∧ (beta:ℝ)-rounded beta s ≤ 1/(s:ℝ) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hlow : (numerator beta s:ℚ) ≤ (s:ℚ)*beta := Int.floor_le _
  have hhigh : (s:ℚ)*beta < (numerator beta s:ℚ)+1 := Int.lt_floor_add_one _
  have hl : (numerator beta s:ℝ) ≤ (s:ℝ)*(beta:ℝ) := by exact_mod_cast hlow
  have hu : (s:ℝ)*(beta:ℝ) < (numerator beta s:ℝ)+1 := by exact_mod_cast hhigh
  constructor
  · exact (div_le_iff₀ hsR).mpr (by simpa only [mul_comm] using hl)
  · unfold rounded
    apply (le_div_iff₀ hsR).mpr
    have he : ((beta:ℝ)-(numerator beta s:ℝ)/(s:ℝ))*(s:ℝ)=
        (s:ℝ)*(beta:ℝ)-(numerator beta s:ℝ) := by field_simp
    rw [he]
    linarith

lemma rounded_power_root (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    ((2:ℝ)^rounded beta s)^s=(((2:ℚ)^numerator beta s:ℚ):ℝ) := by
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  unfold rounded
  rw [div_mul_cancel₀ _ hsR,Real.rpow_intCast]
  exact (Rat.cast_zpow _ _).symm

/-- Rounding downward loses at most 1/s in relative value. The proof uses
only the tangent bound for exp and log 2 ≤ 1. -/
lemma rounded_power_error (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    0 ≤ (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ∧
      (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ≤ (2:ℝ)^(beta:ℝ)/(s:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hT : 0 < (2:ℝ)^(beta:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hd : rounded beta s-(beta:ℝ) ≤ 0 := by linarith [hb.1]
  have hmul := mul_le_mul_of_nonpos_right hlog hd
  have he := Real.add_one_le_exp (Real.log 2*(rounded beta s-(beta:ℝ)))
  have hlower : 1-1/(s:ℝ) ≤ (2:ℝ)^rounded beta s/(2:ℝ)^(beta:ℝ) := by
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [hb.2]
  have hprod := (le_div_iff₀ hT).mp hlower
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) hb.1)
  · calc
      _ ≤ (2:ℝ)^(beta:ℝ)-(1-1/(s:ℝ))*(2:ℝ)^(beta:ℝ) := by linarith
      _ = _ := by ring

/-- The only non-rational quantity in the proof is the target. The
returned value is the midpoint of a fixed number of rational comparisons. -/
theorem approximation_error (beta : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (s n : ℕ) (hs : 0 < s) (sigma : ℝ)
    (hbudget : 1/(s:ℝ)+32/(2:ℝ)^n ≤ sigma) :
    |(approximation beta s n:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ sigma*(2:ℝ)^(beta:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hp := rounded_power_error beta s hs
  have ht0 : 0 ≤ (2:ℝ)^rounded beta s := (Real.rpow_pos_of_pos (by norm_num) _).le
  have ht8 : (2:ℝ)^rounded beta s ≤ 8 := by
    have hr : rounded beta s ≤ 2 := hb.1.trans (by exact_mod_cast hhi)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at hh
    linarith
  have hT : (1/4:ℝ) ≤ (2:ℝ)^(beta:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (-2:ℝ) ≤ (beta:ℝ) by exact_mod_cast hlo)
    norm_num at hh
    exact hh
  have he := midpoint_error ((2:ℚ)^numerator beta s) s hs ((2:ℝ)^rounded beta s)
    ht0 ht8 (rounded_power_root beta s hs) n
  have hscale : 8/(2:ℝ)^n ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 32/(2:ℝ)^n by positivity)
    convert hh using 1 <;> first | rfl | ring
  have htpos : 0 ≤ (2:ℝ)^(beta:ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ |(approximation beta s n:ℝ)-(2:ℝ)^rounded beta s|+
        |(2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ)| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        ((approximation beta s n:ℝ)-(2:ℝ)^rounded beta s)
        ((2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ))
    _ ≤ 8/(2:ℝ)^n+(2:ℝ)^(beta:ℝ)/(s:ℝ) := by
      exact add_le_add he (by rw [abs_of_nonpos (by linarith [hp.1])]; linarith [hp.2])
    _ ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ)+(2:ℝ)^(beta:ℝ)/(s:ℝ) := add_le_add hscale le_rfl
    _ = (1/(s:ℝ)+32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget htpos

lemma degree_positive (sigma : ℚ) (hsigma : 0 < sigma) : 0 < rootDegree sigma := by
  have h := Nat.le_ceil (128/sigma:ℚ)
  have hp : (0:ℚ) < 128/sigma := by positivity
  have hc : (0:ℚ) < rootDegree sigma := lt_of_lt_of_le hp h
  exact_mod_cast hc

lemma error_budget (sigma : ℚ) (hsigma : 0 < sigma) :
    1/(rootDegree sigma:ℝ)+32/(2:ℝ)^depth sigma ≤ (sigma:ℝ) := by
  have hs := degree_positive sigma hsigma
  have hsR : (0:ℝ) < rootDegree sigma := by exact_mod_cast hs
  have hsigmaR : (0:ℝ) < sigma := by exact_mod_cast hsigma
  have hceil : (128:ℝ)/(sigma:ℝ) ≤ rootDegree sigma := by
    have hh := Nat.le_ceil (128/sigma:ℚ)
    exact_mod_cast hh
  have hpow : (rootDegree sigma:ℝ) ≤ (2:ℝ)^depth sigma := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (rootDegree sigma)
  have hrec : 1/(rootDegree sigma:ℝ) ≤ (sigma:ℝ)/128 := by
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<128)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  have hrec' : 32/(2:ℝ)^depth sigma ≤ (sigma:ℝ)/4 := by
    apply (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 32) hsR hpow).trans
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<4)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  linarith

theorem approximate_error (beta sigma : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (hsigma : 0 < sigma) :
    |(approximate beta sigma:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ (sigma:ℝ)*(2:ℝ)^(beta:ℝ) :=
  approximation_error beta hlo hhi _ _ (degree_positive sigma hsigma) _ (error_budget sigma hsigma)

end

end ContingencyTables.PowerOfTwoApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCorrectionArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rationalIntegerPoint_cast (A : Instance I J) (C : ℕ) (f : FreeIndex A.small A.T A.b)
    (i : Fin (dimension A)) :
    (rationalIntegerPoint A C f i:ℝ)=integerPoint A C f i := by
  simp only [rationalIntegerPoint,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,rationalBinWidth_cast,
    integerPoint,ForestScaledPenalty.integerCube,freeRange,Nat.cast_add,Nat.cast_one]
  push_cast
  rfl

lemma rationalPopulation_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) : 0 < rationalPopulation A K hK f := by
  unfold rationalPopulation
  apply div_pos
  · exact mul_pos (pow_pos (by exact_mod_cast hK) _) (by exact_mod_cast ownFiber_positive A K hK f)
  · exact_mod_cast assignmentCount_positive A

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

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleSchedule
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sampleCount_positive (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) : 0 < sampleCount j delta failure := by
  have hh := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
  have hp : (0:ℚ) < sampleCount j delta failure := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

end

end ContingencyTables.CompanionOracleDensity

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorRange
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Output range on every execution of the finite-word estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rationalAverage_bounds {X : Type*} (g : X → ℚ) (N : ℕ) (hN : 0 < N)
    (L U : ℝ) (hg : ∀ x,L ≤ (g x:ℝ) ∧ (g x:ℝ) ≤ U) (draws : Fin N → X) :
    L ≤ (rationalAverage g N draws:ℝ) ∧ (rationalAverage g N draws:ℝ) ≤ U := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hg (draws i)).1)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hg (draws i)).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hl hu
  simp only [rationalAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
  exact ⟨(le_div_iff₀ hNR).mpr (by linarith),(div_le_iff₀ hNR).mpr (by linarith)⟩

end

end ContingencyTables.CompanionOracleDensity

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

lemma rationalMedian_mem (l : List ℚ) (hl : 0 < l.length) : rationalMedian l ∈ l := by
  have hi : l.length/2 < (l.mergeSort (· ≤ ·)).length := by
    rw [List.length_mergeSort]
    omega
  unfold rationalMedian
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_mergeSort.mp (List.getElem_mem hi)

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

lemma profile_inBox (A : Instance I J) (S : Set (Labels A×Bool)) :
    BalancedBox.InBox (bounds A) (profile A S) := by
  rw [←label_capacity]
  exact SliceFactorial.groupCount_inBox _ _

lemma factorialRatio_positive (A : Instance I J) (S : Set (Labels A×Bool)) :
    0 < factorialRatio A S := by
  unfold factorialRatio factorialNumerator factorialDenominator
  positivity

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

lemma independent_pair_failure {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (P : X → Prop) (Q : Y → Prop)
    (a b : ℝ) (hP : uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ a)
    (hQ : uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) ≤ b) :
    uniformAverage (fun xy : X×Y => if ¬(P xy.1 ∧ Q xy.2) then (1:ℝ) else 0) ≤ a+b := by
  have hfst : uniformAverage (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)=
      uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun x : X => uniformAverage (fun _y : Y => if ¬P x then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)
      _ = _ := by simp_rw [uniformAverage_const]
  have hsnd : uniformAverage (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)=
      uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun _x : X => uniformAverage (fun y : Y => if ¬Q y then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)
      _ = _ := uniformAverage_const _
  calc
    _ ≤ uniformAverage (fun xy : X×Y =>
        (if ¬P xy.1 then (1:ℝ) else 0)+(if ¬Q xy.2 then (1:ℝ) else 0)) := by
      apply uniformAverage_mono
      intro xy
      by_cases hp : P xy.1 <;> by_cases hq : Q xy.2 <;> simp [hp,hq]
    _ = uniformAverage (fun x => if ¬P x then (1:ℝ) else 0)+
        uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
      rw [uniformAverage_add,hfst,hsnd]
    _ ≤ a+b := add_le_add hP hQ

end

end ContingencyTables.CompanionPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRationalThreshold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded dyadic comparison with a rational acceptance probability -/

namespace ContingencyTables.FairBits

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

lemma rationalThreshold_le (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    rationalThreshold k q ≤ 2^k := by
  have h := Nat.floor_le (mul_nonneg (by positivity : (0:ℚ) ≤ 2^k) hq0)
  have h' : (rationalThreshold k q:ℚ) ≤ (2:ℚ)^k := by
    change (⌊(2:ℚ)^k*q⌋₊:ℚ) ≤ (2:ℚ)^k
    exact h.trans (by nlinarith [pow_pos (by norm_num : (0:ℚ)<2) k])
  exact_mod_cast h'

lemma rationalThreshold_count (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (Finset.univ.filter (fun z : Fin (2^k) => z.val < rationalThreshold k q)).card=
      rationalThreshold k q := by
  rw [Fin.card_filter_val_lt,min_eq_right (rationalThreshold_le k q hq0 hq1)]

/-- The finite coin always rounds downward and loses less than one
code word, including the exact endpoint probabilities zero and one. -/
theorem rationalThreshold_error (k : ℕ) (q : ℚ) (hq : 0 ≤ q) :
    0 ≤ rationalThresholdMass k q ∧ rationalThresholdMass k q ≤ q ∧
      q-rationalThresholdMass k q < 1/(2:ℚ)^k := by
  have hp : (0:ℚ)<2^k := by positivity
  have hlo := Nat.floor_le (mul_nonneg hp.le hq)
  have hhi := Nat.lt_floor_add_one ((2:ℚ)^k*q)
  change 0 ≤ (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ∧
    (⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k ≤ q ∧
    q-(⌊(2:ℚ)^k*q⌋₊:ℚ)/(2:ℚ)^k < 1/(2:ℚ)^k
  refine ⟨by positivity,?_,?_⟩
  · exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hlo)
  · rw [sub_div' hp.ne',div_lt_div_iff_of_pos_right hp]
    nlinarith

/-- An actual k-bit input realizes the stated rounded probability. -/
theorem rationalThreshold_expectation (k : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    uniformAverage (fun bits : Fin k → Bool =>
      if rationalThresholdAccept k q bits then (1:ℝ) else 0)=
        (rationalThresholdMass k q:ℝ) := by
  have he := uniformAverage_equiv (binaryWordEquiv k)
    (fun z : Fin (2^k) => if z.val < rationalThreshold k q then (1:ℝ) else 0)
  simp only [rationalThresholdAccept]
  rw [he]
  unfold uniformAverage
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,rationalThreshold_count k q hq0 hq1,
    Fintype.card_fin,rationalThresholdMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,
    Nat.cast_pow,Nat.cast_ofNat]

end

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBooleanPhase
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion phase walk driven by disjoint bounded Boolean words -/

namespace ContingencyTables.CompanionBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact subsetBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (State A)))
    (fun T : State A => ExchangeAdjacent S.val T.val) (proposalBits A) (proposal_codes A S) T

end

end ContingencyTables.CompanionBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

theorem mem_binaryExchangeIndices (xs : List ℕ) (i j : ℕ) :
    (i,j)∈binaryExchangeIndices xs ↔
      i<xs.length ∧ j<xs.length ∧ xs.getD i 0=0 ∧ xs.getD j 0=1 := by
  simp only [binaryExchangeIndices,List.mem_filter,mem_cellPairs,binaryExchangeTest,
    decide_eq_true_eq]
  tauto

theorem binaryExchangeIndices_nodup (xs : List ℕ) : (binaryExchangeIndices xs).Nodup :=
  (cellPairs_nodup xs xs).filter _

lemma setProfile_injective {n : ℕ} : Function.Injective (setProfile (n := n)) := by
  intro S T he
  ext i
  have hi := congrFun he i
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp_all [setProfile]

/-- On an absent/present coordinate pair, the natural update is exactly
set removal followed by set insertion. -/
theorem exchange_setProfile {n : ℕ} (S : Set (Fin n)) (i j : Fin n)
    (hi : i∉S) (hj : j∈S) :
    IntegerWeightedTransport.exchangeTarget (setProfile S) i j=
      setProfile (insert i (S\{j})) := by
  have hij : i≠j := fun he => hi (he ▸ hj)
  funext a
  by_cases hai : a=i
  · subst a
    simp [IntegerWeightedTransport.exchangeTarget,setProfile,hi,hij]
  · by_cases haj : a=j
    · subst a
      simp [IntegerWeightedTransport.exchangeTarget,setProfile,hj,hai]
    · by_cases ha : a∈S <;>
        simp [IntegerWeightedTransport.exchangeTarget,setProfile,hai,haj,ha]

/-- Every program output is a genuine binary exchange, and all such
exchanges are listed. No enumeration of the set of states is involved. -/
theorem mem_binaryExchanges_setProfile {n : ℕ} (S : Set (Fin n)) (ys : List ℕ) :
    ys∈binaryExchanges (List.ofFn (setProfile S)) ↔
      ∃ i j : Fin n,i∉S ∧ j∈S ∧ ys=List.ofFn (setProfile (insert i (S\{j}))) := by
  simp only [binaryExchanges,List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩,hij,rfl⟩
    have h := (mem_binaryExchangeIndices _ i j).mp hij
    have hi : i<n := by simpa only [List.length_ofFn] using h.1
    have hj : j<n := by simpa only [List.length_ofFn] using h.2.1
    let a : Fin n := ⟨i,hi⟩
    let b : Fin n := ⟨j,hj⟩
    have hget (k : Fin n) : (List.ofFn (setProfile S)).getD k.val 0=setProfile S k := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
      simp only [Option.getD_some,List.getElem_ofFn]
    have ha : a∉S := by
      have hh := h.2.2.1
      rw [hget a] at hh
      intro ha
      simp [setProfile,ha] at hh
    have hb : b∈S := by
      have hh := h.2.2.2
      rw [hget b] at hh
      by_contra hn
      simp [setProfile,hn] at hh
    refine ⟨a,b,ha,hb,?_⟩
    exact (listExchange_ofFn (setProfile S) a b).trans
      (congrArg List.ofFn (exchange_setProfile S a b ha hb))
  · rintro ⟨i,j,hi,hj,rfl⟩
    refine ⟨(i.val,j.val),?_,?_⟩
    · apply (mem_binaryExchangeIndices _ _ _).mpr
      refine ⟨by simp,by simp,?_,?_⟩ <;>
        simp [List.getD_eq_getElem?_getD,setProfile,hi,hj]
    · exact ((listExchange_ofFn (setProfile S) i j).trans
        (congrArg List.ofFn (exchange_setProfile S i j hi hj)))

lemma getD_setProfile {n : ℕ} (S : Set (Fin n)) (i : Fin n) :
    (List.ofFn (setProfile S)).getD i.val 0=setProfile S i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,List.getElem_ofFn]

lemma binaryIndex_specs {n : ℕ} (S : Set (Fin n)) (ij : ℕ×ℕ)
    (h : ij∈binaryExchangeIndices (List.ofFn (setProfile S))) :
    ∃ i j : Fin n,ij=(i.val,j.val) ∧ i∉S ∧ j∈S := by
  have hh := (mem_binaryExchangeIndices _ ij.1 ij.2).mp h
  have hi : ij.1<n := by simpa only [List.length_ofFn] using hh.1
  have hj : ij.2<n := by simpa only [List.length_ofFn] using hh.2.1
  let i : Fin n := ⟨ij.1,hi⟩
  let j : Fin n := ⟨ij.2,hj⟩
  refine ⟨i,j,rfl,?_,?_⟩
  · intro hm
    have he := hh.2.2.1
    rw [getD_setProfile S i] at he
    simp [setProfile,hm] at he
  · by_contra hm
    have he := hh.2.2.2
    rw [getD_setProfile S j] at he
    simp [setProfile,hm] at he

/-- Distinct eligible coordinate pairs give distinct binary profiles. -/
theorem binaryExchanges_nodup {n : ℕ} (S : Set (Fin n)) :
    (binaryExchanges (List.ofFn (setProfile S))).Nodup := by
  apply (binaryExchangeIndices_nodup _).map_on
  intro a ha b hb he
  obtain ⟨i,j,rfl,hi,hj⟩ := binaryIndex_specs S a ha
  obtain ⟨u,v,rfl,hu,hv⟩ := binaryIndex_specs S b hb
  rw [listExchange_ofFn,listExchange_ofFn,exchange_setProfile S i j hi hj,
    exchange_setProfile S u v hu hv] at he
  have hs := setProfile_injective (List.ofFn_injective he)
  change CommonBasesFPRAS.exchangedSet S (⟨j,hj⟩,⟨i,hi⟩)=
    CommonBasesFPRAS.exchangedSet S (⟨v,hv⟩,⟨u,hu⟩) at hs
  have hp := CommonBasesFPRAS.exchangedSet_injective S hs
  have h1 : i=u := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.2.val) hp
  have h2 : j=v := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.1.val) hp
  subst u
  subst v
  rfl

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

omit [Codec A] [Inhabited A] in
/-- The literal binary program has the previously proved dyadic proposal
law, including all unused indices that return `none`. -/
theorem listWordChoice_mass [Fintype A] [DecidableEq A]
    (xs : List A) (hxs : xs.Nodup) (k : ℕ) (hk : xs.length≤2^k) (a : A) :
    (FirstSuccess.mapLaw
      (FirstSuccess.uniformLaw (α := Fin k → Bool))
      (fun bits => listWordChoice (xs,List.ofFn bits))).mass (some a)=
        if a∈xs then 1/(2:ℚ)^k else 0 := by
  simp_rw [listWordChoice_ofFn]
  exact FairBits.listBitDraw_mass xs hxs k hk a

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionArithmeticProposal
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit coordinate-list proposal for the companion chain

Only ordered coordinates are enumerated. The arithmetic binary-profile
program generates the possible exchanges, after which the actual chain
state predicate removes disallowed states. A dyadic list index has exactly
the same proposal law as the abstract injection.
-/

namespace ContingencyTables.CompanionArithmeticProposal
open CommonBasesFPRAS ProfilePrograms FirstSuccess ResidualMixture FairBits
open CompanionFactorialApplication CompanionBooleanPhase TwoLiftStates
open scoped BigOperators Classical

noncomputable section

section Coordinates
variable {Γ : Type*} [Fintype Γ] {n : ℕ} (e : Γ ≃ Fin n)

omit [Fintype Γ] in
lemma adjacent_preimage {Δ : Type*} [Fintype Δ] (f : Γ ≃ Δ) (S T : Set Δ)
    (h : ExchangeAdjacent S T) : ExchangeAdjacent (f ⁻¹' S) (f ⁻¹' T) := by
  obtain ⟨B,a,b,hab,ha,hb,rfl,rfl⟩ := h
  refine ⟨f ⁻¹' B,f.symm a,f.symm b,fun he => hab (f.symm.injective he),?_,?_,?_,?_⟩
  · simpa using ha
  · simpa using hb
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]

lemma adjacent_coordinate_iff (S T : Set Γ) :
    ExchangeAdjacent (coordinateSet e S) (coordinateSet e T) ↔ ExchangeAdjacent S T := by
  constructor
  · intro h
    have hh : ExchangeAdjacent (physicalSet e (coordinateSet e S))
        (physicalSet e (coordinateSet e T)) := adjacent_preimage e _ _ h
    simpa only [physical_coordinate] using hh
  · exact adjacent_preimage e.symm S T

omit [Fintype Γ] in
@[simp] lemma decode_encode (S : Set Γ) : decodeSet e (encodeSet e S)=S := by
  ext a
  simp only [decodeSet,Set.mem_ofPred_eq,encodeSet,getD_setProfile,setProfile,
    coordinateSet,Set.mem_preimage,Equiv.symm_apply_apply]
  by_cases ha : a∈S <;> simp [ha]

omit [Fintype Γ] in
lemma encode_physical (U : Set (Fin n)) :
    encodeSet e (physicalSet e U)=List.ofFn (setProfile U) := by
  simp only [encodeSet,coordinate_physical]

/-- The executable integer update enumerates exactly the set exchanges. -/
theorem mem_raw_codes (S : Set Γ) (xs : List ℕ) :
    xs∈binaryExchanges (encodeSet e S) ↔
      ∃ T : Set Γ,ExchangeAdjacent S T ∧ xs=encodeSet e T := by
  rw [encodeSet,mem_binaryExchanges_setProfile]
  constructor
  · rintro ⟨i,j,hi,hj,rfl⟩
    let U := insert i (coordinateSet e S\{j})
    have hU : ExchangeAdjacent (coordinateSet e S) U :=
      exchangedSet_adjacent _ (⟨j,hj⟩,⟨i,hi⟩)
    refine ⟨physicalSet e U,?_,(encode_physical e U).symm⟩
    apply (adjacent_coordinate_iff e S _).mp
    simpa only [coordinate_physical] using hU
  · rintro ⟨T,hST,rfl⟩
    obtain ⟨j,hj,i,hi,he⟩ := ((adjacent_coordinate_iff e S T).mpr hST).move
    exact ⟨i,j,hi,hj,by rw [encodeSet,he]⟩

lemma mem_neighborSets (S T : Set Γ) : T∈neighborSets e S ↔ ExchangeAdjacent S T := by
  simp only [neighborSets,List.mem_map,mem_raw_codes]
  constructor
  · rintro ⟨xs,⟨U,hU,rfl⟩,he⟩
    have he' : U=T := by simpa only [decode_encode] using he
    exact he' ▸ hU
  · intro h
    exact ⟨encodeSet e T,⟨T,h,rfl⟩,decode_encode e T⟩

lemma neighborSets_nodup (S : Set Γ) : (neighborSets e S).Nodup := by
  apply (binaryExchanges_nodup (coordinateSet e S)).map_on
  intro xs hxs ys hys he
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes e S xs).mp hxs
  obtain ⟨U,hU,rfl⟩ := (mem_raw_codes e S ys).mp hys
  simpa only [decode_encode] using congrArg (encodeSet e) he

omit [Fintype Γ] in
lemma stateFilter_eq_some (gs : List (Γ×Γ)) (T : Set Γ) (U : ChainIndex gs) :
    (if h : ChainState gs T then some (⟨T,h⟩ : ChainIndex gs) else none)=some U ↔ T=U.val := by
  by_cases h : ChainState gs T
  · simp only [dite_eq_left h,Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [dite_eq_right h,reduceCtorEq,false_iff]
    intro he
    exact h (he.symm ▸ U.property)

lemma mem_neighborStates (gs : List (Γ×Γ)) (S T : ChainIndex gs) :
    T∈neighborStates e gs S ↔ ExchangeAdjacent S.val T.val := by
  simp only [neighborStates,List.mem_filterMap,stateFilter_eq_some]
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (mem_neighborSets e S.val T.val).mp hU
  · intro h
    exact ⟨T.val,(mem_neighborSets e S.val T.val).mpr h,rfl⟩

lemma neighborStates_nodup (gs : List (Γ×Γ)) (S : ChainIndex gs) :
    (neighborStates e gs S).Nodup := by
  apply List.Nodup.filterMap _ (neighborSets_nodup e S.val)
  intro T U V hT hU
  have hTV := (stateFilter_eq_some gs T V).mp (Option.mem_def.mp hT)
  have hUV := (stateFilter_eq_some gs U V).mp (Option.mem_def.mp hU)
  exact hTV.trans hUV.symm

end Coordinates

variable {I J : Type} [Fintype I] [Fintype J]

@[simp] theorem mem_neighbors (A : Instance I J) (S T : State A) :
    T∈neighbors A S ↔ ExchangeAdjacent S.val T.val :=
  mem_neighborStates _ _ _ _

theorem neighbors_nodup (A : Instance I J) (S : State A) : (neighbors A S).Nodup :=
  neighborStates_nodup _ _ _

theorem neighbors_length (A : Instance I J) (S : State A) :
    (neighbors A S).length≤2^proposalBits A := by
  have he : (neighbors A S).toFinset=Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val) := by
    ext T
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,mem_neighbors]
  rw [←List.toFinset_card_of_nodup (neighbors_nodup A S),he]
  simpa only [Fintype.card_subtype] using proposal_codes A S

theorem proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact (listWordChoice_mass (neighbors A S) (neighbors_nodup A S)
    (proposalBits A) (neighbors_length A S) T).trans (by simp only [mem_neighbors])

/-- The explicit arithmetic enumeration changes no proposal probabilities,
including the unused-code outcome. -/
theorem proposal_law (A : Instance I J) (S : State A) :
    mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)=
      mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
        (CompanionBooleanPhase.proposal A S) := by
  let p := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)
  let q := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
    (CompanionBooleanPhase.proposal A S)
  have hs (T : State A) : p.mass (some T)=q.mass (some T) :=
    (proposal_mass A S T).trans (CompanionBooleanPhase.proposal_mass A S T).symm
  change p=q
  apply RationalLaw.ext
  funext T
  cases T with
  | some T => exact hs T
  | none =>
    have hp := p.total
    have hq := q.total
    simp only [Fintype.sum_option] at hp hq
    simp_rw [hs] at hp
    linarith

end
end ContingencyTables.CompanionArithmeticProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealKernelApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accumulating rational implementation errors against a real kernel

The exact companion weights may be real. The implemented probabilities
are rational; comparison takes place after their canonical real cast.
-/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma distance_triangle (p q r : X → ℝ) : distance p r ≤ distance p q+distance q r := by
  have h := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => abs_sub_le (p x) (q x) (r x))
  simp only [Finset.sum_add_distrib] at h
  unfold distance
  linarith

lemma distance_push (K : FiniteKernel X Y) (p q : X → ℝ) :
    distance (K.push p) (K.push q) ≤ distance p q := by
  have hp (y : Y) : |K.push p y-K.push q y| ≤ ∑ x, |p x-q x| * K.P x y := by
    unfold FiniteKernel.push
    rw [←Finset.sum_sub_distrib]
    have h := Finset.abs_sum_le_sum_abs
      (fun x => p x*K.P x y-q x*K.P x y) Finset.univ
    simpa only [←sub_mul,abs_mul,abs_of_nonneg (K.nonnegative _ _)] using h
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hp y)
  have ht : (∑ y,∑ x, |p x-q x| * K.P x y) ≤ ∑ x,|p x-q x| := by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.substochastic x) (abs_nonneg (p x-q x)))
  unfold distance
  exact div_le_div_of_nonneg_right (hs.trans ht) (by norm_num)

lemma distance_push_rows (K L : FiniteKernel X Y) (p : X → ℝ)
    (hp : ∀ x,0 ≤ p x) :
    distance (K.push p) (L.push p) ≤ ∑ x,p x*distance (K.P x) (L.P x) := by
  have hb (y : Y) : |K.push p y-L.push p y| ≤ ∑ x,p x*|K.P x y-L.P x y| := by
    unfold FiniteKernel.push
    rw [←Finset.sum_sub_distrib]
    have h := Finset.abs_sum_le_sum_abs
      (fun x => p x*K.P x y-p x*L.P x y) Finset.univ
    simpa only [←mul_sub,abs_mul,abs_of_nonneg (hp _)] using h
  have hs := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) => hb y)
  rw [Finset.sum_comm] at hs
  simp only [←Finset.mul_sum] at hs
  unfold distance
  simpa only [Finset.sum_div,mul_div_assoc] using
    div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ)≤2)

lemma distance_push_two (K L : FiniteKernel X Y) (p q : X → ℝ)
    (hp : ∀ x,0 ≤ p x) (hmass : ∑ x,p x=1) (η : ℝ)
    (hη : ∀ x,distance (K.P x) (L.P x) ≤ η) :
    distance (K.push p) (L.push q) ≤ distance p q+η := by
  have hr : distance (K.push p) (L.push p) ≤ η := by
    calc
      _ ≤ ∑ x,p x*distance (K.P x) (L.P x) := distance_push_rows K L p hp
      _ ≤ ∑ x,p x*η := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hη x) (hp x))
      _ = η := by rw [←Finset.sum_mul,hmass,one_mul]
  have ht := distance_triangle (K.push p) (L.push p) (L.push q)
  have hc := distance_push L p q
  linarith

lemma rationalKernel_push (K : X → RationalLaw Y) (p : RationalLaw X) :
    (rationalKernel K).push (fun x => (p.mass x:ℝ))=
      fun y => ((bindLaw p K).mass y:ℝ) := by
  funext y
  simp only [rationalKernel,FiniteKernel.push,bindLaw,Rat.cast_sum,Rat.cast_mul]

variable [DecidableEq X]

/-- Each realized step may use fresh approximate oracle calls. A uniform
real row error adds once per actual step against the exact real chain. -/
theorem walk_distance (Q : X → RationalLaw X) (K : FiniteKernel X X)
    (η : ℝ) (hη : ∀ x,distance ((rationalKernel Q).P x) (K.P x) ≤ η)
    (x : X) (n : ℕ) :
    distance (fun y => ((walkLaw Q x n).mass y:ℝ)) ((K.power n).P x) ≤ n*η := by
  induction n with
  | zero =>
    simp only [walkLaw,FiniteKernel.power,Nat.cast_zero,zero_mul,distance]
    apply le_of_eq
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro y _
    by_cases h : x=y
    · subst y; simp [pointLaw,FiniteKernel.identity]
    · simp [pointLaw,FiniteKernel.identity,h,Ne.symm h]
  | succ n ih =>
    have hm : (∑ y,((walkLaw Q x n).mass y:ℝ))=1 := by
      exact_mod_cast (walkLaw Q x n).total
    have ht := distance_push_two (rationalKernel Q) K
      (fun y => ((walkLaw Q x n).mass y:ℝ)) ((K.power n).P x)
      (fun y => by exact_mod_cast (walkLaw Q x n).nonnegative y) hm η hη
    rw [rationalKernel_push] at ht
    change distance (fun y => ((walkLaw Q x (n+1)).mass y:ℝ)) ((K.power (n+1)).P x) ≤ _ at ht
    exact ht.trans (by push_cast; linarith)

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealPathApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping an entire finite history during real-kernel comparison -/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open CommonBasesFPRAS ResidualMixture FirstSuccess

noncomputable section
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

lemma rational_map_push [DecidableEq Y] (p : RationalLaw X) (f : X → Y) :
    (fun y => ((mapLaw p f).mass y:ℝ))=(mapKernel f).push (fun x => (p.mass x:ℝ)) := by
  funext y
  simp only [mapLaw,FiniteKernel.push,mapKernel,Rat.cast_sum,apply_ite,Rat.cast_zero,
    mul_one,mul_zero]

omit [Fintype X] [Fintype A] in
/-- Recording extra coordinates never increases one transition's error. -/
theorem lifted_row_distance [DecidableEq B] (Q : X → RationalLaw Y)
    (K : FiniteKernel X Y) (read : A → X) (put : A → Y → B) (a : A) :
    distance ((rationalKernel (liftRational Q read put)).P a)
      ((liftKernel K read put).P a) ≤ distance ((rationalKernel Q).P (read a)) (K.P (read a)) := by
  change distance (fun b => ((mapLaw (Q (read a)) (put a)).mass b:ℝ))
    ((mapKernel (put a)).push (K.P (read a))) ≤ _
  rw [rational_map_push]
  exact distance_push (mapKernel (put a)) _ _

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrajectory
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The observed Boolean trajectory has the source path law

The finite history stores the visited prefix. Its exact real reference
expectation is the manuscript's list-path expectation, so the row error
controls events involving all empirical observations simultaneously.
-/

namespace ContingencyTables.CompanionPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation CompanionBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

lemma prefix_last {N : ℕ} (a : PathState X N) :
    (historyPrefix a).getLast (prefix_nonempty a)=pathRead a := by
  unfold historyPrefix
  rw [List.getLast_ofFn_succ]
  apply congrArg a.2
  apply Fin.ext
  rfl

lemma prefix_end {N : ℕ} (a : PathState X N) :
    (historyPrefix a).dropLast++[pathRead a]=historyPrefix a := by
  rw [←prefix_last a]
  exact List.dropLast_append_getLast (prefix_nonempty a)

lemma read_put {N : ℕ} (a : PathState X N) (x : X) : pathRead (pathPut a x)=x := by
  simp [pathRead,pathPut]

lemma position_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    (pathPut a x).1.val=a.1.val+1 := by
  simp only [pathPut,nextPosition,min_eq_left (Nat.succ_le_of_lt h)]

lemma prefix_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    historyPrefix (pathPut a x)=historyPrefix a++[x] := by
  rcases a with ⟨⟨i,hi⟩,v⟩
  change i<N at h
  have hh : i+1≤N := by omega
  simp only [historyPrefix,pathPut,nextPosition,min_eq_left hh]
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext k
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      have hv' : k.val=i+1 := by simpa only [Fin.cast,Fin.castSucc,Fin.castAdd,Fin.castLE] using hv
      exact (Nat.ne_of_lt k.isLt) hv')]
    exact congrArg v (Fin.ext rfl)
  · simp only [List.singleton_inj]
    exact Function.update_self _ _ _

lemma prefix_initial (N : ℕ) (x : X) : historyPrefix (pathInitial N x)=[x] := by
  simp [historyPrefix,pathInitial,List.ofFn_succ]

variable [Fintype X]

private lemma power_succ_left (K : FiniteKernel X X) (n : ℕ) (x z : X) :
    (K.power (n+1)).P x z=∑ y,K.P x y*(K.power n).P y z := by
  induction n generalizing x z with
  | zero => simp [FiniteKernel.power,FiniteKernel.comp,FiniteKernel.identity]
  | succ n ih =>
    change (∑ y,(K.power (n+1)).P x y*K.P y z)=
      ∑ y,K.P x y*(∑ v,(K.power n).P y v*K.P v z)
    simp_rw [ih,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm

private lemma power_expectation_succ (K : FiniteKernel X X) (n : ℕ) (x : X) (F : X → ℝ) :
    (∑ z,(K.power (n+1)).P x z*F z)=
      ∑ y,K.P x y*(∑ z,(K.power n).P y z*F z) := by
  simp_rw [power_succ_left,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

omit [Fintype X] in
private lemma lift_expectation {Y Z : Type*} [Fintype Y] [Fintype Z]
    (K : FiniteKernel X Y) (read : Z → X) (put : Z → Y → Z) (a : Z) (F : Z → ℝ) :
    (∑ b,(liftKernel K read put).P a b*F b)=∑ y,K.P (read a) y*F (put a y) := by
  simp only [liftKernel,FiniteKernel.push,mapKernel,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp

/-- Before saturation, the finite lifted chain has exactly the usual
list-path expectation, with the observed prefix retained. -/
theorem prefix_expectation (C : FiniteChain X) (N n : ℕ)
    (a : PathState X N) (hn : a.1.val+n≤N) (F : List X → ℝ) :
    (∑ b,((liftKernel C.kernel pathRead pathPut).power n).P a b*F (historyPrefix b))=
      C.pathExpectation n (pathRead a) (fun l => F ((historyPrefix a).dropLast++l)) := by
  induction n generalizing a F with
  | zero =>
    simp only [FiniteKernel.power,FiniteKernel.identity,FiniteChain.pathExpectation,
      ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,prefix_end]
  | succ n ih =>
    have ha : a.1.val<N := by omega
    rw [power_expectation_succ,lift_expectation]
    change (∑ y,C.P (pathRead a) y*
      (∑ b,((liftKernel C.kernel pathRead pathPut).power n).P (pathPut a y) b*F (historyPrefix b)))=_
    calc
      _ = ∑ y,C.P (pathRead a) y*
          C.pathExpectation n (pathRead (pathPut a y))
            (fun l => F ((historyPrefix (pathPut a y)).dropLast++l)) := by
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        apply ih
        rw [position_put a y ha]
        omega
      _ = C.pathExpectation (n+1) (pathRead a) (fun l => F ((historyPrefix a).dropLast++l)) := by
        simp only [read_put,prefix_put a _ ha,List.dropLast_concat,FiniteChain.pathExpectation]
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        apply congrArg (C.pathExpectation n y)
        funext l
        simpa only [List.append_assoc,List.singleton_append] using
          congrArg (fun xs => F (xs++l)) (prefix_end a).symm

theorem initial_prefix_expectation (C : FiniteChain X) (N : ℕ) (x : X) (F : List X → ℝ) :
    (∑ b,((liftKernel C.kernel pathRead pathPut).power N).P (pathInitial N x) b*F (historyPrefix b))=
      C.pathExpectation N x F := by
  have h := prefix_expectation C N N (pathInitial N x) (by simp [pathInitial]) F
  rw [prefix_initial] at h
  simpa only [List.dropLast_singleton,List.nil_append,pathRead,pathInitial] using h

end

end ContingencyTables.CompanionPhaseTrajectory

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma correctionExponent_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    (correctionExponent A R C a z K hK f:ℝ)=
      (gridExponent A R C a z (integerBin A K hK f):ℝ)-
        (a:ℝ)/height A C*D A R C z (integerPoint A C f) := by
  simp only [correctionExponent,Rat.cast_sub,Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,
    rationalHeight_cast,rationalD_cast,rationalIntegerPoint_cast]

/-- The exponent passed to numerical approximation is a bounded rational,
although the original capacities may be arbitrarily large. -/
theorem correctionExponent_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    -2 ≤ correctionExponent A R C a z K hK f ∧ correctionExponent A R C a z K hK f ≤ 2 := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hd := exponent_change A R C a hCR (Nat.cast_nonneg _) haHR z
    (realCorner (integerBin A K hK f)) (integerPoint A C f) 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using integerPoint_distance A C K hK hB f i)
  have he := gridExponent_eq_floor A R C a z (integerBin A K hK f)
  have hlo := Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  have hhi := Int.lt_floor_add_one ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  rw [←he] at hlo hhi
  have hbounds : (-2:ℝ) ≤ (correctionExponent A R C a z K hK f:ℝ) ∧
      (correctionExponent A R C a z K hK f:ℝ) ≤ 2 := by
    rw [correctionExponent_cast]
    simp only [Int.cast_natCast] at hlo hhi
    rcases abs_le.mp hd with ⟨hl,hu⟩
    constructor <;> linarith
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

lemma correction_eq_population_power (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    correction A R C a z K hK f=(rationalPopulation A K hK f:ℝ)*
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
  have hV : gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(-(gridExponent A R C a z (integerBin A K hK f):ℝ)) := by
    unfold gridWeight V DenseWeights.binWeight
    rw [←gridExponent_eq_floor]
    simp only [Int.cast_natCast]
  have hr : rho A R C a z (integerPoint A C f)/gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
    rw [hV,correctionExponent_cast]
    unfold rho DenseWeights.density
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  unfold correction
  rw [mul_div_assoc,hr]
  congr 1
  simp only [rationalPopulation,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]

/-- A deterministic pointwise relative-error guarantee for the actual
rational correction returned on every integer assignment. -/
theorem computedCorrection_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (f : FreeIndex A.small A.T A.b) :
    |(computedCorrection A R C a z K hK sigma f:ℝ)-correction A R C a z K hK f| ≤
      (sigma:ℝ)*correction A R C a z K hK f := by
  have hb := correctionExponent_bounds A R C a hC haH z K hK hB f
  have he := PowerOfTwoApproximation.approximate_error _ sigma hb.1 hb.2 hsigma
  have hp : (0:ℝ) ≤ rationalPopulation A K hK f := by
    exact_mod_cast (rationalPopulation_positive A K hK f).le
  rw [correction_eq_population_power]
  simp only [computedCorrection,Rat.cast_mul]
  rw [←mul_sub,abs_mul,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (by ring)

/-- Positivity and a uniform range hold on all executions, independently
of the statistical event used by the estimator. -/
theorem computedCorrection_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (f : FreeIndex A.small A.T A.b) :
    (1/16:ℝ) ≤ computedCorrection A R C a z K hK sigma f ∧
      (computedCorrection A R C a z K hK sigma f:ℝ) ≤ 8 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hb := correction_bounds A R C a (by exact_mod_cast hC) (Nat.cast_nonneg _) haHR z K hK hW hB f
  have he := computedCorrection_error A R C a hC haH z K hK hB sigma hsigma f
  have hsR : (sigma:ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hsigmaHalf
  have hprod : (sigma:ℝ)*correction A R C a z K hK f ≤ (1/2)*correction A R C a z K hK f :=
    mul_le_mul_of_nonneg_right hsR (by linarith [hb.1])
  rcases abs_le.mp he with ⟨hl,hu⟩
  constructor <;> nlinarith

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

lemma rationalRatioObservable_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalRatioObservable A R C a z v:ℝ)=ratioObservable A R C a z v := by
  simp only [rationalRatioObservable,Rat.cast_div,rationalGridWeight_cast,Nat.cast_add,
    Nat.cast_one,ratioObservable]

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

lemma ratioSample_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) :
    (ratioSample A R C a z v n bits:ℝ)=
      ratioObservable A R C a z (wordWalk (oracleBitStep A R C a z) v n bits) :=
  rationalRatioObservable_cast A R C a z _

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorRange
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Output range on every execution of the finite-word estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma observed_ratio_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) (a : Fin j) :
    1/2 ≤ (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ) ∧
      (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ) ≤ 1 := by
  apply rationalAverage_bounds _ _ (sampleCount_positive j delta failure hd hf)
  intro bits
  rw [ratioSample_cast]
  exact ratioObservable_bounds A R C (by exact_mod_cast hC) a.val z hz hB.le _

lemma observed_correction_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1)
    (hf : 0 < failure) (v : Grid (I := Fin (dimension A)) K)
    (draws : EstimatorInput A C K j delta failure) :
    1/16 ≤ (observedFactor A R C z K hK hW j delta failure v draws none:ℝ) ∧
      (observedFactor A R C z K hK hW j delta failure v draws none:ℝ) ≤ 8 := by
  apply rationalAverage_bounds _ _ (sampleCount_positive j delta failure hd hf)
  intro bits
  apply computedCorrection_bounds A R C j hC hj z K (by omega) hW hB (roundingTolerance delta)
  · unfold roundingTolerance
    positivity
  · unfold roundingTolerance
    linarith

/-- These bounds hold for every Boolean input, including executions on
which the empirical averages are statistically inaccurate. -/
theorem estimateValue_range (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤ (estimateValue A R C z K hK hW j delta failure v draws:ℝ) ∧
      (estimateValue A R C z K hK hW j delta failure v draws:ℝ) ≤ 8*assignmentCount A := by
  let r := fun a : Fin j => (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ)
  let q := (observedFactor A R C z K hK hW j delta failure v draws none:ℝ)
  have hr := observed_ratio_bounds A R C hC z hz K hK hW hB j delta failure hd hf v draws
  have hq := observed_correction_bounds A R C hC z K hK hW hB j hj delta failure hd hd1 hf v draws
  have hrlow : (1/2:ℝ)^j ≤ ∏ a,r a := by
    have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun _ _ => by norm_num : ∀ a : Fin j,a∈Finset.univ → (0:ℝ) ≤ 1/2)
      (fun a _ => (hr a).1)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  have hrup : (∏ a,r a) ≤ 1 := by
    have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun a _ => show (0:ℝ) ≤ r a from (by have h := (hr a).1; linarith)) (fun a _ => (hr a).2)
    simpa only [Finset.prod_const_one] using hh
  have hr0 : (0:ℝ) ≤ ∏ a,r a := Finset.prod_nonneg (fun a _ => by have h := (hr a).1; linarith)
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith [hq.1]
  have hlow : (1/16:ℝ)*(1/2:ℝ)^j ≤ q*(∏ a,r a) :=
    mul_le_mul hq.1 hrlow (by positivity) hq0
  have hupp : q*(∏ a,r a) ≤ 8 := by
    calc
      _ ≤ 8*1 := mul_le_mul hq.2 hrup hr0 (by norm_num)
      _ = _ := by norm_num
  have hMf : (0:ℝ) ≤ assignmentCount A := Nat.cast_nonneg _
  have he : (estimateValue A R C z K hK hW j delta failure v draws:ℝ)=
      (assignmentCount A:ℝ)*(q*∏ a,r a) := by
    simp only [estimateValue,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod,Fintype.prod_option]
    rfl
  rw [he]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlow hMf
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hupp hMf
    nlinarith

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

theorem wordEstimate_range (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) ∧
    (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) ≤ 8*assignmentCount A :=
  estimateValue_range A R C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
    (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf v _

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

/-- Amplification also preserves the proved range on every word,
including statistically unsuccessful words. -/
theorem medianEstimate_range (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ∧
    (medianEstimate A R C z K hK hW j epsilon delta v bits:ℝ) ≤ 8*assignmentCount A := by
  let samples := List.ofFn (fun i : Fin (repetitionCount delta) =>
    wordEstimate A R C z K hK hW j (epsilon/2) 1 v
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i))
  have hmem := rationalMedian_mem samples (by
    dsimp only [samples]
    rw [List.length_ofFn]
    exact repetitionCount_pos delta)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hmem
  have hr := wordEstimate_range A R C hC z hz K hK hW hB j hj (epsilon/2) 1
    (by positivity) (by linarith) (by norm_num) v
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i)
  change _ ≤ (rationalMedian samples:ℝ) ∧ (rationalMedian samples:ℝ) ≤ _
  rw [←hi]
  exact hr


end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWeightOracle
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

lemma evaluate_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : 0 < evaluate A R C K hK hW j xi v S bits := by
  have hr := (RootedOracleDensity.medianEstimate_range A R C hC (profile A S) (profile_inBox A S)
    K hK hW hB j hj xi xi hx0 hx1 v bits).1
  have hc : (0:ℝ) < assignmentCount A := by exact_mod_cast assignmentCount_positive A
  have hm : (0:ℚ) < RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits := by
    exact_mod_cast lt_of_lt_of_le (by positivity : (0:ℝ) < (assignmentCount A:ℝ)*(1/2:ℝ)^j/16) hr
  exact mul_pos hm (factorialRatio_positive A S)

/-- Every query at the actual labelled state uses a fresh bounded word.
Only PL and finite Cheeger remain in the evaluation guarantee. -/
theorem evaluate_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    1-(xi:ℝ) ≤ uniformAverage (fun bits : WeightWord A C K j xi =>
      if accurateCall A R C K j hK hW xi v S bits then (1:ℝ) else 0) := by
  unfold accurateCall
  have hs := RootedOracleDensity.medianEstimate_success A R C hC (profile A S) (profile_inBox A S)
    K hK hW hB j hj xi xi hx0 hx1 hx0 hPL hCheeger v
  apply hs.trans
  apply uniformAverage_mono
  intro bits
  by_cases hg : (1-(xi:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S) ≤
      (RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits:ℝ) ∧
    (RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits:ℝ) ≤
      (1+(xi:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) (profile A S)
  · have hf : (0:ℝ) ≤ factorialRatio A S := by exact_mod_cast (factorialRatio_positive A S).le
    have hlo := mul_le_mul_of_nonneg_right hg.1 hf
    have hhi := mul_le_mul_of_nonneg_right hg.2 hf
    have ho : (1-(xi:ℝ))*RootedAnnealing.weight A R j S ≤ (evaluate A R C K hK hW j xi v S bits:ℝ) ∧
        (evaluate A R C K hK hW j xi v S bits:ℝ) ≤ (1+(xi:ℝ))*RootedAnnealing.weight A R j S := by
      rw [weight_source A R C hC j S]
      simpa only [evaluate,Rat.cast_mul,mul_assoc] using And.intro hlo hhi
    simp only [hg,ho,le_refl]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

end

end ContingencyTables.RootedWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseOracleError
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error of actual selected-root calls in a rational phase update -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv failure_of_success
  independent_pair_failure )
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma accurateCall_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi =>
      if ¬accurateCall A R C K j hK hW xi v S bits then (1:ℝ) else 0) ≤ (xi:ℝ) := by
  have hs := evaluate_success A R C hC K hK hW hB j hj xi hx0 hx1 hPL hCheeger v S
  exact @failure_of_success (WeightWord A C K j xi) inferInstance inferInstance
    (accurateCall A R C K j hK hW xi v S) (xi:ℝ) hs

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root weight calls control the Metropolis decision -/

namespace ContingencyTables.RootedOracleAcceptance

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open RootedPhaseWords CommonBasesFPRAS GridBoundary FairBits TwoLiftStates
open CompanionPhaseWords (independent_pair_failure)
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section

private lemma ratio_linear_bounds {u v uh vh e : ℝ}
    (hu : 0 < u) (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1/4)
    (huh : (1-e)*u ≤ uh ∧ uh ≤ (1+e)*u)
    (hvh : (1-e)*v ≤ vh ∧ vh ≤ (1+e)*v) :
    (1-4*e)*(v/u) ≤ vh/uh ∧ vh/uh ≤ (1+4*e)*(v/u) := by
  have huh0 := AnnealingMultipliers.empirical_positive hu he1 huh.1
  have ha0 : 0 ≤ 1-4*e := by linarith
  have hp0 : 0 ≤ 1+4*e := by linarith
  have hx : 0 < uh/u := div_pos huh0 hu
  have hlo : 1-e ≤ uh/u := (le_div_iff₀ hu).mpr huh.1
  have hhi : uh/u ≤ 1+e := (div_le_iff₀ hu).mpr huh.2
  have hyl : 1-e ≤ vh/v := (le_div_iff₀ hv).mpr hvh.1
  have hyu : vh/v ≤ 1+e := (div_le_iff₀ hv).mpr hvh.2
  have hnorm : 1-4*e ≤ (vh/v)/(uh/u) ∧ (vh/v)/(uh/u) ≤ 1+4*e := by
    constructor
    · rw [le_div_iff₀ hx]
      have hm := mul_le_mul_of_nonneg_left hhi ha0
      nlinarith [sq_nonneg e]
    · rw [div_le_iff₀ hx]
      have hm := mul_le_mul_of_nonneg_left hlo hp0
      have he : 0 ≤ 2*e-4*e^2 := by nlinarith
      nlinarith
  have hid : ((vh/v)/(uh/u))*(v/u)=vh/uh := by
    field_simp [hu.ne',hv.ne',huh0.ne']
  constructor
  · simpa only [hid] using mul_le_mul_of_nonneg_right hnorm.1 (div_pos hv hu).le
  · simpa only [hid] using mul_le_mul_of_nonneg_right hnorm.2 (div_pos hv hu).le

private lemma min_one_stability {a r s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (h : (1-a)*r ≤ s ∧ s ≤ (1+a)*r) : |min 1 s-min 1 r| ≤ a := by
  by_cases hr : r ≤ 1 <;> by_cases hs : s ≤ 1
  · rw [min_eq_right hs,min_eq_right hr,abs_le]
    have hm := mul_nonneg ha0 (sub_nonneg.mpr hr)
    constructor <;> nlinarith
  · rw [min_eq_left (le_of_not_ge hs),min_eq_right hr,abs_le]
    have hm := mul_nonneg ha0 (sub_nonneg.mpr hr)
    constructor <;> nlinarith
  · rw [min_eq_right hs,min_eq_left (le_of_not_ge hr),abs_le]
    have hm := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr (le_of_not_ge hr))
    constructor <;> nlinarith
  · rw [min_eq_left (le_of_not_ge hs),min_eq_left (le_of_not_ge hr)]
    simpa using ha0

variable {I J : Type*} [Fintype I] [Fintype J]

lemma targetWeight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) : targetWeight A R j w S=
      chainWeight pairs (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j) S := by
  rw [targetWeight,rationalMultiplier_cast]
  rfl

lemma multiplier_positive (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) : 0 < rationalMultiplier pairs w S := by
  unfold rationalMultiplier
  split_ifs
  · exact hw _ _
  · norm_num

lemma targetWeight_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) : 0 < targetWeight A R j w S := by
  apply mul_pos _ (RootedAnnealing.weight_positive A R j S)
  exact_mod_cast multiplier_positive A w hw S

lemma evaluatedWeight_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S : Set (Labels A×Bool)) (bits : WeightWord A C K j xi)
    (hg : accurateCall A R C K j hK hW xi v S bits) :
    (1-(xi:ℝ))*targetWeight A R j w S ≤ (evaluatedWeight A R C K j hK hW xi v w S bits:ℝ) ∧
      (evaluatedWeight A R C K j hK hW xi v w S bits:ℝ) ≤ (1+(xi:ℝ))*targetWeight A R j w S := by
  have hm : (0:ℝ) ≤ rationalMultiplier pairs w S := by
    exact_mod_cast (multiplier_positive A w hw S).le
  have hlo := mul_le_mul_of_nonneg_left hg.1 hm
  have hhi := mul_le_mul_of_nonneg_left hg.2 hm
  simpa only [evaluatedWeight,targetWeight,Rat.cast_mul,mul_left_comm,mul_assoc] using And.intro hlo hhi

/-- Relative errors in both weight calls cause an absolute acceptance
error at most four times the call tolerance, even across clipping at 1. -/
theorem acceptance_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi)
    (hS : accurateCall A R C K j hK hW xi v S bits.1)
    (hT : accurateCall A R C K j hK hW xi v T bits.2) :
    |(acceptance A R C K j hK hW xi v w S T bits:ℝ)-targetAcceptance A R j w S T| ≤ 4*(xi:ℝ) := by
  have hb := ratio_linear_bounds (targetWeight_positive A R j w hw S)
    (targetWeight_positive A R j w hw T) (by exact_mod_cast hx0)
    (by
      have h4 : (4:ℝ)*(xi:ℝ) ≤ 1 := by
        exact_mod_cast (show (4:ℚ)*xi ≤ 1 by linarith)
      linarith)
    (evaluatedWeight_bounds A R C K j hK hW xi v w hw S bits.1 hS)
    (evaluatedWeight_bounds A R C K j hK hW xi v w hw T bits.2 hT)
  have hh := min_one_stability (show (0:ℝ) ≤ 4*(xi:ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ)≤4) hx0)
    (show 4*(xi:ℝ) ≤ 1 by exact_mod_cast (show 4*xi ≤ (1:ℚ) by linarith)) hb
  simpa only [acceptance,targetAcceptance,Rat.cast_min,Rat.cast_one,Rat.cast_div] using hh

lemma acceptance_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi) :
    0 ≤ acceptance A R C K j hK hW xi v w S T bits ∧
      acceptance A R C K j hK hW xi v w S T bits ≤ 1 := by
  have hpos (X : Set (Labels A×Bool)) (b : WeightWord A C K j xi) :
      0 < evaluatedWeight A R C K j hK hW xi v w X b :=
    mul_pos (multiplier_positive A w hw X)
      (evaluate_positive A R C hC K hK hW hB j hj xi hx0 hx1 v X b)
  exact ⟨le_min (by norm_num) (div_pos (hpos T bits.2) (hpos S bits.1)).le,min_le_left _ _⟩

lemma targetAcceptance_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool)) :
    0 ≤ targetAcceptance A R j w S T ∧ targetAcceptance A R j w S T ≤ 1 := by
  exact ⟨le_min (by norm_num)
    (div_pos (targetWeight_positive A R j w hw T) (targetWeight_positive A R j w hw S)).le,
    min_le_left _ _⟩

/-- This is the rounded acceptance probability of the implemented
decision, averaged over its two fresh independent weight-query words. -/
theorem average_acceptance_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (S T : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K j xi =>
      |(rationalThresholdMass k (acceptance A R C K j hK hW xi v w S T bits):ℝ)-
        targetAcceptance A R j w S T|) ≤ 6*(xi:ℝ)+1/(2:ℝ)^k := by
  let goodS := accurateCall A R C K j hK hW xi v S
  let goodT := accurateCall A R C K j hK hW xi v T
  have hx1' : xi < 1 := by linarith
  have hbad : uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K j xi =>
      if ¬(goodS bits.1 ∧ goodT bits.2) then (1:ℝ) else 0) ≤ (xi:ℝ)+(xi:ℝ) := by
    have hs := accurateCall_failure A R C hC K j hK hW hB hj xi hx0 hx1' hPL hCheeger v S
    have ht := accurateCall_failure A R C hC K j hK hW hB hj xi hx0 hx1' hPL hCheeger v T
    exact @independent_pair_failure (WeightWord A C K j xi) (WeightWord A C K j xi)
      inferInstance inferInstance inferInstance inferInstance goodS goodT (xi:ℝ) (xi:ℝ) hs ht
  have hpoint (bits : WeightWord A C K j xi × WeightWord A C K j xi) :
      |(rationalThresholdMass k (acceptance A R C K j hK hW xi v w S T bits):ℝ)-targetAcceptance A R j w S T| ≤
        (4*(xi:ℝ)+1/(2:ℝ)^k)+(if ¬(goodS bits.1 ∧ goodT bits.2) then 1 else 0) := by
    let q := acceptance A R C K j hK hW xi v w S T bits
    have hq := acceptance_bounds A R C hC K j hK hW hB hj xi hx0 hx1' v w hw S T bits
    have hr := rationalThreshold_error k q hq.1
    have hnon : (0:ℝ) ≤ (q:ℝ)-(rationalThresholdMass k q:ℝ) := by exact_mod_cast sub_nonneg.mpr hr.2.1
    have hround : |(rationalThresholdMass k q:ℝ)-(q:ℝ)| ≤ 1/(2:ℝ)^k := by
      rw [abs_sub_comm,abs_of_nonneg hnon]
      have hc : ((q-rationalThresholdMass k q:ℚ):ℝ) ≤ ((1/(2:ℚ)^k:ℚ):ℝ) :=
        Rat.cast_le.mpr hr.2.2.le
      simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc
    have htriangle := abs_add_le ((rationalThresholdMass k q:ℝ)-(q:ℝ))
      ((q:ℝ)-targetAcceptance A R j w S T)
    have hcancel : (rationalThresholdMass k q:ℝ)-(q:ℝ)+((q:ℝ)-targetAcceptance A R j w S T)=
        (rationalThresholdMass k q:ℝ)-targetAcceptance A R j w S T := by ring
    rw [hcancel] at htriangle
    by_cases hg : goodS bits.1 ∧ goodT bits.2
    · have herr := acceptance_error A R C K j hK hW xi hx0.le hx1 v w hw S T bits hg.1 hg.2
      simpa [q,hg,add_comm] using htriangle.trans (add_le_add hround herr)
    · have ht := targetAcceptance_bounds A R j w hw S T
      have hdiff : |(q:ℝ)-targetAcceptance A R j w S T| ≤ 1 := by
        have hqR : (0:ℝ) ≤ q ∧ (q:ℝ) ≤ 1 := by exact_mod_cast hq
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      simp only [hg,not_false_eq_true,ite_true, if_true]
      have hxR : (0:ℝ) ≤ xi := by exact_mod_cast hx0.le
      linarith [htriangle]
  have hh := uniformAverage_mono _ _ hpoint
  rw [uniformAverage_add,uniformAverage_const] at hh
  linarith

end
end ContingencyTables.RootedOracleAcceptance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanPhase
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite-word Metropolis steps using the selected-root oracle -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open CompanionBooleanPhase (State proposal proposal_mass proposalBits proposal_codes stepBits stepWordEquiv)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- A nontrivial move uses exactly its proposal code and the fresh
acceptance experiment. Failed codes and the independent holding bit
contribute only to the diagonal. -/
theorem step_eq_iff (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : State A) (hST : S ≠ T) (bits : Fin (stepBits A C K j k xi) → Bool) :
    step A R C K j k hK hW xi v w S bits=T ↔
      (stepWordEquiv A C K j k xi bits).1 0=false ∧
      proposal A S (stepWordEquiv A C K j k xi bits).2.1=some T ∧
      rationalThresholdAccept k
        (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2 := by
  dsimp only [step]
  generalize stepWordEquiv A C K j k xi bits = b
  cases b.1 0 with
  | true => simp [hST]
  | false =>
    cases proposal A S b.2.1 with
    | none => simp [hST]
    | some U =>
      by_cases hUT : U=T
      · subst U
        simp [hST]
      · by_cases ha : rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val U.val b.2.2.1) b.2.2.2
        · simp [hUT,ha]
        · simp [hST,hUT,ha]

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposal_mass proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

private lemma word_probability {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    [DecidableEq Y] (draw : X → Y) (y : Y) :
    uniformAverage (fun x => if draw x=y then (1:ℝ) else 0)=
      ((mapLaw (uniformLaw (α := X)) draw).mass y:ℝ) := by
  rw [word_expectation draw (fun z => if z=y then (1:ℝ) else 0)]
  simp [expectation]

private lemma independent_decision {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : A → Prop) (Q : B → Prop) (R : C → D → Prop)
    [DecidablePred P] [DecidablePred Q] [∀ c d,Decidable (R c d)] :
    uniformAverage (fun z : A×(B×(C×D)) =>
      if P z.1 ∧ Q z.2.1 ∧ R z.2.2.1 z.2.2.2 then (1:ℝ) else 0)=
      uniformAverage (fun a => if P a then (1:ℝ) else 0)*
        uniformAverage (fun b => if Q b then (1:ℝ) else 0)*
        uniformAverage (fun c => uniformAverage (fun d => if R c d then (1:ℝ) else 0)) := by
  have he (z : A×(B×(C×D))) :
      (if P z.1 ∧ Q z.2.1 ∧ R z.2.2.1 z.2.2.2 then (1:ℝ) else 0)=
        (if P z.1 then 1 else 0)*
          ((if Q z.2.1 then 1 else 0)*(if R z.2.2.1 z.2.2.2 then 1 else 0)) := by
    by_cases hp : P z.1 <;> by_cases hq : Q z.2.1 <;>
      by_cases hr : R z.2.2.1 z.2.2.2 <;> simp [hp,hq,hr]
  have hs : (∑ a : A,∑ b : B,∑ c : C,∑ d : D,
      (if P a then (1:ℝ) else 0)*((if Q b then 1 else 0)*(if R c d then 1 else 0)))=
      (∑ a : A,if P a then (1:ℝ) else 0)*(∑ b : B,if Q b then (1:ℝ) else 0)*
        (∑ c : C,∑ d : D,if R c d then (1:ℝ) else 0) := by
    symm
    simp only [Finset.sum_mul,mul_assoc]
    simp only [Finset.mul_sum]
  simp only [he,uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.sum_div]
  rw [hs]
  ring

private lemma lazy_probability :
    uniformAverage (fun b : Fin 1 → Bool => if b 0=false then (1:ℝ) else 0)=1/2 := by
  rw [uniformAverage_fin_succ]
  simp only [Fin.cons_zero,uniformAverage_const]
  norm_num [uniformAverage]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every nontrivial output probability factors into its lazy bit,
unique neighbor code, and the actual rounded two-oracle acceptance. -/
theorem transition_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi<1)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (S T : State A) (hST : S≠T) :
    ((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)=
      if ExchangeAdjacent S.val T.val then
        (1/(2*(2:ℝ)^proposalBits A))*
          uniformAverage (fun b : WeightWord A C K j xi×WeightWord A C K j xi =>
            (rationalThresholdMass k
              (acceptance A R C K j hK hW xi v w S.val T.val b):ℝ))
      else 0 := by
  have hp : uniformAverage (fun b : Fin (proposalBits A) → Bool =>
      if proposal A S b=some T then (1:ℝ) else 0)=
        if ExchangeAdjacent S.val T.val then 1/(2:ℝ)^proposalBits A else 0 := by
    rw [word_probability,proposal_mass]
    split_ifs <;> simp
  have ha (b : WeightWord A C K j xi×WeightWord A C K j xi) :
      uniformAverage (fun coin : Fin k → Bool =>
        if rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b) coin then (1:ℝ) else 0)=
        (rationalThresholdMass k
          (acceptance A R C K j hK hW xi v w S.val T.val b):ℝ) := by
    exact rationalThreshold_expectation k _
      (acceptance_bounds A R C hC K j hK hW hB hj xi hx0 hx1 v w hw S.val T.val b).1
      (acceptance_bounds A R C hC K j hK hW hB hj xi hx0 hx1 v w hw S.val T.val b).2
  calc
    _ = uniformAverage (fun bits => if step A R C K j k hK hW xi v w S bits=T then (1:ℝ) else 0) :=
      (word_probability _ T).symm
    _ = uniformAverage (fun b : (Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
        ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))) =>
      if b.1 0=false ∧ proposal A S b.2.1=some T ∧
        rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
      then (1:ℝ) else 0) := by
        simp_rw [step_eq_iff A R C K j k hK hW xi v w S T hST]
        have he := uniformAverage_equiv (stepWordEquiv A C K j k xi)
          (fun b : (Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
            ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))) =>
            if b.1 0=false ∧ proposal A S b.2.1=some T ∧
              rationalThresholdAccept k
                (acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
            then (1:ℝ) else 0)
        convert he using 1
        all_goals try with_reducible_and_instances rfl
    _ = _ := by
      rw [independent_decision (fun b : Fin 1 → Bool => b 0=false)
        (fun b : Fin (proposalBits A) → Bool => proposal A S b=some T)
        (fun b coin => rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b) coin),lazy_probability,hp]
      simp_rw [ha]
      split_ifs <;> ring

theorem target_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S T : State A) (hST : S≠T) :
    (targetChain A R j hp w hw).P S T=
      if ExchangeAdjacent S.val T.val then
        (1/(2*(2:ℝ)^proposalBits A))*targetAcceptance A R j w S.val T.val else 0 := by
  have hn : (Fintype.card (Labels A):ℝ)≠0 := by exact_mod_cast hp.ne'
  have hs := targetWeight_positive A R j w hw S.val
  have hm : targetAcceptance A R j w S.val T.val=
      min (targetWeight A R j w S.val) (targetWeight A R j w T.val)/targetWeight A R j w S.val := by
    unfold targetAcceptance
    rw [←min_div_div_right hs.le,div_self hs.ne']
  dsimp only [targetChain,FiniteChainSlowdown.slow,referenceChain,metropolisChain,FiniteChain.ofMoves]
  simp only [hST,ite_false,add_zero,metropolisMove,PairedLabels.length]
  by_cases ha : ExchangeAdjacent S.val T.val
  · rw [ite_eq_left ha,ite_eq_left ha]
    simp only [←targetWeight_eq,slowdown,hm]
    field_simp [hn,hs.ne']
  · simp [ha]

private lemma distance_le_off_diagonal {X : Type*} [Fintype X] [DecidableEq X]
    (p q : X → ℝ) (x : X) (hmass : ∑ y,p y=∑ y,q y) :
    distance p q≤∑ y∈Finset.univ.erase x,|p y-q y| := by
  have ht : (∑ y∈Finset.univ.erase x,(p y-q y))+(p x-q x)=0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ x),Finset.sum_sub_distrib,hmass,sub_self]
  have hd : p x-q x= -(∑ y∈Finset.univ.erase x,(p y-q y)) := by linarith
  have hb := Finset.abs_sum_le_sum_abs (fun y => p y-q y) (Finset.univ.erase x)
  have he := Finset.sum_erase_add (Finset.univ : Finset X) (fun y => |p y-q y|)
    (Finset.mem_univ x)
  rw [hd,abs_neg] at he
  unfold distance
  linarith

private lemma average_abs {X : Type*} [Fintype X] (f : X → ℝ) :
    |uniformAverage f|≤uniformAverage (fun x => |f x|) := by
  unfold uniformAverage
  rw [abs_div,abs_of_nonneg (show (0:ℝ)≤Fintype.card X from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs f Finset.univ)
    (Nat.cast_nonneg _)

/-- The complete transition row loses at most half the acceptance error.
The diagonal is controlled by conservation of probability, rather than
an additional independent error assumption. -/
theorem row_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (S : State A) :
    distance (fun T => ((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ))
      ((targetChain A R j hp w hw).P S)≤(6*(xi:ℝ)+1/(2:ℝ)^k)/2 := by
  let e : ℝ := 6*(xi:ℝ)+1/(2:ℝ)^k
  let a : ℝ := 1/(2*(2:ℝ)^proposalBits A)
  have he : 0≤e := by dsimp only [e]; positivity
  have ha : 0≤a := by dsimp only [a]; positivity
  have hpnt (T : State A) (hST : S≠T) :
      |((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)-
        (targetChain A R j hp w hw).P S T|≤
          if ExchangeAdjacent S.val T.val then a*e else 0 := by
    rw [transition_mass A R C hC K j k hK hW hB hj xi hx0
      (by linarith) v w hw S T hST,target_mass A R j hp w hw S T hST]
    by_cases h : ExchangeAdjacent S.val T.val
    · simp only [h,ite_true, if_true]
      rw [←mul_sub,abs_mul,abs_of_nonneg ha]
      apply mul_le_mul_of_nonneg_left _ ha
      rw [←uniformAverage_sub_const]
      exact (average_abs _).trans
        (average_acceptance_error A R C hC K j k hK hW hB hj xi hx0 hx1
          hPL hCheeger v w hw S.val T.val)
    · simp [h]
  have hm : (∑ T,((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ))=
      ∑ T,(targetChain A R j hp w hw).P S T := by
    rw [(targetChain A R j hp w hw).stochastic]
    exact_mod_cast (transitionLaw A R C K j k hK hW xi v w S).total
  have hc : ((Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val)).card:ℝ)≤
      (2:ℝ)^proposalBits A := by
    have hh := proposal_codes A S
    rw [Fintype.card_subtype] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ T∈Finset.univ.erase S,
        |((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)-
          (targetChain A R j hp w hw).P S T| := distance_le_off_diagonal _ _ S hm
    _ ≤ ∑ T∈Finset.univ.erase S,
        if ExchangeAdjacent S.val T.val then a*e else 0 := by
      apply Finset.sum_le_sum
      intro T hT
      exact hpnt T (Finset.mem_erase.mp hT).1.symm
    _ ≤ ∑ T : State A,if ExchangeAdjacent S.val T.val then a*e else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro T _ _
      split_ifs <;> positivity
    _ = ((Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val)).card:ℝ)*(a*e) := by
      rw [←Finset.sum_filter]
      simp
    _ ≤ (2:ℝ)^proposalBits A*(a*e) := mul_le_mul_of_nonneg_right hc (mul_nonneg ha he)
    _ = e/2 := by dsimp only [a]; field_simp

/-- The error controls the whole recorded phase history, not merely its
last state. Every step uses a disjoint fresh oracle/acceptance word. -/
theorem path_distance_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N n : ℕ) (S : State A) :
    distance (X := PathState (State A) N)
      (fun b : PathState (State A) N => ((pathLaw A R C K j k N n hK hW xi v w S).mass b:ℝ))
      (targetPathMass A R j hp w hw N n S)≤n*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  unfold pathLaw targetPathMass
  apply walk_distance
  intro a
  apply (lifted_row_distance (transitionLaw A R C K j k hK hW xi v w)
    (targetChain A R j hp w hw).kernel
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T) a).trans
  exact row_distance A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw (pathRead a)

theorem recordedWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A R C K j k N n hK hW xi v w S)=
      walkLaw (liftRational (transitionLaw A R C K j k hK hW xi v w) pathRead pathPut)
        (pathInitial N S) n := by
  unfold recordedWalk
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=wordWalkLaw
          (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
          (pathInitial N S) n from rfl,wordWalkLaw_eq]
  apply congrArg (fun Q => walkLaw Q (pathInitial N S) n)
  funext a
  exact (mapLaw_comp (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A R C K j k hK hW xi v w (pathRead a)) (pathPut a)).symm

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseTrajectory
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root Boolean history has the exact source path comparison -/

namespace ContingencyTables.RootedPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation RootedBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseTrajectory (historyPrefix initial_prefix_expectation)
open scoped BigOperators Classical

noncomputable section

private lemma event_le_distance {Y : Type*} [Fintype Y] (p q : Y → ℝ)
    (hmass : ∑ y,p y=∑ y,q y) (E : Y → Prop) :
    (∑ y,p y*(if E y then 1 else 0))≤
      (∑ y,q y*(if E y then 1 else 0))+distance p q := by
  have h := distance_event p q hmass (Finset.univ.filter E)
  rw [Finset.sum_filter,Finset.sum_filter] at h
  simp only [mul_ite,mul_one,mul_zero]
  linarith [le_abs_self ((∑ y,if E y then p y else 0)-(∑ y,if E y then q y else 0))]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every event of the actual observed Boolean trajectory is bounded by
the source list-path event plus one proved row error per transition. -/
theorem recorded_event_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (recordedWalk A R C K j k N N hK hW xi v w S bits)) then (1:ℝ) else 0)≤
      (targetChain A R j hp w hw).pathExpectation N S (fun l => if E l then 1 else 0)+
        N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let p := pathLaw A R C K j k N N hK hW xi v w S
  let q := targetPathMass A R j hp w hw N N S
  have hq : ∑ b,q b=1 := by
    have hh := initial_prefix_expectation (targetChain A R j hp w hw) N S (fun _ => (1:ℝ))
    simpa only [targetPathMass,q,mul_one,FiniteChain.pathExpectation_const] using hh
  have hpq : (∑ b,(p.mass b:ℝ))=∑ b,q b := by rw [hq]; exact_mod_cast p.total
  have he := event_le_distance (fun b => (p.mass b:ℝ)) q hpq (fun b => E (historyPrefix b))
  have hd := path_distance_bound A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N N S
  have hword := word_expectation (recordedWalk A R C K j k N N hK hW xi v w S)
    (fun b => if E (historyPrefix b) then (1:ℝ) else 0)
  rw [recordedWalk_law] at hword
  change _=∑ b,(p.mass b:ℝ)*(if E (historyPrefix b) then 1 else 0) at hword
  have htarget := initial_prefix_expectation (targetChain A R j hp w hw) N S
    (fun l => if E l then (1:ℝ) else 0)
  change (∑ b,q b*(if E (historyPrefix b) then 1 else 0))=_ at htarget
  rw [hword]
  exact he.trans (by rw [htarget]; exact add_le_add_right hd _)

end
end ContingencyTables.RootedPhaseTrajectory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedArithmeticStep
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed coordinate proposals for the selected-root phase walk -/

namespace ContingencyTables.RootedArithmeticStep

open CommonBasesFPRAS FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open RootedBooleanPhase RealKernelApproximation
open CompanionBooleanPhase (State stepBits proposalBits stepWordEquiv)
open CompanionArithmeticStep (RestWord)
open scoped BigOperators Classical

noncomputable section

private lemma word_finish_law {B P Q X Z : Type*}
    [Fintype B] [Fintype P] [Fintype Q] [Fintype X] [Fintype Z]
    [Nonempty B] [Nonempty P] [Nonempty Q] [DecidableEq X] [DecidableEq Z]
    (E : B ≃ P×Q) (draw : P → X) (finish : X → Q → Z) :
    mapLaw (uniformLaw (α := B)) (fun b => finish (draw (E b).1) (E b).2)=
      bindLaw (mapLaw (uniformLaw (α := P)) draw)
        (fun x => mapLaw (uniformLaw (α := Q)) (finish x)) := by
  have he := map_equiv E (uniformLaw (α := B)) (fun b : P×Q => finish (draw b.1) b.2)
  rw [uniform_equiv,←uniform_product] at he
  exact he.symm.trans (mapLaw_product_finish _ _ draw finish)

variable {I J : Type} [Fintype I] [Fintype J]

private lemma source_step_eq_finish (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    (fun bits => finish A R C K j k hK hW xi v w S
      (CompanionBooleanPhase.proposal A S (wordSplit A C K j k xi bits).1)
      (wordSplit A C K j k xi bits).2)=
      RootedBooleanPhase.step A R C K j k hK hW xi v w S := by
  funext bits
  simp only [finish,wordSplit,regroup,RootedBooleanPhase.step,Equiv.trans_apply,Equiv.coe_fn_mk]
  by_cases hlazy : (stepWordEquiv A C K j k xi bits).1 0 = true
  · simp only [hlazy,ite_true, if_true]
  · simp only [hlazy]
    cases CompanionBooleanPhase.proposal A S
      (stepWordEquiv A C K j k xi bits).2.1 with
    | none => simp only
    | some T =>
      simp only
      by_cases haccept : rationalThresholdAccept k
        (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2
      · simp only [haccept,ite_true, if_true]
      · simp only [haccept,ite_false]

/-- Exact equality of complete one-step laws, including all holding
probability. Weight calls and the acceptance coin have not been reused. -/
theorem step_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
      (step A R C K j k hK hW xi v w S)=
        transitionLaw A R C K j k hK hW xi v w S := by
  have hnew := word_finish_law (wordSplit A C K j k xi)
    (CompanionArithmeticProposal.proposal A S) (finish A R C K j k hK hW xi v w S)
  have hold := word_finish_law (wordSplit A C K j k xi)
    (CompanionBooleanPhase.proposal A S) (finish A R C K j k hK hW xi v w S)
  change mapLaw _ (fun bits => finish A R C K j k hK hW xi v w S
    (CompanionArithmeticProposal.proposal A S (wordSplit A C K j k xi bits).1)
    (wordSplit A C K j k xi bits).2)=_
  rw [hnew,CompanionArithmeticProposal.proposal_law]
  rw [source_step_eq_finish] at hold
  exact hold.symm

theorem recordedWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A R C K j k N n hK hW xi v w S)=
        pathLaw A R C K j k N n hK hW xi v w S := by
  unfold recordedWalk pathLaw
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=
      wordWalkLaw (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n from rfl,wordWalkLaw_eq]
  congr 1
  funext a
  rw [←mapLaw_comp,step_law]
  rfl

end
end ContingencyTables.RootedArithmeticStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTraceWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded first-return words for the selected-root chain -/

namespace ContingencyTables.RootedTraceWords

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase
open RootedPhaseTrajectory CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator firstHit )
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

private lemma arithmetic_event_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0)=
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v w S bits))
      then (1:ℝ) else 0) := by
  have hnew := FiniteLawMoments.word_expectation
    (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  have hold := FiniteLawMoments.word_expectation
    (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v w S)
    (fun a => if E (historyPrefix a) then (1:ℝ) else 0)
  rw [RootedArithmeticStep.recordedWalk_law] at hnew
  rw [RootedBooleanPhase.recordedWalk_law] at hold
  exact hnew.trans hold.symm

theorem arithmetic_recorded_event_bound_oai (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (historyPrefix
        (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))))≤
      (targetChain A R j hp w hw).pathExpectation N S (fun xs => eventIndicator (E xs))+
      N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  exact (arithmetic_event_eq A R C K j k N hK hW xi v w S E).trans_le
    (recorded_event_bound A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N S E)

end
end ContingencyTables.RootedTraceWords

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound_oai := @OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound_oai

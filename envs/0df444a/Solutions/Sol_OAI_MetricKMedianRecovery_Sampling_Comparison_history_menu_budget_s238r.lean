-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:41:43.105164+00:00
-- url     : https://prove2.me/submissions/613fad4c-7920-45d1-8d43-cc8f59d22d71

import Mathlib
import Definitions.Def_Q238L021
import Definitions.Def_Q238L026

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma thirdNormalizer_lt_one (J : ℕ) : thirdNormalizer J < 1 := by
  rw [thirdNormalizer_eq]
  have hh : (0 : ℝ) < (1/2 : ℝ)^J := pow_pos (by norm_num) _
  linarith

lemma menuConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < menuConstant kappa hk := by
  have hM : (0 : ℝ) < firstSize kappa := by
    dsimp [firstSize]
    positivity
  unfold menuConstant
  refine lt_min (div_pos zero_lt_one (mul_pos (by norm_num) hM)) ?_
  exact lt_min (by positivity) (by norm_num)

lemma menuConstant_le_one (kappa : ℝ) (hk : 0 < kappa) : menuConstant kappa hk ≤ 1 := by
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)

lemma first_entry_lower (kappa : ℝ) (hk : 0 < kappa) :
    menuConstant kappa hk ≤ 1/(3*(firstSize kappa : ℝ)) := min_le_left _ _

lemma second_entry_lower (kappa : ℝ) (hk : 0 < kappa) :
    menuConstant kappa hk ≤ 1/(3*((geometricCap kappa hk : ℝ)+1)) :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma third_entry_lower (kappa : ℝ) (hk : 0 < kappa) (J j : ℕ) (hJ : 0 < J) :
    menuConstant kappa hk * (1/2 : ℝ)^j ≤
      (1/3 : ℝ) * ((1/2 : ℝ)^j / thirdNormalizer J) := by
  have hc : menuConstant kappa hk ≤ 1/3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hp : (0 : ℝ) ≤ (1/2 : ℝ)^j := pow_nonneg (by norm_num) _
  have hh : (1/2 : ℝ)^j ≤ (1/2 : ℝ)^j / thirdNormalizer J := by
    apply (le_div_iff₀ (thirdNormalizer_pos hJ)).mpr
    exact mul_le_of_le_one_right hp (thirdNormalizer_lt_one J).le
  exact (mul_le_mul_of_nonneg_right hc hp).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num))

theorem menu_product_budget {ι : Type*} (s : Finset ι) (m : ℕ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (j : ι → ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ s, c*(1/2 : ℝ)^(j i) ≤ p i)
    (hn : s.card ≤ m) (A : ℝ) (hA : (∑ i ∈ s, (j i : ℝ)) ≤ A) :
    c^m * (2 : ℝ)^(-A) ≤ ∏ i ∈ s, p i := by
  have hcp : c^m ≤ c^s.card := pow_le_pow_of_le_one hc.le hc1 hn
  have hsum : (2 : ℝ)^(-A) ≤ (1/2 : ℝ)^(∑ i ∈ s, j i) := by
    rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hprod : c^s.card * (1/2 : ℝ)^(∑ i ∈ s, j i) =
      ∏ i ∈ s, c*(1/2 : ℝ)^(j i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ c^s.card*(1/2 : ℝ)^(∑ i ∈ s, j i) :=
      mul_le_mul hcp hsum (Real.rpow_nonneg (by norm_num) _) (pow_nonneg hc.le _)
    _ = _ := hprod
    _ ≤ _ := Finset.prod_le_prod (fun index _ => mul_nonneg hc.le (pow_nonneg (by norm_num) (j index))) hp

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Ball
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in

lemma ceiling_index_budget {I : Type*} (A : Finset I) (q r : I → ℝ)
    (kappa : ℝ) (m : ℕ) (hk : 0 < kappa) (hA : A.card ≤ m)
    (hq : ∀ i ∈ A, 0 < q i) (hr : ∀ i ∈ A, 0 ≤ r i)
    (hbudget : ∑ i ∈ A, r i/q i ≤ (10/9 : ℝ)*m) :
    (∑ i ∈ A, (Nat.ceil (r i/(kappa*q i)) : ℝ)) ≤ (10/(9*kappa)+1)*m := by
  have hpoint : ∀ i ∈ A, (Nat.ceil (r i/(kappa*q i)) : ℝ) ≤ (r i/q i)/kappa+1 := by
    intro i hi
    have hh := Nat.ceil_lt_add_one_of_gt_neg_one
      (show (-1 : ℝ) < r i/(kappa*q i) by
        have := div_nonneg (hr i hi) (mul_pos hk (hq i hi)).le
        linarith)
    have he : r i/(kappa*q i) = (r i/q i)/kappa := by ring
    rw [he] at hh ⊢
    exact hh.le
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [← Finset.sum_div] at hs
  have hb := div_le_div_of_nonneg_right hbudget hk.le
  have hc : (A.card : ℝ) ≤ m := by exact_mod_cast hA
  calc
    _ ≤ (∑ i ∈ A, r i/q i)/kappa + (A.card : ℝ) := hs
    _ ≤ ((10/9 : ℝ)*m)/kappa + m := add_le_add hb hc
    _ = _ := by ring

end MetricKMedianRecovery.Population

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

lemma correct_initial (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ) :
    C.Correct hD kappa State.initial := by
  simp [Correct, State.initial]

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma correct_lengths (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    s.leaves.length ≤ C.bad.card ∧ s.deleted.card ≤ C.bad.card := by
  have hc : (C.covered s).card = s.leaves.length := by
    rw [covered, List.toFinset_card_of_nodup hs.2.1, List.length_map]
  refine ⟨?_, ?_⟩
  · rw [← hc]
    exact Finset.card_le_card (C.correct_covered_subset hD kappa s hs)
  · rw [← C.nonproxy_card]
    exact Finset.card_le_card hs.1

lemma correct_remove (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (v : V) (hv : v ∈ C.nonproxy) : C.Correct hD kappa (s.remove v) := by
  refine ⟨?_,hs.2⟩
  simpa only [State.remove, Finset.insert_subset_iff] using And.intro hv hs.1

lemma correct_add (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (R : ℝ) (hw : w ∈ D) (hb : C.assign w ∈ C.bad)
    (hnew : C.assign w ∉ C.covered s)
    (hnear : dist w (C.assign w) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign w))
    (hR : 0 < R) (hlow : dist w (C.assign w) ≤ R)
    (hupp : R ≤ (1+kappa)*dist w (C.assign w) +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w) :
    C.Correct hD kappa (s.add w R) := by
  refine ⟨hs.1,?_,?_⟩
  · change ((s.leaves ++ [(w,R)]).map (fun z => C.assign z.1)).Nodup
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨hs.2.1,by simp,?_⟩
    intro a ha b hb hab
    have he : b = C.assign w := by simpa using hb
    apply hnew
    exact List.mem_toFinset.mpr ((hab.trans he) ▸ ha)
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hs.2.2 z hz
    · have he : z = (w,R) := by simpa using hz
      subst z
      exact ⟨hw,hb,hnear,hR,hlow,hupp⟩

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*} [Fintype A]
open scoped Classical

variable {I : Type*} [Fintype I]

lemma routed_pos (q : Kernel S I) (route : S → I → A) (s : S) (a : A)
    (h : 0 < (routed q route).weight s a) : ∃ i, route s i = a ∧ 0 < q.weight s i := by
  classical
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (show ∀ i ∈ (Finset.univ : Finset I), 0 ≤ if route s i = a then q.weight s i else 0 from
      fun i _ => by split_ifs; exact q.nonneg s i; exact le_rfl)).mp h
  by_cases he : route s i = a
  · exact ⟨i,he,by simpa only [ite_eq_left he] using hi⟩
  · simp only [ite_eq_right he, lt_self_iff_false] at hi

omit [Fintype A] in
lemma states_zero (f : S → A → S) (n : ℕ) (s : S) (seed : Fin n → A) :
    states f n s seed 0 = s := by
  cases n <;> rfl

omit [Fintype A] in
lemma states_step (f : S → A → S) (n : ℕ) (s : S) (seed : Fin n → A) (i : Fin n) :
    states f n s seed i.succ = f (states f n s seed i.castSucc) (seed i) := by
  induction n generalizing s with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [states,Fin.cases_zero,Fin.cases_succ,Fin.castSucc_zero]
      exact states_zero f n (f s (seed 0)) (Fin.tail seed)
    · simpa only [states,Fin.castSucc_succ,Fin.cases_succ,Fin.tail] using
        ih (f s (seed 0)) (Fin.tail seed) j

omit [Fintype A] in
lemma pathWeight_eq_prod (f : S → A → S) (p : S → A → ℝ)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f p n s seed = ∏ i : Fin n, p (states f n s seed i.castSucc) (seed i) := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simpa only [pathWeight,states,Fin.castSucc_succ,Fin.castSucc_zero,Fin.cases_zero,Fin.cases_succ,Fin.tail] using
      congrArg (fun x => p s (seed 0)*x) (ih (f s (seed 0)) (Fin.tail seed))

lemma supported_step (f : S → A → S) (p : Kernel S A)
    (n : ℕ) (s : S) (seed : Fin n → A)
    (hseed : 0 < pathWeight f p.weight n s seed) (i : Fin n) :
    0 < p.weight (states f n s seed i.castSucc) (seed i) := by
  rw [pathWeight_eq_prod] at hseed
  have hh := (Finset.prod_ne_zero_iff).mp (ne_of_gt hseed) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (p.nonneg _ _) (Ne.symm hh)

lemma states_invariant (f : S → A → S) (p : Kernel S A) (Inv : S → Prop)
    (hstep : ∀ s, Inv s → ∀ a, 0 < p.weight s a → Inv (f s a))
    (n : ℕ) (s : S) (hs : Inv s) (seed : Fin n → A)
    (hseed : 0 < pathWeight f p.weight n s seed) (i : Fin (n+1)) :
    Inv (states f n s seed i) := by
  refine Fin.induction ?_ (fun j hj => ?_) i
  · simpa only [states_zero] using hs
  · rw [states_step]
    exact hstep _ hj _ (supported_step f p n s seed hseed j)

end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

lemma third_ball_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (_hk : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves)
    (hzthird : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1 < dist z.1 (C.assign z.1))
    (hwthird : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w))
    (hwleaf : 10*dist w (C.assign w) < dist w z.1+z.2) :
    Disjoint (Population.ball D z.1 (Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1))
      (Population.ball D w (Population.radius D hD (comparisonCost D C.assign) C.bad.card w)) := by
  apply Finset.disjoint_left.mpr
  intro p hpz hpw
  have hzp := (Finset.mem_filter.mp hpz).2
  have hwp := (Finset.mem_filter.mp hpw).2
  have ht := dist_triangle z.1 p w
  rw [dist_comm p w] at ht
  have ht' := C.comparison_triangle z.1 w (hs.2.2 z hz).1 hw
  have hR := (hs.2.2 z hz).2.2.2.2.2
  have hq := Population.radius_pos D hD (comparisonCost D C.assign) C.bad.card z.1 hP hm
  have hm1 := mul_le_mul_of_nonneg_right hk1 (dist_nonneg (x := z.1) (y := C.assign z.1))
  have hm2 := mul_le_mul_of_nonneg_right hk1 hq.le
  rw [dist_comm w z.1] at hwleaf
  nlinarith

lemma nearTotal_le_weight (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) :
    C.nearTotal Δ s ≤ totalWeight D S Δ s := by
  rw [C.nearTotal_eq]
  have he : (∑ p ∈ C.nearEligible s, reference S Δ s p) =
      ∑ p ∈ C.nearEligible s, clientWeight S Δ s p :=
    Finset.sum_congr rfl (fun p _ => (clientWeight_eq S Δ s p hΔ
      (C.correct_radii_nonneg hD kappa s hs)).symm)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => clientWeight_nonneg S Δ s p)

lemma removalTotal_le_weight (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) :
    C.removalTotal Δ s ≤ totalWeight D S Δ s := by
  have he : C.removalTotal Δ s = ∑ p ∈ C.removalEligible Δ s, clientWeight S Δ s p :=
    Finset.sum_congr rfl (fun p _ => (clientWeight_eq S Δ s p hΔ
      (C.correct_radii_nonneg hD kappa s hs)).symm)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => clientWeight_nonneg S Δ s p)

lemma eligible_ball_correct (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ C.nearEligible s) (R : ℝ) (hR : 0 < R)
    (hlo : dist w (C.assign w) ≤ R)
    (hhi : R ≤ (1+kappa)*dist w (C.assign w)+
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w) :
    C.Correct hD kappa (s.add w R) := by
  obtain ⟨hwD,hb,hnear⟩ := Finset.mem_filter.mp hw
  exact C.correct_add hD kappa s hs w R hwD (Finset.mem_sdiff.mp hb).1
    (Finset.mem_sdiff.mp hb).2 hnear hR hlo hhi

lemma counter_ball_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (w : V) (R : ℝ)
    (hs' : C.Correct hD kappa (s.add w R)) : C.counter (s.add w R) < C.counter s := by
  have hlen := C.correct_lengths hD kappa (s.add w R) hs'
  simp only [State.add, List.length_append, List.length_singleton] at hlen
  simp only [counter, State.add, List.length_append, List.length_singleton]
  omega

lemma counter_remove_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (v : V) (hv : v ∉ s.deleted)
    (hs' : C.Correct hD kappa (s.remove v)) : C.counter (s.remove v) < C.counter s := by
  have hlen := C.correct_lengths hD kappa (s.remove v) hs'
  have hcard : (s.remove v).deleted.card = s.deleted.card+1 := by
    exact @Finset.card_insert_of_notMem V s.deleted v (fun a b => Classical.propDecidable (a = b)) hv
  rw [hcard] at hlen
  unfold counter
  rw [hcard]
  change 2*C.bad.card-(s.leaves.length+(s.deleted.card+1)) < _
  change (s.leaves.length ≤ C.bad.card ∧ s.deleted.card+1 ≤ C.bad.card) at hlen
  omega

open scoped Classical

lemma conditionalClients_pos (D S : Finset V) (Δ : ℝ) (s : State V)
    (E : Finset V) (hE : E ⊆ D) (T : ℝ) (hT : 0 < T)
    (he : ∑ p ∈ E, clientWeight S Δ s p = T) (w : D)
    (hw : 0 < (conditionalClients D S Δ s E hE T hT he).weight () w) :
    w.val ∈ E ∧ 0 < clientWeight S Δ s w := by
  change 0 < (if w.val ∈ E then clientWeight S Δ s w/T else 0) at hw
  by_cases h : w.val ∈ E
  · have hh : 0 < clientWeight S Δ s w/T := by simpa only [ite_eq_left h] using hw
    rcases div_pos_iff.mp hh with ⟨hp,_⟩ | ⟨_,htneg⟩
    · exact ⟨h,hp⟩
    · linarith
  · simp only [ite_eq_right h,lt_self_iff_false] at hw

lemma prescribedEntry_spec (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (w : D) :
    ∃ R : ℝ,
      menuRadius D hD (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        s w (C.prescribedEntry hD hP hm s w) = some R ∧
      0 < R ∧ dist w.val (C.assign w) ≤ R ∧
      R ≤ (1+mainKappa)*dist w.val (C.assign w)+
        mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w ∧
      (∀ j, C.prescribedEntry hD hP hm s w = .inr (.inr j) →
        10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w.val (C.assign w) ∧
        (∀ z ∈ s.leaves, 10*dist w.val (C.assign w) < dist w.val z.1+z.2) ∧
        j.val+1 = Nat.ceil (dist w.val (C.assign w)/
          (mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w))) := by
  simp only [prescribedEntry,dite_eq_left hs]
  exact (C.correct_entry_exists hD mainKappa mainKappa_pos s hs hP hm w w.property).choose_spec

lemma activeGuide_support (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s)
    (a : MainAction D C.bad.card)
    (ha : 0 < (C.activeGuide hD Δ hΔ hP hm s hs ht).weight () a) :
    (mainKappa*comparisonCost D C.assign < C.nearTotal Δ s ∧
      ∃ w : D, a = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
        w.val ∈ C.nearEligible s) ∨
    (C.nearTotal Δ s ≤ mainKappa*comparisonCost D C.assign ∧
      mainKappa*comparisonCost D C.assign < C.removalTotal Δ s ∧
      ∃ w : D, a = .inr (.inl w) ∧ w.val ∈ C.removalEligible Δ s) := by
  unfold activeGuide at ha
  split_ifs at ha with hb
  · obtain ⟨w,he,hw⟩ := Guided.routed_pos _ _ () a ha
    exact Or.inl ⟨hb,w,he.symm,(conditionalClients_pos _ _ _ _ _ _ _ _ _ w hw).1⟩
  · have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
      by_contra hh
      exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
    obtain ⟨w,he,hw⟩ := Guided.routed_pos _ _ () a ha
    exact Or.inr ⟨le_of_not_gt hb,hi,w,he.symm,(conditionalClients_pos _ _ _ _ _ _ _ _ _ w hw).1⟩

lemma active_weight_pos (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s) :
    0 < totalWeight D S Δ s := by
  have h0 := mul_pos mainKappa_pos hP
  by_cases hb : mainKappa*comparisonCost D C.assign < C.nearTotal Δ s
  · exact (h0.trans hb).trans_le (C.nearTotal_le_weight hD mainKappa Δ s hs hΔ)
  · have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
      by_contra hh
      exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
    exact (h0.trans hi).trans_le (C.removalTotal_le_weight hD mainKappa Δ s hs hΔ)

lemma update_eligible_ball (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (hW : 0 < totalWeight D S Δ s)
    (w : D) (hw : w.val ∈ C.nearEligible s) :
    ∃ R, update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        (some s) (.inr (.inr (w,C.prescribedEntry hD hP hm s w))) = some (s.add w R) ∧
      C.Correct hD mainKappa (s.add w R) ∧ C.counter (s.add w R) < C.counter s := by
  obtain ⟨R,hmenu,hR,hlo,hhi,_⟩ := C.prescribedEntry_spec hD hP hm s hs w
  have hc := C.eligible_ball_correct hD mainKappa s hs w hw R hR hlo hhi
  have hball : (F.filter (fun v => dist w.val v ≤ R)).Nonempty :=
    ⟨C.assign w,Finset.mem_filter.mpr ⟨hOF (C.assigned w w.property),hlo⟩⟩
  refine ⟨R,?_,hc,C.counter_ball_decreases hD mainKappa s w R hc⟩
  simp only [update,ite_eq_left hW,hmenu,ite_eq_left hball,retain,
    ite_eq_left (C.correct_lengths hD mainKappa (s.add w R) hc)]

lemma update_eligible_removal (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (Δ : ℝ) (s : State V) (hs : C.Correct hD mainKappa s)
    (hW : 0 < totalWeight D S Δ s) (w : D) (hw : w.val ∈ C.removalEligible Δ s) :
    ∃ v, v ∈ C.nonproxy \ s.deleted ∧
      update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        (some s) (.inr (.inl w)) = some (s.remove v) ∧
      C.Correct hD mainKappa (s.remove v) ∧ C.counter (s.remove v) < C.counter s := by
  obtain ⟨v,hv,hchosen⟩ := (Finset.mem_filter.mp hw).2
  have hc := C.correct_remove hD mainKappa s hs v (Finset.mem_sdiff.mp hv).1
  refine ⟨v,hv,?_,hc,C.counter_remove_decreases hD mainKappa s v (Finset.mem_sdiff.mp hv).2 hc⟩
  simp only [update,ite_eq_left hW,hchosen,realTag,ofLex_toLex,retain,
    ite_eq_left (C.correct_lengths hD mainKappa (s.remove v) hc)]

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

lemma guide_invariant (C : Comparison D S O) (hD : D.Nonempty) (F : Finset V) (hOF : O ⊆ F)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (hs : C.Valid hD s) (a : MainAction D C.bad.card)
    (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight s a) :
    C.Valid hD (C.guidedUpdate hD F Δ s a) := by
  cases s with
  | none => contradiction
  | some s =>
    change C.Correct hD mainKappa s at hs
    by_cases ht : C.Terminal mainKappa Δ s
    · change C.Valid hD (if C.stop hD Δ (some s) then some s else _)
      rw [ite_eq_left (show C.stop hD Δ (some s) from ⟨hs,ht⟩)]
      exact hs
    · have hstop : ¬C.stop hD Δ (some s) := by simpa only [stop,and_iff_right hs] using ht
      change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
      simp only [guideAt,dite_eq_left hs,dite_eq_right ht] at ha
      have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop]
      rcases C.activeGuide_support hD Δ hΔ hP hm s hs ht a ha with ⟨_,w,rfl,hw⟩ | ⟨_,_,w,rfl,hw⟩
      · obtain ⟨R,he,hc,_⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
        rw [he]
        exact hc
      · obtain ⟨v,_,he,hc,_⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
        rw [he]
        exact hc

lemma history_state (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin (n+1)) :
    Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i =
      some (C.history hD F Δ n seed i) := by
  have hv := Guided.states_invariant (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.Valid hD) (C.guide_invariant hD F hOF Δ hΔ hP hm) n (some State.initial)
    (C.correct_initial hD mainKappa) seed hseed i
  unfold history
  cases he : Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i with
  | none => rw [he] at hv; exact False.elim hv
  | some s => rfl

lemma history_correct (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin (n+1)) : C.Correct hD mainKappa (C.history hD F Δ n seed i) := by
  have hh := Guided.states_invariant (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.Valid hD) (C.guide_invariant hD F hOF Δ hΔ hP hm) n (some State.initial)
    (C.correct_initial hD mainKappa) seed hseed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i] at hh
  exact hh

lemma supported_guide_step (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (a : MainAction D C.bad.card)
    (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight (some s) a) :
    (C.Terminal mainKappa Δ s ∧ a = .inl () ∧ C.guidedUpdate hD F Δ (some s) a = some s) ∨
    (∃ w : D, ∃ R, a = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ C.guidedUpdate hD F Δ (some s) a = some (s.add w R)) ∨
    (∃ w : D, ∃ v, a = .inr (.inl w) ∧ v ∈ C.nonproxy \ s.deleted ∧
      C.guidedUpdate hD F Δ (some s) a = some (s.remove v)) := by
  by_cases ht : C.Terminal mainKappa Δ s
  · have he : a = .inl () := by
      by_contra hh
      simp only [guideKernel,guideAt,dite_eq_left hs,dite_eq_left ht,Guided.pure,ite_eq_right hh] at ha
      exact lt_irrefl 0 ha
    refine Or.inl ⟨ht,he,?_⟩
    change (if C.stop hD Δ (some s) then some s else _) = some s
    exact ite_eq_left ⟨hs,ht⟩
  · have hstop : ¬C.stop hD Δ (some s) := fun h => ht h.2
    change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
    simp only [guideAt,dite_eq_left hs,dite_eq_right ht] at ha
    have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
    rcases C.activeGuide_support hD Δ hΔ hP hm s hs ht a ha with ⟨_,w,he,hw⟩ | ⟨_,_,w,he,hw⟩
    · obtain ⟨R,hupdate,_,_⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
      refine Or.inr (Or.inl ⟨w,R,he,hw,?_⟩)
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop,he]
      exact hupdate
    · obtain ⟨v,hv,hupdate,_,_⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
      refine Or.inr (Or.inr ⟨w,v,he,hv,?_⟩)
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop,he]
      exact hupdate

lemma history_step (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) :
    let s := C.history hD F Δ n seed i.castSucc
    let t := C.history hD F Δ n seed i.succ
    (C.Terminal mainKappa Δ s ∧ seed i = .inl () ∧ t = s) ∨
    (∃ w : D, ∃ R, seed i = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ t = s.add w R) ∨
    (∃ w : D, ∃ v, seed i = .inr (.inl w) ∧ v ∈ C.nonproxy \ s.deleted ∧ t = s.remove v) := by
  dsimp only
  have ha := Guided.supported_step (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    n (some State.initial) seed hseed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.castSucc] at ha
  have he := Guided.states_step (C.guidedUpdate hD F Δ) n (some State.initial) seed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.castSucc,
    C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.succ] at he
  rcases C.supported_guide_step hD F hOF Δ hΔ hP hm _
      (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (seed i) ha with
    ⟨ht,hact,hup⟩ | ⟨w,R,hact,hw,hup⟩ | ⟨w,v,hact,hv,hup⟩
  · exact Or.inl ⟨ht,hact,Option.some.inj (he.trans hup)⟩
  · exact Or.inr (Or.inl ⟨w,R,hact,hw,Option.some.inj (he.trans hup)⟩)
  · exact Or.inr (Or.inr ⟨w,v,hact,hv,Option.some.inj (he.trans hup)⟩)

lemma history_leaves_mono (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    Monotone (fun i => (C.history hD F Δ n seed i).leaves.toFinset) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rcases C.history_step hD F hOF Δ hΔ hP hm n seed hseed i with
    ⟨_,_,he⟩ | ⟨w,R,_,_,he⟩ | ⟨w,v,_,_,he⟩
  · rw [he]
  · rw [he]
    intro z hz
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hz))
  · rw [he]
    exact Finset.Subset.refl _

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma thirdSteps_subset {m n : ℕ} (seed : Fin n → MainAction D m) :
    thirdSteps seed ⊆ ballSteps seed := by
  intro i hi
  obtain ⟨w,j,he⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,_,he⟩

lemma history_ball (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ ballSteps seed) :
    let s := C.history hD F Δ n seed i.castSucc
    let w := ballLeader hD (seed i)
    ∃ R, seed i = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ C.history hD F Δ n seed i.succ = s.add w R := by
  dsimp only
  obtain ⟨wi,ei,hai⟩ := (Finset.mem_filter.mp hi).2
  rcases C.history_step hD F hOF Δ hΔ hP hm n seed hseed i with
    ⟨_,ha,_⟩ | ⟨w,R,ha,hw,he⟩ | ⟨w,v,ha,_,_⟩
  · rw [hai] at ha; contradiction
  · have hl : ballLeader hD (seed i) = w := by rw [ha]; rfl
    rw [hl]
    exact ⟨R,ha,hw,he⟩
  · rw [hai] at ha
    cases Sum.inr.inj ha

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_EntryIndex
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

lemma history_ball_before (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i j : Fin n) (hi : i ∈ ballSteps seed) (hij : i < j) :
    ∃ R, ((ballLeader hD (seed i)).val,R) ∈ (C.history hD F Δ n seed j.castSucc).leaves := by
  obtain ⟨R,_,_,he⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i hi
  have hmem : ((ballLeader hD (seed i)).val,R) ∈ (C.history hD F Δ n seed i.succ).leaves := by
    rw [he]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hij' : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
  exact ⟨R,List.mem_toFinset.mp (C.history_leaves_mono hD F hOF Δ hΔ hP hm n seed hseed hij'
    (List.mem_toFinset.mpr hmem))⟩

lemma covered_of_leaf (C : Comparison D S O) (s : State V) (w : V) (R : ℝ)
    (hmem : (w,R) ∈ s.leaves) : C.assign w ∈ C.covered s := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(w,R),hmem,rfl⟩)

lemma history_ball_count (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (ballSteps seed).card ≤ C.bad.card := by
  let center := fun i : Fin n => C.assign (ballLeader hD (seed i))
  have hmemb : ∀ i ∈ ballSteps seed, center i ∈ C.bad \ C.covered (C.history hD F Δ n seed i.castSucc) := by
    intro i hi
    obtain ⟨_,_,hw,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i hi
    exact (Finset.mem_filter.mp hw).2.1
  have hne : ∀ i ∈ ballSteps seed, ∀ j ∈ ballSteps seed, i < j → center i ≠ center j := by
    intro i hi j hj hij he
    obtain ⟨R,hR⟩ := C.history_ball_before hD F hOF Δ hΔ hP hm n seed hseed i j hi hij
    have hc := C.covered_of_leaf _ _ _ hR
    have hn := (Finset.mem_sdiff.mp (hmemb j hj)).2
    exact hn (he ▸ hc)
  apply Finset.card_le_card_of_injOn center (fun i hi => (Finset.mem_sdiff.mp (hmemb i hi)).1)
  intro i hi j hj he
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hne i hi j hj hij he
  · exact hne j hj i hi hji he.symm

lemma history_third_spec (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ thirdSteps seed) :
    let s := C.history hD F Δ n seed i.castSucc
    let w := ballLeader hD (seed i)
    10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w.val (C.assign w) ∧
      (∀ z ∈ s.leaves, 10*dist w.val (C.assign w) < dist w.val z.1+z.2) := by
  dsimp only
  obtain ⟨R,ha,_,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i ((thirdSteps_subset seed) hi)
  obtain ⟨w,j,hj⟩ := (Finset.mem_filter.mp hi).2
  have he : C.prescribedEntry hD hP hm (C.history hD F Δ n seed i.castSucc)
      (ballLeader hD (seed i)) = .inr (.inr j) := by
    rw [hj] at ha
    simpa only [hj] using (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj ha))).2.symm
  obtain ⟨_,_,_,_,_,hentry⟩ := C.prescribedEntry_spec hD hP hm _
    (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (ballLeader hD (seed i))
  exact ⟨(hentry j he).1,(hentry j he).2.1⟩

lemma history_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    Set.PairwiseDisjoint (↑(thirdSteps seed)) (fun i => Population.ball D (ballLeader hD (seed i))
      (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))) := by
  have hordered : ∀ i ∈ thirdSteps seed, ∀ j ∈ thirdSteps seed, i < j →
      Disjoint (Population.ball D (ballLeader hD (seed i))
        (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i))))
        (Population.ball D (ballLeader hD (seed j))
        (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed j)))) := by
    intro i hi j hj hij
    obtain ⟨R,hR⟩ := C.history_ball_before hD F hOF Δ hΔ hP hm n seed hseed i j
      ((thirdSteps_subset seed) hi) hij
    have hti := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed i hi
    have htj := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed j hj
    exact C.third_ball_disjoint hD mainKappa mainKappa_pos.le (by norm_num [mainKappa])
      _ (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed j.castSucc) hP hm
      (ballLeader hD (seed j)) (ballLeader hD (seed j)).property
      ((ballLeader hD (seed i)).val,R) hR hti.1 htj.1 (htj.2 _ hR)
  intro i hi j hj hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hordered i hi j hj hij
  · exact (hordered j hj i hi hji).symm

lemma history_population_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    ∑ i ∈ thirdSteps seed, dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))) /
      Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)) ≤
      (10/9 : ℝ)*C.bad.card := by
  apply Population.disjoint_population_budget D (thirdSteps seed)
    (fun i => Population.ball D (ballLeader hD (seed i))
      (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i))))
    _ _ (fun p => dist p (C.assign p)) (comparisonCost D C.assign) C.bad.card hP hm
    (fun _ _ => dist_nonneg) rfl (fun _ _ => Finset.filter_subset _ _)
    (C.history_disjoint hD F hOF Δ hΔ hP hm n seed hseed)
    (fun _ _ => Population.radius_pos D hD _ _ _ hP hm) (fun _ _ => dist_nonneg)
    (fun _ _ => Population.radius_feasible D hD _ _ _ hP hm)
  intro i hi p hp
  have ht := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed i hi
  obtain ⟨hpD,hpd⟩ := Finset.mem_filter.mp hp
  have htri := C.comparison_triangle (ballLeader hD (seed i)) p
    (ballLeader hD (seed i)).property hpD
  linarith [ht.1]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma entryIndex_zero {m : ℕ} (a : MainAction D m) (ha : ¬IsThird a) : entryIndex a = 0 := by
  rcases a with u | (w | ⟨w,e⟩)
  · rfl
  · rfl
  · rcases e with j | (e | j)
    · rfl
    · rfl
    · exact False.elim (ha ⟨w,j,rfl⟩)

lemma history_third_index (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ thirdSteps seed) :
    entryIndex (seed i) = Nat.ceil (dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))) /
      (mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))) := by
  obtain ⟨R,ha,_,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i ((thirdSteps_subset seed) hi)
  obtain ⟨w,j,hj⟩ := (Finset.mem_filter.mp hi).2
  have he : C.prescribedEntry hD hP hm (C.history hD F Δ n seed i.castSucc)
      (ballLeader hD (seed i)) = .inr (.inr j) := by
    rw [hj] at ha
    simpa only [hj] using (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj ha))).2.symm
  obtain ⟨_,_,_,_,_,hentry⟩ := C.prescribedEntry_spec hD hP hm _
    (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (ballLeader hD (seed i))
  have hh := (hentry j he).2.2
  simpa only [hj,entryIndex,ballLeader] using hh

lemma history_index_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (∑ i ∈ ballSteps seed, (entryIndex (seed i) : ℝ)) ≤ (10/(9*mainKappa)+1)*C.bad.card := by
  have he : (∑ i ∈ ballSteps seed, (entryIndex (seed i) : ℝ)) =
      ∑ i ∈ thirdSteps seed, (entryIndex (seed i) : ℝ) := by
    symm
    apply Finset.sum_subset (thirdSteps_subset seed)
    intro i _ hi
    have hh : ¬IsThird (seed i) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [entryIndex_zero (seed i) hh,Nat.cast_zero]
  rw [he]
  have hh := Population.ceiling_index_budget (thirdSteps seed)
    (fun i => Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))
    (fun i => dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))))
    mainKappa C.bad.card mainKappa_pos
    ((Finset.card_le_card (thirdSteps_subset seed)).trans
      (C.history_ball_count hD F hOF Δ hΔ hP hm n seed hseed))
    (fun _ _ => Population.radius_pos D hD _ _ _ hP hm) (fun _ _ => dist_nonneg)
    (C.history_population_budget hD F hOF Δ hΔ hP hm n seed hseed)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i hi
  rw [C.history_third_index hD F hOF Δ hΔ hP hm n seed hseed i hi]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma action_entry_lower (m : ℕ) (a : MainAction D m) :
    menuConstant mainKappa mainKappa_pos * (1/2 : ℝ)^(entryIndex a) ≤ actionMenuWeight m a := by
  rcases a with u | (w | ⟨w,e⟩)
  · simpa only [entryIndex,actionMenuWeight,pow_zero,mul_one] using menuConstant_le_one mainKappa mainKappa_pos
  · simpa only [entryIndex,actionMenuWeight,pow_zero,mul_one] using menuConstant_le_one mainKappa mainKappa_pos
  · rcases e with j | (e | j)
    · simpa only [entryIndex,actionMenuWeight,menuWeight,pow_zero,mul_one] using
        first_entry_lower mainKappa mainKappa_pos
    · simpa only [entryIndex,actionMenuWeight,menuWeight,pow_zero,mul_one] using
        second_entry_lower mainKappa mainKappa_pos
    · exact third_entry_lower mainKappa mainKappa_pos (thirdSize mainKappa m) (j.val+1)
        (by unfold thirdSize; omega)

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_of_notBall (m : ℕ) (a : MainAction D m) (ha : ¬IsBall a) :
    actionMenuWeight m a = 1 := by
  rcases a with u | (w | ⟨w,e⟩)
  · rfl
  · rfl
  · exact False.elim (ha ⟨w,e,rfl⟩)

lemma history_menu_budget_s238r_oai (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (menuConstant mainKappa mainKappa_pos)^C.bad.card *
      (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
        ∏ i : Fin n, actionMenuWeight C.bad.card (seed i) := by
  have hh := menu_product_budget (ballSteps seed) C.bad.card (menuConstant mainKappa mainKappa_pos)
    (menuConstant_pos mainKappa mainKappa_pos) (menuConstant_le_one mainKappa mainKappa_pos)
    (fun i => entryIndex (seed i)) (fun i => actionMenuWeight C.bad.card (seed i))
    (fun i _ => action_entry_lower _ (seed i))
    (C.history_ball_count hD F hOF Δ hΔ hP hm n seed hseed) _
    (C.history_index_budget hD F hOF Δ hΔ hP hm n seed hseed)
  have he : (∏ i ∈ ballSteps seed, actionMenuWeight C.bad.card (seed i)) =
      ∏ i : Fin n, actionMenuWeight C.bad.card (seed i) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro i _ hi
    exact actionMenuWeight_of_notBall _ _ (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  exact hh.trans_eq he

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r_oai.{u_1}

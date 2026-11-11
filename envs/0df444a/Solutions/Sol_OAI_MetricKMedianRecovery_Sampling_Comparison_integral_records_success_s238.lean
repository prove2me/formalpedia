-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:57.288909+00:00
-- url     : https://prove2.me/submissions/34d45c4c-f502-4cb2-a0b1-ed47772dcfc1

import Mathlib
import Definitions.Def_Q238K023
import Definitions.Def_Q238K027
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_guideLoss_domination_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_history_menu_budget_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_integralPrecision_spec_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma menuConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < menuConstant kappa hk := by
  have hM : (0 : ℝ) < firstSize kappa := by
    dsimp [firstSize]
    positivity
  unfold menuConstant
  refine lt_min (div_pos zero_lt_one (mul_pos (by norm_num) hM)) ?_
  exact lt_min (by positivity) (by norm_num)

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

end Average

lemma average_fin_succ {Ω : Type*} [Fintype Ω] (n : ℕ)
    (X : (Fin (n+1) → Ω) → ℝ) :
    average X = average (fun ω => average (fun s : Fin n → Ω => X (Fin.cons ω s))) := by
  calc
    average X = average (fun p : Ω × (Fin n → Ω) => X (Fin.cons p.1 p.2)) := by
      apply average_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).symm
      intro s
      exact congrArg X (Fin.cons_self_tail s).symm
    _ = _ := average_prod _

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_Kernel
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided

variable {S A : Type*} [Fintype A]

omit [Fintype A] in
lemma pathWeight_nonneg (f : S → A → S) (p : S → A → ℝ)
    (hp : ∀ s a, 0 ≤ p s a) (n : ℕ) (s : S) (seed : Fin n → A) :
    0 ≤ pathWeight f p n s seed := by
  induction n generalizing s with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp s _) (ih _ _)

lemma sum_fin_succ (n : ℕ) (X : (Fin (n+1) → A) → ℝ) :
    (∑ seed, X seed) = ∑ a : A, ∑ seed : Fin n → A, X (Fin.cons a seed) := by
  calc
    _ = ∑ y : A × (Fin n → A), X (Fin.cons y.1 y.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => A)).symm
      intro x
      exact congrArg X (Fin.cons_self_tail x).symm
    _ = _ := Fintype.sum_prod_type _

lemma pathWeight_total (f : S → A → S) (p : Kernel S A) (n : ℕ) (s : S) :
    ∑ seed : Fin n → A, pathWeight f p.weight n s seed = 1 := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [sum_fin_succ]
    simp only [pathWeight, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum, ih, mul_one]
    exact p.total s

lemma pathWeight_domination (f : S → A → S) (p q : Kernel S A)
    (loss : S → A → ℝ) (hloss : ∀ s a, 0 ≤ loss s a)
    (hstep : ∀ s a, loss s a * q.weight s a ≤ p.weight s a)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f loss n s seed * pathWeight f q.weight n s seed ≤
      pathWeight f p.weight n s seed := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hh := mul_le_mul (hstep s (seed 0)) (ih (f s (seed 0)) (Fin.tail seed))
      (mul_nonneg (pathWeight_nonneg f loss hloss _ _ _)
        (pathWeight_nonneg f q.weight q.nonneg _ _ _))
      (p.nonneg s (seed 0))
    simpa only [pathWeight, mul_mul_mul_comm] using hh

lemma supported_path_hits (f : S → A → S) (q : Kernel S A) (stop Inv : S → Prop)
    (counter : S → ℕ)
    (hInv : ∀ s, Inv s → ∀ a, 0 < q.weight s a → Inv (f s a))
    (hzero : ∀ s, Inv s → counter s = 0 → stop s)
    (hdesc : ∀ s, Inv s → ¬stop s → ∀ a, 0 < q.weight s a → counter (f s a) < counter s)
    (n : ℕ) (s : S) (hs : Inv s) (hc : counter s ≤ n) (seed : Fin n → A)
    (hseed : 0 < pathWeight f q.weight n s seed) : Hits f stop n s seed := by
  induction n generalizing s with
  | zero => exact hzero s hs (Nat.eq_zero_of_le_zero hc)
  | succ n ih =>
    by_cases ht : stop s
    · exact Or.inl ht
    · change 0 < q.weight s (seed 0) *
        pathWeight f q.weight n (f s (seed 0)) (Fin.tail seed) at hseed
      have hn := pathWeight_nonneg f q.weight q.nonneg n (f s (seed 0)) (Fin.tail seed)
      have hp : 0 < q.weight s (seed 0) := by nlinarith
      have htail : 0 < pathWeight f q.weight n (f s (seed 0)) (Fin.tail seed) := by
        nlinarith [q.nonneg s (seed 0)]
      exact Or.inr (ih _ (hInv s hs _ hp) (by have := hdesc s hs ht _ hp; omega) _ htail)

theorem history_likelihood_bound (f : S → A → S) (p q : Kernel S A)
    (loss : S → A → ℝ) (hloss : ∀ s a, 0 ≤ loss s a)
    (hstep : ∀ s a, loss s a * q.weight s a ≤ p.weight s a)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) (B : ℝ) (_hB : 0 ≤ B)
    (hbudget : ∀ seed, 0 < pathWeight f q.weight n s seed → B ≤ pathWeight f loss n s seed)
    (hevent : ∀ seed, 0 < pathWeight f q.weight n s seed → E seed) :
    B ≤ eventMass f p.weight n s E := by
  classical
  have hpoint : ∀ seed : Fin n → A,
      B * pathWeight f q.weight n s seed ≤
        if E seed then pathWeight f p.weight n s seed else 0 := by
    intro seed
    have hq := pathWeight_nonneg f q.weight q.nonneg n s seed
    by_cases hp : 0 < pathWeight f q.weight n s seed
    · rw [ite_eq_left (hevent seed hp)]
      exact (mul_le_mul_of_nonneg_right (hbudget seed hp) hq).trans
        (pathWeight_domination f p q loss hloss hstep n s seed)
    · have hz : pathWeight f q.weight n s seed = 0 := le_antisymm (le_of_not_gt hp) hq
      rw [hz, mul_zero]
      split_ifs
      · exact pathWeight_nonneg f p.weight p.nonneg n s seed
      · exact le_rfl
  have hsum := Finset.sum_le_sum (fun seed (_ : seed ∈ Finset.univ) => hpoint seed)
  rw [← Finset.mul_sum, pathWeight_total, mul_one] at hsum
  exact hsum

end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.NearClients
variable {V : Type*}

variable [PseudoMetricSpace V]

lemma progressConstant_pos (kappa : ℝ) (hk : 0 < kappa) : 0 < progressConstant kappa := by
  unfold progressConstant
  positivity

end MetricKMedianRecovery.NearClients

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

lemma hitMass_zero (f : S → A → S) (p : Kernel S A) (stop : S → Prop) (s : S) :
    hitMass f p stop 0 s = if stop s then 1 else 0 := by
  classical
  by_cases h : stop s <;> simp [hitMass,eventMass,Hits,pathWeight,h]

lemma hitMass_succ (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (n : ℕ) (s : S) :
    hitMass f p stop (n+1) s = if stop s then 1 else
      ∑ a : A, p.weight s a*hitMass f p stop n (f s a) := by
  classical
  by_cases hs : stop s
  · simp only [hitMass, eventMass, Hits, hs, true_or, ite_true, if_true]
    exact pathWeight_total f p (n+1) s
  · simp only [ite_eq_right hs, hitMass, eventMass]
    rw [sum_fin_succ]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    simp only [Hits, hs, false_or, Fin.cons_zero, Fin.tail_cons, pathWeight]
    split_ifs <;> simp

lemma hitMass_eq_of_agree (f g : S → A → S) (p q : Kernel S A) (stop : S → Prop)
    (hf : ∀ s, ¬stop s → ∀ a, f s a = g s a)
    (hp : ∀ s, ¬stop s → ∀ a, p.weight s a = q.weight s a)
    (n : ℕ) (s : S) : hitMass f p stop n s = hitMass g q stop n s := by
  classical
  induction n generalizing s with
  | zero => rw [hitMass_zero,hitMass_zero]
  | succ n ih =>
    rw [hitMass_succ,hitMass_succ]
    split_ifs with hs
    · rfl
    · apply Finset.sum_congr rfl
      intro a _
      rw [hp s hs a,hf s hs a,ih]

lemma hitMass_stopped (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (a₀ : A) (n : ℕ) (s : S) :
    hitMass (stoppedUpdate f stop) (stoppedKernel p stop a₀) stop n s =
      hitMass f p stop n s := by
  apply hitMass_eq_of_agree
  · intro s hs a
    simp only [stoppedUpdate,ite_eq_right hs]
  · intro s hs a
    simp only [stoppedKernel,ite_eq_right hs]

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
lemma pathWeight_eq_prod (f : S → A → S) (p : S → A → ℝ)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f p n s seed = ∏ i : Fin n, p (states f n s seed i.castSucc) (seed i) := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simpa only [pathWeight,states,Fin.castSucc_succ,Fin.castSucc_zero,Fin.cases_zero,Fin.cases_succ,Fin.tail] using
      congrArg (fun x => p s (seed 0)*x) (ih (f s (seed 0)) (Fin.tail seed))

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

lemma counter_zero_terminal (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hk : 0 ≤ kappa)
    (hz : C.counter s = 0) : C.Terminal kappa Δ s := by
  have hlen := C.correct_lengths hD kappa s hs
  have he1 : s.leaves.length = C.bad.card := by unfold counter at hz; omega
  have he2 : s.deleted.card = C.bad.card := by unfold counter at hz; omega
  have hcard : (C.covered s).card = C.bad.card := by
    rw [covered, List.toFinset_card_of_nodup hs.2.1, List.length_map, he1]
  have hcov : C.covered s = C.bad := Finset.eq_of_subset_of_card_le
    (C.correct_covered_subset hD kappa s hs) hcard.ge
  have hdel : s.deleted = C.nonproxy := Finset.eq_of_subset_of_card_le hs.1
    (by rw [he2, C.nonproxy_card])
  have hP : 0 ≤ comparisonCost D C.assign := Finset.sum_nonneg (fun p _ => dist_nonneg)
  have hT : C.nearTotal Δ s = 0 := by simp only [nearTotal, hcov, Finset.sdiff_self, Finset.sum_empty]
  have hI : C.removalTotal Δ s = 0 := by simp [removalTotal, hdel]
  exact ⟨hT ▸ mul_nonneg hk hP, hI ▸ mul_nonneg hk hP⟩

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

lemma guide_counter_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (hs : C.Valid hD s) (ht : ¬C.stop hD Δ s)
    (a : MainAction D C.bad.card) (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight s a) :
    C.remaining (C.guidedUpdate hD F Δ s a) < C.remaining s := by
  cases s with
  | none => contradiction
  | some s =>
    change C.Correct hD mainKappa s at hs
    have hterm : ¬C.Terminal mainKappa Δ s := fun h => ht ⟨hs,h⟩
    change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
    simp only [guideAt,dite_eq_left hs,dite_eq_right hterm] at ha
    have hW := C.active_weight_pos hD Δ hΔ hP s hs hterm
    simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right ht]
    rcases C.activeGuide_support hD Δ hΔ hP hm s hs hterm a ha with ⟨_,w,rfl,hw⟩ | ⟨_,_,w,rfl,hw⟩
    · obtain ⟨R,he,_,hc⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
      rw [he]
      exact hc
    · obtain ⟨v,_,he,_,hc⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
      rw [he]
      exact hc

theorem guide_hits (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (seed : Fin (2*C.bad.card) → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight (2*C.bad.card) (some State.initial) seed) :
    Guided.Hits (C.guidedUpdate hD F Δ) (C.stop hD Δ) (2*C.bad.card) (some State.initial) seed := by
  apply Guided.supported_path_hits (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.stop hD Δ) (C.Valid hD) C.remaining
    (C.guide_invariant hD F hOF Δ hΔ hP hm) ?_
    (C.guide_counter_decreases hD F hOF Δ hΔ hP hm) (2*C.bad.card) (some State.initial)
    (C.correct_initial hD mainKappa) ?_ seed hseed
  · intro s hs hc
    cases s with
    | none => contradiction
    | some s =>
      exact ⟨hs,C.counter_zero_terminal hD mainKappa Δ s hs mainKappa_pos.le hc⟩
  · simp only [remaining,counter,State.initial,List.length_nil,Finset.card_empty,add_zero,Nat.sub_zero,le_refl]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_nonneg (m : ℕ) (a : MainAction D m) :
    0 ≤ actionMenuWeight m a := by
  rcases a with u | (w | ⟨w,e⟩)
  · exact zero_le_one
  · exact zero_le_one
  · exact menuWeight_nonneg _ _ _ e

lemma guideLoss_nonneg (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    0 ≤ C.guideLoss hD Δ s a := by
  unfold guideLoss
  split_ifs
  · exact mul_nonneg (NearClients.progressConstant_pos _ mainKappa_pos).le
      (actionMenuWeight_nonneg _ _)
  · exact zero_le_one

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

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_le_one (m : ℕ) (a : MainAction D m) : actionMenuWeight m a ≤ 1 := by
  rcases a with u | (w | ⟨w,e⟩)
  · exact le_rfl
  · exact le_rfl
  · have hh := Finset.single_le_sum (s := (Finset.univ : Finset (MainEntry m)))
      (f := menuWeight (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m))
      (fun j _ => menuWeight_nonneg _ _ _ j) (Finset.mem_univ e)
    rw [menuWeight_total _ _ _ (by unfold firstSize; omega) (by unfold thirdSize; omega)] at hh
    exact hh

lemma progressConstant_le_one : NearClients.progressConstant mainKappa ≤ 1 := by
  norm_num [NearClients.progressConstant,mainKappa]

lemma guideLoss_lower (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a ≤ C.guideLoss hD Δ s a := by
  unfold guideLoss
  split_ifs
  · exact le_rfl
  · exact (mul_le_mul_of_nonneg_left (actionMenuWeight_le_one _ _)
      (NearClients.progressConstant_pos mainKappa mainKappa_pos).le).trans
      (by simpa only [mul_one] using progressConstant_le_one)

lemma history_loss_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    NearClients.progressConstant mainKappa ^ n * (menuConstant mainKappa mainKappa_pos)^C.bad.card *
      (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
        Guided.pathWeight (C.guidedUpdate hD F Δ) (C.guideLoss hD Δ) n (some State.initial) seed := by
  have hρ := (NearClients.progressConstant_pos mainKappa mainKappa_pos).le
  rw [Guided.pathWeight_eq_prod]
  calc
    _ = NearClients.progressConstant mainKappa ^ n *
        ((menuConstant mainKappa mainKappa_pos)^C.bad.card *
          (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card))) := mul_assoc _ _ _
    _ ≤ NearClients.progressConstant mainKappa ^ n *
        (∏ i : Fin n, actionMenuWeight C.bad.card (seed i)) :=
      mul_le_mul_of_nonneg_left (C.history_menu_budget_s238 hD F hOF Δ hΔ hP hm n seed hseed) (pow_nonneg hρ n)
    _ = ∏ i : Fin n, NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card (seed i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ _ := Finset.prod_le_prod (fun i _ => mul_nonneg hρ (actionMenuWeight_nonneg _ _))
      (fun i _ => C.guideLoss_lower hD Δ _ _)

lemma samplingBound_pos (m : ℕ) : 0 < samplingBound m := by
  exact mul_pos (mul_pos (pow_pos (NearClients.progressConstant_pos mainKappa mainKappa_pos) _)
    (pow_pos (menuConstant_pos mainKappa mainKappa_pos) _)) (Real.rpow_pos_of_pos (by norm_num) _)

theorem actual_records_success (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    samplingBound C.bad.card ≤ Guided.hitMass
      (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
      (mainActual D S Δ C.bad.card) (C.stop hD Δ) (2*C.bad.card) (some State.initial) := by
  rw [← Guided.hitMass_stopped _ _ _ (Sum.inl ())]
  change samplingBound C.bad.card ≤ Guided.hitMass (C.guidedUpdate hD F Δ)
    (C.stoppedActual hD Δ) (C.stop hD Δ) (2*C.bad.card) (some State.initial)
  apply Guided.history_likelihood_bound (C.guidedUpdate hD F Δ) (C.stoppedActual hD Δ)
    (C.guideKernel hD Δ hΔ hP hm) (C.guideLoss hD Δ) (C.guideLoss_nonneg hD Δ)
    (C.guideLoss_domination_s238 hD Δ hΔ hP hm) _ _ _ _ (samplingBound_pos _).le
  · intro seed hseed
    exact C.history_loss_budget hD F hOF Δ hΔ hP hm _ seed hseed
  · exact C.guide_hits hD F hOF Δ hΔ hP hm

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawCount
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma count_ge (p : A → ℝ) (b : ℕ) (default a : A) : rawCount p b a ≤ count p b default a := by
  unfold count
  omega

lemma weight_lower (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (b : ℕ) (default a : A)
    (hb : ∀ a, 0 < p a → 2 ≤ (2:ℝ)^b * p a) : p a / 2 ≤ weight p b default a := by
  by_cases ha : p a = 0
  · rw [ha,zero_div]
    exact weight_nonneg p b default a
  · have ha' : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
    have hh := hb a ha'
    have hf := Nat.lt_floor_add_one ((2:ℝ)^b * p a)
    have hc : (rawCount p b a : ℝ) ≤ count p b default a := Nat.cast_le.mpr (count_ge p b default a)
    change p a / 2 ≤ (count p b default a : ℝ) / 2^b
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2^b)).mpr
    change (2:ℝ)^b * p a < (rawCount p b a : ℝ) + 1 at hf
    nlinarith

lemma draw_average (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) (f : A → ℝ) :
    (∑ bits : Fin b → Bool, f (draw p hp ht b default bits)) / 2^b =
      ∑ a, weight p b default a * f a := by
  have h := Fintype.sum_equiv (allocation p hp ht b default)
    (fun bits => f (draw p hp ht b default bits)) (fun x => f x.1) (fun _ => rfl)
  rw [h,Fintype.sum_sigma,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,weight]
  ring

end MetricKMedianRecovery.Dyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.FixedDyadic
open FiniteSampling
variable {S A : Type*} [Fintype A] [DecidableEq A]

lemma draw_average (p : Kernel S A) (b : ℕ) (default : A) (s : S) (g : A → ℝ) :
    average (fun bits => g (draw p b default s bits)) =
      ∑ a, (kernel p b default).weight s a * g a := by
  rw [average,Fintype.expect_eq_sum_div_card]
  simpa only [draw,kernel,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    using Dyadic.draw_average (p.weight s) (p.nonneg s) (p.total s) b default g

theorem actions_average (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (g : (Fin n → A) → ℝ) :
    average (fun bits => g (actions f p b default n s bits)) =
      ∑ a : Fin n → A, pathWeight f (kernel p b default).weight n s a * g a := by
  classical
  induction n generalizing s with
  | zero =>
    simp only [actions,average_const,pathWeight,one_mul]
    simp only [Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [average_fin_succ,sum_fin_succ]
    simp only [actions,Fin.cons_zero,Fin.tail_cons,pathWeight]
    conv_lhs =>
      arg 1; ext bits
      rw [ih (f s (draw p b default s bits)) (fun seed => g (Fin.cons (draw p b default s bits) seed))]
    rw [draw_average p b default s
      (fun a => ∑ seed : Fin n → A,
        pathWeight f (kernel p b default).weight n (f s a) seed * g (Fin.cons a seed))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring

lemma actions_probability (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) :
    probability (fun bits => E (actions f p b default n s bits)) =
      eventMass f (kernel p b default).weight n s E := by
  classical
  unfold probability
  rw [actions_average f p b default n s (fun a => if E a then 1 else 0)]
  simp only [eventMass,mul_ite,mul_one,mul_zero]

lemma weight_lower (p : Kernel S A) (b : ℕ) (default : A) (s : S)
    (h : ∀ a, 0 < p.weight s a → 2 ≤ (2:ℝ)^b * p.weight s a) (a : A) :
    (1/2:ℝ)*p.weight s a ≤ (kernel p b default).weight s a := by
  simpa only [kernel,div_eq_mul_inv,one_mul,mul_comm] using
    Dyadic.weight_lower (p.weight s) (p.nonneg s) b default a h

lemma path_lower (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (h : Precise f p b n s) (seed : Fin n → A) :
    (1/2:ℝ)^n * pathWeight f p.weight n s seed ≤
      pathWeight f (kernel p b default).weight n s seed := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hh := mul_le_mul (weight_lower p b default s h.1 (seed 0))
      (ih (f s (seed 0)) (h.2 (seed 0)) (Fin.tail seed))
      (mul_nonneg (by positivity) (pathWeight_nonneg f p.weight p.nonneg _ _ _))
      ((kernel p b default).nonneg s (seed 0))
    simpa only [pathWeight,pow_succ,mul_mul_mul_comm,mul_comm,mul_left_comm,mul_assoc] using hh

theorem event_lower (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (h : Precise f p b n s) (E : (Fin n → A) → Prop) :
    (1/2:ℝ)^n * eventMass f p.weight n s E ≤
      probability (fun bits => E (actions f p b default n s bits)) := by
  classical
  rw [actions_probability,eventMass,eventMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro seed _
  split_ifs with he
  · exact path_lower f p b default n s h seed
  · simp only [mul_zero,le_refl]

end MetricKMedianRecovery.Guided.FixedDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

attribute [local instance] OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2
theorem integral_records_success_s238_oai {D S O : Finset V}
    (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card) * samplingBound C.bad.card ≤
      probability (fun bits => Hits
        (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
        (C.stop hD Δ) (2*C.bad.card) (some State.initial)
        (integralActions D F S hD Δ (comparisonCost D C.assign) C.bad.card bits)) := by
  have hh := event_lower
    (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
    (mainActual D S Δ C.bad.card) (integralPrecision D Δ C.bad.card)
    (Sum.inl ()) (2*C.bad.card) (some State.initial)
    (integralPrecision_spec_s238 D F S hD hSF Δ (comparisonCost D C.assign) hΔ C.bad.card hsep)
    (Hits (blindUpdate D F S hD Δ (comparisonCost D C.assign) C.bad.card)
      (C.stop hD Δ) (2*C.bad.card) (some State.initial))
  exact (mul_le_mul_of_nonneg_left (C.actual_records_success hD F hOF Δ (by linarith) hP hm)
    (by positivity)).trans hh

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238_oai.{u_1}

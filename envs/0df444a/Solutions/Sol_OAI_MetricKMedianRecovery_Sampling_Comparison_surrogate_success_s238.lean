-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:34:16.800019+00:00
-- url     : https://prove2.me/submissions/c4c9ea25-f93c-44a5-89f4-6c3486aacbe8

import Mathlib
import Definitions.Def_Q238K027
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_successful_completion_charge_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma real_mem_tags (S : Finset V) (s : State V) (v : V) :
    realTag v ∈ tags S s ↔ v ∈ S \ s.deleted := by
  simp [tags, realTag, leafTag]

omit [PseudoMetricSpace V] in
lemma leaf_mem_tags (S : Finset V) (s : State V) (j : ℕ) :
    leafTag j ∈ tags S s ↔ j ≤ s.leaves.length := by
  simp [tags, realTag, leafTag]

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

lemma reference_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) : reference S Δ s x ≤ tagDistance Δ s x t :=
  Prod.Lex.monotone_fst _ _ (chosen_key_le S Δ s x ht)

lemma reference_le_real (S : Finset V) (Δ : ℝ) (s : State V) (x v : V)
    (hv : v ∈ S \ s.deleted) : reference S Δ s x ≤ dist x v :=
  reference_le S Δ s x ((real_mem_tags S s v).mpr hv)

lemma reference_le_diameter (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x ≤ Δ :=
  reference_le S Δ s x ((leaf_mem_tags S s 0).mpr (Nat.zero_le _))

lemma reference_le_leaf (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (j : ℕ) (z : V × ℝ) (hz : s.leaves[j]? = some z) :
    reference S Δ s x ≤ dist x z.1 + z.2 := by
  have hj : j < s.leaves.length := List.getElem?_eq_some_iff.mp hz |>.1
  have hh := reference_le S Δ s x ((leaf_mem_tags S s (j+1)).mpr (by omega))
  simpa only [tagDistance, leafTag, ofLex_toLex, hz] using hh

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma cluster_mem (D : Finset V) (c : V → V) (p o : V) :
    p ∈ cluster D c o ↔ p ∈ D ∧ c p = o := Finset.mem_filter

omit [PseudoMetricSpace V] in
lemma cluster_partition (D O : Finset V) (c : V → V)
    (hc : ∀ p ∈ D, c p ∈ O) (f : V → ℝ) :
    (∑ o ∈ O, ∑ p ∈ cluster D c o, f p) = ∑ p ∈ D, f p := by
  classical
  simp only [cluster, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp [hc p hp]

namespace Comparison
variable {D S O : Finset V}

lemma proxy_survives (C : Comparison D S O) (s : State V) (hq : s.deleted ⊆ C.nonproxy)
    (o : V) (ho : o ∈ C.good) : C.proxy o ∈ S \ s.deleted := by
  refine Finset.mem_sdiff.mpr ⟨C.proxy_mem o ho, ?_⟩
  intro hh
  have hn := (Finset.mem_sdiff.mp (hq hh)).2
  exact hn (Finset.mem_image.mpr ⟨o,ho,rfl⟩)

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma center_sum_partition (C : Comparison D S O) (s : State V)
    (hA : C.covered s ⊆ C.bad) (f : V → ℝ) :
    (∑ o ∈ O, f o) = (∑ o ∈ C.good, f o) + (∑ o ∈ C.covered s, f o) +
      ∑ o ∈ C.bad \ C.covered s, f o := by
  have hg := Finset.sum_sdiff C.good_subset (f := f)
  have ha := Finset.sum_sdiff hA (f := f)
  change (∑ o ∈ C.bad, f o)+(∑ o ∈ C.good, f o) = ∑ o ∈ O, f o at hg
  linarith

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma leaderPair_spec (C : Comparison D S O) (s : State V) (o : V) (ho : o ∈ C.covered s) :
    C.leaderPair s o ∈ s.leaves ∧ C.assign (C.leaderPair s o).1 = o := by
  simp only [leaderPair,dite_eq_left ho]
  exact Classical.choose_spec (C.covered_witness s o ho)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

lemma le_topSum {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : (∑ s ∈ S, v s) ≤ topSum q v := by
  apply Finset.le_sup' (f := fun S => ∑ s ∈ S, v s)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact hS

lemma bottomSum_le {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : bottomSum q v ≤ ∑ s ∈ S, v s := by
  have hh := le_topSum (fun r => -v r) hS
  simp only [Finset.sum_neg_distrib] at hh
  exact neg_le.mp (by simpa only [bottomSum] using hh)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma assignmentWeight_nonneg {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) : 0 ≤ assignmentWeight D assignment s := by
  exact Nat.cast_nonneg _

omit [PseudoMetricSpace V] in
lemma assignmentWeight_sum {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) (charge : ℝ) :
    (∑ p ∈ D, if assignment p = Virtual.real s then charge else 0) =
      assignmentWeight D assignment s * charge := by
  rw [← Finset.sum_filter]
  simp [assignmentWeight]

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}
lemma coveredCenter_mem (C : Comparison D S O) (s : State V) (i : Fin s.leaves.length) :
    C.coveredCenter s i ∈ C.covered s := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨s.leaves[i.val],List.getElem_mem i.isLt,rfl⟩
lemma leaderPair_eq_indexed (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (i : Fin s.leaves.length) :
    C.leaderPair s (C.coveredCenter s i) = s.leaves[i.val] := by
  have hh := C.leaderPair_spec s (C.coveredCenter s i) (C.coveredCenter_mem s i)
  exact List.inj_on_of_nodup_map hs.2.1 hh.1 (List.getElem_mem i.isLt) hh.2

lemma coveredIndex_spec (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : C.coveredCenter s (C.coveredIndex s o ho) = o :=
  Classical.choose_spec (C.exists_coveredCenter s o ho)
lemma leafPair_index (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (o : V)
    (ho : o ∈ C.covered s) :
    s.leaves[(C.coveredIndex s o ho).val] = C.leaderPair s o := by
  have hh := C.leaderPair_eq_indexed hD kappa s hs (C.coveredIndex s o ho)
  simpa only [C.coveredIndex_spec s o ho] using hh.symm
end MetricKMedianRecovery.Sampling.Comparison
namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma toVirtual_real_iff (s : State V) (t : Tag V) (v : V) :
    toVirtual s t = .real v ↔ t = realTag v := by
  cases ht : ofLex t with
  | inl u =>
    have he : t = realTag u := congrArg toLex ht
    subst t
    simp [toVirtual,realTag]
  | inr j =>
    have he : t = leafTag j := congrArg toLex ht
    subst t
    cases j with
    | zero => simp [toVirtual,leafTag,realTag]
    | succ j => simp [toVirtual,leafTag,realTag]; split <;> simp_all

omit [PseudoMetricSpace V] in
lemma toVirtual_mem (S : Finset V) (s : State V) (t : Tag V)
    (ht : t ∈ tags S s) : toVirtual s t ∈ withGhosts (S \ s.deleted) := by
  cases he : ofLex t with
  | inl v =>
    have hh : t = realTag v := congrArg toLex he
    have hv := (real_mem_tags S s v).mp (hh ▸ ht)
    simp [toVirtual,he,hv]
  | inr j =>
    cases j with
    | zero => simp [toVirtual,he]
    | succ j => simp only [toVirtual,he]; split <;> simp

lemma toVirtual_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) (t : Tag V)
    (ht : t ∈ tags S s) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (toVirtual s t) = tagDistance Δ s x t := by
  cases he : ofLex t with
  | inl v => simp [toVirtual,tagDistance,he,virtualDistance]
  | inr j =>
    have htag : t = leafTag j := congrArg toLex he
    have hj := (leaf_mem_tags S s j).mp (htag ▸ ht)
    cases j with
    | zero => simp [toVirtual,tagDistance,he,virtualDistance]
    | succ j =>
      have hj' : j < s.leaves.length := by omega
      simp [toVirtual,tagDistance,he,hj',virtualDistance,leafCenter,leafRadius]

lemma reference_eq_virtualNearest (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x = virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro t ht
    cases t with
    | real v =>
      exact reference_le_real S Δ s x v (real_mem_withGhosts.mp ht)
    | ball i =>
      exact reference_le_leaf S Δ s x i.val s.leaves[i.val]
        (List.getElem?_eq_getElem i.isLt)
    | permanent => exact reference_le_diameter S Δ s x
  · have hh := Finset.inf'_le (virtualDistance (leafCenter s) (leafRadius s) Δ x)
      (toVirtual_mem S s (chosen S Δ s x) (chosen_mem S Δ s x))
    simpa only [toVirtual_distance S Δ s x _ (chosen_mem S Δ s x), virtualNearest, reference] using hh

lemma completionAssignment_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (completionAssignment S Δ s x) =
      virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  exact (toVirtual_distance S Δ s x _ (chosen_mem S Δ s x)).trans
    (reference_eq_virtualNearest S Δ s x)

lemma completionAssignment_real_iff (S : Finset V) (Δ : ℝ) (s : State V) (x v : V) :
    completionAssignment S Δ s x = .real v ↔ chosen S Δ s x = realTag v :=
  toVirtual_real_iff s (chosen S Δ s x) v

lemma assigned_clients_agree (D S R : Finset V) (Δ : ℝ) (s : State V) :
    D.filter (fun p => ∃ v ∈ R, completionAssignment S Δ s p = .real v) =
      D.filter (fun p => ∃ v ∈ R, chosen S Δ s p = realTag v) := by
  ext p
  simp only [Finset.mem_filter,completionAssignment_real_iff]

lemma assigned_reference_total_agree (D S R : Finset V) (Δ : ℝ) (s : State V) :
    (∑ p ∈ D.filter (fun p => ∃ v ∈ R, completionAssignment S Δ s p = .real v),
      virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) =
    ∑ p ∈ D.filter (fun p => ∃ v ∈ R, chosen S Δ s p = realTag v), reference S Δ s p := by
  rw [assigned_clients_agree]
  apply Finset.sum_congr rfl
  intro p _
  exact (reference_eq_virtualNearest S Δ s p).symm

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealFilling
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in

lemma sum_assignment_charges {a : ℕ} {R : Type*} (D : Finset V)
    (assignment : V → Virtual V a) (T : Finset R) (loc : R → V) (charge : R → ℝ) :
    (∑ p ∈ D, ∑ r ∈ T, if assignment p = Virtual.real (loc r) then charge r else 0) =
      ∑ r ∈ T, assignmentWeight D assignment (loc r) * charge r := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => assignmentWeight_sum D assignment (loc r) (charge r))

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destination
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

lemma convex_surrogate_upper {P E R : Type*} [Fintype P] [Fintype R]
    (K : ℝ) (q : ℕ) (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (T : Finset R) (hT : T.card = q) (X : Finset E) :
    theta * surrogate K q base distance weight redBase redDistance ∅ +
      (1-theta) * surrogate K q base distance weight redBase redDistance X ≤
    K + (∑ p : P, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ)) +
      ∑ r ∈ T, weight r * (theta*redBase r +
        (1-theta)*cappedCost (redBase r) (redDistance r) X) := by
  have hq : q ≤ Fintype.card R := hT ▸ Finset.card_le_univ T
  have hc : T.card = min q (Fintype.card R) := by rw [min_eq_left hq, hT]
  have h₀ := mul_le_mul_of_nonneg_left
    (bottomSum_le (fun r => weight r * redBase r) hc) ht0
  have h₁ := mul_le_mul_of_nonneg_left
    (bottomSum_le (fun r => weight r * cappedCost (redBase r) (redDistance r) X) hc)
    (show 0 ≤ 1-theta by linarith)
  simp only [surrogate, cappedCost_empty]
  simp only [Finset.sum_add_distrib]
  have he : (∑ r ∈ T, weight r * (theta * redBase r)) +
      ∑ r ∈ T, weight r * ((1-theta)*cappedCost (redBase r) (redDistance r) X) =
      theta * (∑ r ∈ T, weight r * redBase r) +
      (1-theta) * (∑ r ∈ T, weight r * cappedCost (redBase r) (redDistance r) X) := by
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;> ring
  simp only [mul_add, Finset.sum_add_distrib] at he ⊢
  rw [he]
  simp only [← Finset.mul_sum]
  nlinarith

lemma cappedCost_le_base {E : Type*} (b : ℝ) (d : E → ℝ) (X : Finset E) :
    cappedCost b d X ≤ b := (Finset.fold_min_le _).mpr (Or.inl le_rfl)

lemma cappedCost_le_offer {E : Type*} (b : ℝ) (d : E → ℝ) {X : Finset E} {e : E}
    (he : e ∈ X) : cappedCost b d X ≤ d e :=
  (Finset.fold_min_le _).mpr (Or.inr ⟨e, he, le_rfl⟩)

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma virtualNearest_le_real {a : ℕ} (H : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) {s : V} (hs : s ∈ H) :
    virtualNearest H w radius M x ≤ dist x s := by
  exact Finset.inf'_le _ (real_mem_withGhosts.mpr hs)

lemma virtualNearest_le_ball {a : ℕ} (H : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) (i : Fin a) :
    virtualNearest H w radius M x ≤ dist x (w i) + radius i := by
  exact Finset.inf'_le _ (ball_mem_withGhosts H i)

omit [DecidableEq V] in

lemma mixedDistance_covered_triangle {a : ℕ} (theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (center w : Fin a → V)
    (radius : Fin a → ℝ) (s p : V) (i : Fin a) :
    mixedDistance theta center w radius s (.covered i) ≤
      dist p s + dist p (center i) + theta * (dist (w i) (center i) + radius i) := by
  have h₀ := mul_le_mul_of_nonneg_left
    (dist_triangle s (center i) (w i)) ht0
  have h₁ := mul_le_mul_of_nonneg_left
    (dist_triangle s p (center i)) (show 0 ≤ 1-theta by linarith)
  have h₂ := mul_le_mul_of_nonneg_left
    (dist_triangle s p (center i)) ht0
  simp only [mixedDistance]
  rw [dist_comm (center i) (w i)] at h₀
  rw [dist_comm s p] at h₁ h₂
  nlinarith

lemma red_mixed_comparison {E : Type*} {a : ℕ} (G : Finset V)
    (loc : E → V) (X : Finset E) (center w : Fin a → V) (radius : Fin a → ℝ)
    (M theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = center i) (s : V)
    (d : Destination V a)
    (hd : match d with | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False) :
    theta * virtualNearest G w radius M s + (1-theta) *
      cappedCost (virtualNearest G w radius M s) (fun e => dist s (loc e)) X ≤
      mixedDistance theta center w radius s d := by
  have ht : 0 ≤ 1-theta := by linarith
  cases d with
  | proxy φ =>
    have hb := virtualNearest_le_real G w radius M s hd
    have hc := (cappedCost_le_base (virtualNearest G w radius M s) (fun e => dist s (loc e)) X).trans hb
    have h₀ := mul_le_mul_of_nonneg_left hb ht0
    have h₁ := mul_le_mul_of_nonneg_left hc ht
    simp only [mixedDistance]
    nlinarith
  | covered i =>
    obtain ⟨e, he, heloc⟩ := hcenter i
    have hb := virtualNearest_le_ball G w radius M s i
    have hc := cappedCost_le_offer (virtualNearest G w radius M s) (fun e => dist s (loc e)) he
    rw [heloc] at hc
    exact add_le_add (mul_le_mul_of_nonneg_left hb ht0) (mul_le_mul_of_nonneg_left hc ht)
  | uncovered o => exact hd.elim

omit [PseudoMetricSpace V] in

lemma weighted_removal_bound {a : ℕ} (D T : Finset V)
    (assignment : V → Virtual V a) (mixed charge : V → ℝ)
    (hcharge : ∀ p ∈ D, ∀ s ∈ T, assignment p = Virtual.real s → mixed s ≤ charge p) :
    (∑ s ∈ T, assignmentWeight D assignment s * mixed s) ≤
      ∑ p ∈ assignedClients D T assignment, charge p := by
  classical
  have hs := sum_assignment_charges D assignment T id mixed
  simp only [id_eq] at hs
  rw [← hs, assignedClients, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hh : ∃ s ∈ T, assignment p = Virtual.real s
  · obtain ⟨s, hs, has⟩ := hh
    rw [ite_eq_left ⟨s, hs, has⟩]
    have he : (∑ r ∈ T, if assignment p = Virtual.real r then mixed r else 0) = mixed s := by
      rw [Finset.sum_eq_single s]
      · exact ite_eq_left has
      · intro r _ hrs
        apply ite_eq_right
        intro hr
        exact hrs (Virtual.real.inj (hr.symm.trans has))
      · exact fun hns => (hns hs).elim
    rw [he]
    exact hcharge p hp s hs has
  · rw [ite_eq_right hh]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro s hs
    exact ite_eq_right (fun he => hh ⟨s, hs, he⟩)

lemma interpolated_client_sum {P E : Type*} [DecidableEq P]
    (D J : Finset P) (hJ : J ⊆ D) (base : P → ℝ) (distance : P → E → ℝ)
    (X : Finset E) (theta : ℝ) (ht1 : theta ≤ 1) :
    (∑ p ∈ D, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ)) ≤
      (∑ p ∈ J, base p) +
      ∑ p ∈ D \ J, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ) := by
  rw [← Finset.sum_sdiff hJ (f := fun p => theta*base p +
    (1-theta)*cappedCost (base p) (distance p) X), add_comm]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro p _
  have hh := mul_le_mul_of_nonneg_left (cappedCost_le_base (base p) (distance p) X)
    (show 0 ≤ 1-theta by linarith)
  nlinarith

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClientCharge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma selectedDestination_mem {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    selectedDestination theta center w radius Ω hΩ s ∈ Ω :=
  (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).1

omit [DecidableEq V] in
lemma selectedDestination_distance {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    mixedDistance theta center w radius s (selectedDestination theta center w radius Ω hΩ s) =
      minimumMixed theta center w radius Ω hΩ s := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun d hd =>
      (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).2 d hd)
  · exact Finset.inf'_le _ (selectedDestination_mem theta center w radius Ω hΩ s)

omit [DecidableEq V] in
lemma mixedDistance_client_triangle {a : ℕ} (theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (center w : Fin a → V) (radius : Fin a → ℝ)
    (s p : V) (d : Destination V a) :
    mixedDistance theta center w radius s d ≤ dist p s + clientCharge theta center w radius p d := by
  cases d with
  | proxy φ => simpa only [mixedDistance,clientCharge,dist_comm s p] using dist_triangle s p φ
  | covered i => simpa only [clientCharge,add_assoc] using mixedDistance_covered_triangle theta ht0 ht1 center w radius s p i
  | uncovered i => simpa only [mixedDistance,clientCharge,dist_comm s p] using dist_triangle s p i

lemma removal_comparison_charge {a : ℕ} (D H Rstar : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (assignment : V → Virtual V a)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (own : V → Destination V a)
    (hown : ∀ p ∈ D, own p ∈ Ω) :
    (∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) ≤
      (∑ p ∈ assignedClients D Rstar assignment, virtualNearest H w radius M p) +
      ∑ p ∈ assignedClients D Rstar assignment, clientCharge theta center w radius p (own p) := by
  rw [← Finset.sum_add_distrib]
  apply weighted_removal_bound
  intro p hp s _ has
  have hh := (Finset.inf'_le (mixedDistance theta center w radius s) (hown p hp)).trans
    (mixedDistance_client_triangle theta ht0 ht1 center w radius s p (own p))
  have hd := hadist p
  simp only [has,virtualDistance] at hd
  change minimumMixed theta center w radius Ω hΩ s ≤ virtualNearest H w radius M p + _
  rw [← hd]
  exact hh

lemma surrogate_comparison_bound {E R : Type*} [DecidableEq E] [Fintype R]
    {a q : ℕ} (D H G Rstar Blue : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta K : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (assignment : V → Virtual V a) (redLoc : R → V) (hredInj : Function.Injective redLoc)
    (T : Finset R) (hT : T.card = q)
    (hdisj : Disjoint (T.image redLoc) Blue) (hcover : T.image redLoc ∪ Blue = Rstar)
    (loc : E → V) (X : Finset E) (hcenter : ∀ i, ∃ e ∈ X, loc e = center i)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty)
    (hredDest : ∀ r ∈ T,
      match selectedDestination theta center w radius Ω hΩ (redLoc r) with
      | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
    (hK : K ≤ ∑ s ∈ Blue, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest H w radius M p) (fun p e => dist (p:V) (loc e))
      (fun r => assignmentWeight D assignment (redLoc r))
      (fun r => virtualNearest G w radius M (redLoc r)) (fun r e => dist (redLoc r) (loc e))
    theta * Ψ ∅ + (1-theta) * Ψ X ≤
      (∑ p ∈ D, (theta * virtualNearest H w radius M p + (1-theta) *
        cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)) +
      ∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s := by
  dsimp only
  have hh := convex_surrogate_upper K q
    (fun p : ↥D => virtualNearest H w radius M p) (fun p e => dist (p:V) (loc e))
    (fun r => assignmentWeight D assignment (redLoc r))
    (fun r => virtualNearest G w radius M (redLoc r)) (fun r e => dist (redLoc r) (loc e))
    theta ht0 ht1 T hT X
  rw [Finset.sum_coe_sort D (fun p => theta * virtualNearest H w radius M p + (1-theta) *
    cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)] at hh
  refine hh.trans ?_
  have hred : (∑ r ∈ T, assignmentWeight D assignment (redLoc r) *
      (theta * virtualNearest G w radius M (redLoc r) + (1-theta) *
        cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X)) ≤
      ∑ s ∈ T.image redLoc, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s := by
    rw [Finset.sum_image (fun r _ r' _ he => hredInj he)]
    apply Finset.sum_le_sum
    intro r hr
    apply mul_le_mul_of_nonneg_left _ (assignmentWeight_nonneg _ _ _)
    have hrule := red_mixed_comparison G loc X center w radius M theta ht0 ht1 hcenter (redLoc r)
      (selectedDestination theta center w radius Ω hΩ (redLoc r)) (hredDest r hr)
    rwa [selectedDestination_distance] at hrule
  rw [← hcover,Finset.sum_union hdisj]
  linarith

lemma completion_endpoint_bound {E : Type*} {a : ℕ} (D H Rstar : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (assignment : V → Virtual V a)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (own : V → Destination V a)
    (hown : ∀ p ∈ D, own p ∈ Ω) (loc : E → V) (X : Finset E) :
    (∑ p ∈ D, (theta * virtualNearest H w radius M p + (1-theta) *
      cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)) +
      (∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) ≤
    2 * (∑ p ∈ assignedClients D Rstar assignment, virtualNearest H w radius M p) +
      (∑ p ∈ assignedClients D Rstar assignment, clientCharge theta center w radius p (own p)) +
      ∑ p ∈ D \ assignedClients D Rstar assignment,
        (theta * virtualNearest H w radius M p + (1-theta) *
          cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X) := by
  have hb := interpolated_client_sum D (assignedClients D Rstar assignment)
    (Finset.filter_subset _ _) (virtualNearest H w radius M) (fun p e => dist p (loc e)) X theta ht1
  have hr := removal_comparison_charge D H Rstar w center radius M theta ht0 ht1 assignment hadist Ω hΩ own hown
  linarith

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destinations
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma own_charge_good (C : Comparison D S O) (s : State V) (theta : ℝ)
    (p o : V) (ho : o ∈ C.good) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) = dist p (C.proxy o) := by
  simp [ownDestination, hp, ho, clientCharge]

lemma own_charge_covered (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (theta : ℝ)
    (p o : V) (ho : o ∈ C.covered s) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) =
      dist p o + theta * (dist (C.leaderPair s o).1 o + (C.leaderPair s o).2) := by
  have hn : o ∉ C.good := (Finset.mem_sdiff.mp (C.correct_covered_subset hD kappa s hs ho)).2
  simp only [ownDestination, hp, ite_eq_right hn, dite_eq_left ho, clientCharge,
    coveredIndex_spec, leafCenter, leafRadius, C.leafPair_index hD kappa s hs o ho]

lemma own_charge_uncovered (C : Comparison D S O) (s : State V) (theta : ℝ)
    (p o : V) (ho : o ∈ C.bad \ C.covered s) (hp : C.assign p = o) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) = dist p o := by
  have hg : o ∉ C.good := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).2
  have hc := (Finset.mem_sdiff.mp ho).2
  simp [ownDestination, hp, hg, hc, clientCharge]

lemma interpolated_reference_le (Δ : ℝ) (s : State V)
    {E : Type*} (loc : E → V) (X : Finset E) (theta : ℝ) (ht : theta ≤ 1) (p : V) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤ reference S Δ s p := by
  have hh := cappedCost_le_base (reference S Δ s p) (fun e => dist p (loc e)) X
  nlinarith [mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ht)]

lemma interpolated_covered_charge (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (_hs : C.Correct hD kappa s)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (p o : V) (ho : o ∈ C.covered s) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤
      dist p o + theta * (dist (C.leaderPair s o).1 o + (C.leaderPair s o).2) := by
  let i := C.coveredIndex s o ho
  obtain ⟨e, he, heo⟩ := hcenter i
  have hei : C.coveredCenter s i = o := C.coveredIndex_spec s o ho
  have heo' : loc e = o := heo.trans hei
  have hc := cappedCost_le_offer (reference S Δ s p) (fun e => dist p (loc e)) he
  rw [heo'] at hc
  have hw := C.leaderPair_spec s o ho
  obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hw.1
  have href := reference_le_leaf S Δ s p j (C.leaderPair s o)
    (by simp only [List.getElem?_eq_getElem hj, hjz])
  have tri := dist_triangle p o (C.leaderPair s o).1
  rw [dist_comm o (C.leaderPair s o).1] at tri
  have hc' := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr ht1)
  have hr' := mul_le_mul_of_nonneg_left href ht0
  have ht' := mul_le_mul_of_nonneg_left tri ht0
  nlinarith

lemma own_charge_le_endpoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (theta : ℝ) (J : Finset V) (p : V) (hp : p ∈ D) (hpJ : p ∈ J) :
    clientCharge theta (C.coveredCenter s) (leafCenter s) (leafRadius s) p
      (C.ownDestination s p) ≤ C.endpointCharge Δ s theta J p := by
  by_cases hg : C.assign p ∈ C.good
  · rw [C.own_charge_good s theta p (C.assign p) hg rfl]
    simp [endpointCharge,hg]
  by_cases hc : C.assign p ∈ C.covered s
  · rw [C.own_charge_covered hD kappa s hs theta p (C.assign p) hc rfl]
    simp [endpointCharge,hg,hc]
  · have hb : C.assign p ∈ C.bad \ C.covered s :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨C.assigned p hp,hg⟩,hc⟩
    rw [C.own_charge_uncovered s theta p (C.assign p) hb rfl]
    simp [endpointCharge,hg,hc,hpJ]

lemma interpolation_le_endpoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (J : Finset V) (p : V) (hpJ : p ∉ J) :
    theta * reference S Δ s p + (1-theta) *
      cappedCost (reference S Δ s p) (fun e => dist p (loc e)) X ≤
      C.endpointCharge Δ s theta J p := by
  by_cases hg : C.assign p ∈ C.good
  · simp only [endpointCharge,ite_eq_left hg]
    exact (interpolated_reference_le Δ s loc X theta ht1 p).trans
      (reference_le_real S Δ s p (C.proxy (C.assign p))
        (C.proxy_survives s hs.1 (C.assign p) hg))
  by_cases hc : C.assign p ∈ C.covered s
  · simp only [endpointCharge,ite_eq_right hg,ite_eq_left hc]
    exact C.interpolated_covered_charge hD kappa Δ s hs loc X hcenter theta ht0 ht1 p (C.assign p) hc
  · simp only [endpointCharge,ite_eq_right hg,ite_eq_right hc,ite_eq_right hpJ]
    exact interpolated_reference_le Δ s loc X theta ht1 p

lemma endpoint_charge_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (theta : ℝ) (J : Finset V) :
    (∑ p ∈ D, C.endpointCharge Δ s theta J p) =
      (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
      (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
        (dist p o+theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
      (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
        if p ∈ J then dist p o else reference S Δ s p) := by
  rw [← cluster_partition D O C.assign C.assigned (C.endpointCharge Δ s theta J)]
  rw [C.center_sum_partition s (C.correct_covered_subset hD kappa s hs)
    (fun o => ∑ p ∈ cluster D C.assign o, C.endpointCharge Δ s theta J p)]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro o ho
      apply Finset.sum_congr rfl
      intro p hp
      simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_left ho]
    · apply Finset.sum_congr rfl
      intro o ho
      have hn := (Finset.mem_sdiff.mp (C.correct_covered_subset hD kappa s hs ho)).2
      apply Finset.sum_congr rfl
      intro p hp
      simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_right hn,ite_eq_left ho]
  · apply Finset.sum_congr rfl
    intro o ho
    have hc := (Finset.mem_sdiff.mp ho).2
    have hg := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).2
    apply Finset.sum_congr rfl
    intro p hp
    simp only [endpointCharge,(cluster_mem D C.assign p o).mp hp |>.2,ite_eq_right hg,ite_eq_right hc]

lemma completion_endpoint_success (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    {E : Type*} (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i) :
    let J := assignedClients D (C.nonproxy \ s.deleted) (completionAssignment S Δ s)
    2 * (∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) +
      (∑ p ∈ J, clientCharge (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s) p
        (C.ownDestination s p)) +
      ∑ p ∈ D \ J, ((19/50) * virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p +
        (1-19/50) * cappedCost (virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
          (fun e => dist p (loc e)) X) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  dsimp only
  let J := assignedClients D (C.nonproxy \ s.deleted) (completionAssignment S Δ s)
  have hJD : J ⊆ D := Finset.filter_subset _ _
  have hsum := C.successful_completion_charge_s238 hD Δ s hs hΔ hP hm J (C.removalTotal Δ s) hI hT
  have hemp := C.endpoint_charge_sum hD (1/1000000) Δ s hs (19/50) J
  have hsum' : 2*C.removalTotal Δ s + (∑ p ∈ D, C.endpointCharge Δ s (19/50) J p) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by linarith
  have h₁ := Finset.sum_le_sum (s := J) (fun p hp =>
    C.own_charge_le_endpoint hD (1/1000000) Δ s hs (19/50) J p (hJD hp) hp)
  have h₂ := Finset.sum_le_sum (s := D \ J) (fun p hp =>
    C.interpolation_le_endpoint hD (1/1000000) Δ s hs loc X hcenter
      (19/50) (by norm_num) (by norm_num) J p (Finset.mem_sdiff.mp hp).2)
  have hsplit := Finset.sum_sdiff hJD (f := C.endpointCharge Δ s (19/50) J)
  have hIeq : (∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) =
      C.removalTotal Δ s := assigned_reference_total_agree D S (C.nonproxy \ s.deleted) Δ s
  change 2*(∑ p ∈ J, virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) +
    (∑ p ∈ J, _) + (∑ p ∈ D \ J, _) ≤ _
  rw [hIeq]
  simp_rw [← reference_eq_virtualNearest] at ⊢
  linarith

lemma surrogate_success_s238_oai {E R : Type*} [DecidableEq E] [Fintype R]
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (loc : E → V) (X : Finset E)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = C.coveredCenter s i)
    (G Blue : Finset V) (redLoc : R → V) (hredInj : Function.Injective redLoc)
    (q : ℕ) (T : Finset R) (hT : T.card = q)
    (hdisj : Disjoint (T.image redLoc) Blue)
    (hcover : T.image redLoc ∪ Blue = C.nonproxy \ s.deleted)
    (hredDest : ∀ r ∈ T,
      match selectedDestination (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
          (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
      | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
    (K : ℝ)
    (hK : K ≤ ∑ u ∈ Blue, assignmentWeight D (completionAssignment S Δ s) u *
      minimumMixed (19/50) (C.coveredCenter s) (leafCenter s) (leafRadius s)
        (C.destinations s) (C.destinations_nonempty hD s) u) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p)
      (fun p e => dist (p:V) (loc e))
      (fun r => assignmentWeight D (completionAssignment S Δ s) (redLoc r))
      (fun r => virtualNearest G (leafCenter s) (leafRadius s) Δ (redLoc r))
      (fun r e => dist (redLoc r) (loc e))
    (19/50)*Ψ ∅+(1-19/50)*Ψ X ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  dsimp only
  have h₁ := surrogate_comparison_bound D (S \ s.deleted) G (C.nonproxy \ s.deleted) Blue
    (leafCenter s) (C.coveredCenter s) (leafRadius s) Δ (19/50) K (by norm_num) (by norm_num)
    (completionAssignment S Δ s) redLoc hredInj T hT hdisj hcover loc X hcenter
    (C.destinations s) (C.destinations_nonempty hD s) (fun r hr => by
      have hh := hredDest r hr
      cases hd : selectedDestination (19/50) (C.coveredCenter s) (leafCenter s)
          (leafRadius s) (C.destinations s) (C.destinations_nonempty hD s) (redLoc r) with
      | proxy φ => simpa only [hd] using hh
      | covered i => trivial
      | uncovered v => simp only [hd] at hh) hK
  have h₂ := completion_endpoint_bound D (S \ s.deleted) (C.nonproxy \ s.deleted)
    (leafCenter s) (C.coveredCenter s) (leafRadius s) Δ (19/50) (by norm_num) (by norm_num)
    (completionAssignment S Δ s) (completionAssignment_distance S Δ s)
    (C.destinations s) (C.destinations_nonempty hD s) (C.ownDestination s)
    (C.ownDestination_mem s) loc X
  exact h₁.trans (h₂.trans (C.completion_endpoint_success hD Δ s hs hΔ hP hm hI hN loc X hcenter))

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238_oai.{u_1, u_2, u_3} := @OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238_oai.{u_1, u_2, u_3}

-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:31:34.593973+00:00
-- url     : https://prove2.me/submissions/71a73fad-f11a-4683-87a3-6921c511ffca

import Mathlib
import Definitions.Def_Q238L011

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

lemma radius_minimal (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {q : ℝ} (_hq : 0 ≤ q)
    (hpop : P / m ≤ q * (ball D w q).card) : radius D hn P m w ≤ q := by
  have hpos : (0 : ℝ) < P / m := div_pos hP (Nat.cast_pos.mpr hm)
  have hc : (0 : ℝ) < (ball D w q).card := by
    by_contra hh
    have he : ((ball D w q).card : ℝ) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
    rw [he, mul_zero] at hpop
    linarith
  have hne : (ball D w q).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hc)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (ball D w q) (dist w) hne
  have hpeq : ball D w (dist w p) = ball D w q := by
    apply Finset.Subset.antisymm (ball_mono D w (Finset.mem_filter.mp hp).2)
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hmax x hx⟩
  have hdiv : P / ((m : ℝ)*(ball D w q).card) ≤ q := by
    apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hm) hc)).mpr
    have hh := (div_le_iff₀ (Nat.cast_pos.mpr hm)).mp hpop
    nlinarith
  apply (Finset.inf'_le (candidate D P m w) (Finset.mem_filter.mp hp).1).trans
  exact max_le (Finset.mem_filter.mp hp).2 (by simpa only [hpeq] using hdiv)

omit [PseudoMetricSpace V] in

lemma sublevel_card [DecidableEq V] (C : Finset V) (f : V → ℝ) (hf : ∀ p ∈ C, 0 ≤ f p)
    (mean a : ℝ) (hmean : ∑ p ∈ C, f p = mean * C.card) (ha : 0 < a) :
    (1-1/a) * (C.card : ℝ) ≤ ((C.filter (fun p => f p ≤ a*mean)).card : ℝ) := by
  classical
  let N := C.filter (fun p => f p ≤ a*mean)
  by_cases hm : mean = 0
  · have hzero : ∀ p ∈ C, f p = 0 := by
      have hs : ∑ p ∈ C, f p = 0 := by simpa only [hm, zero_mul] using hmean
      exact (Finset.sum_eq_zero_iff_of_nonneg hf).mp hs
    have hN : N = C := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      simp [hzero p hp, hm]
    change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
    rw [hN]
    nlinarith [mul_nonneg (one_div_pos.mpr ha).le (Nat.cast_nonneg (α := ℝ) C.card)]
  · by_cases hn : C.Nonempty
    · have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hn)
      have hmn : 0 < mean := by
        have hs : 0 ≤ mean * C.card := hmean ▸ Finset.sum_nonneg hf
        exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left hs hc) (Ne.symm hm)
      have hh : (a*mean) * ((C \ N).card : ℝ) ≤ ∑ p ∈ C \ N, f p := by
        calc
          _ = ∑ _p ∈ C \ N, a*mean := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun p hp => by
            have hnp := (Finset.mem_sdiff.mp hp).2
            have hpC := (Finset.mem_sdiff.mp hp).1
            exact (lt_of_not_ge (fun h => hnp (Finset.mem_filter.mpr ⟨hpC,h⟩))).le)
      have hs : (∑ p ∈ C \ N, f p) ≤ mean * C.card := by
        rw [← hmean]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ => hf p hp)
      have hcard := Finset.card_sdiff_add_card_eq_card (show N ⊆ C from Finset.filter_subset _ _)
      have hcard' : ((C \ N).card : ℝ) + (N.card : ℝ) = C.card := by exact_mod_cast hcard
      change (1-1/a)*(C.card : ℝ) ≤ (N.card : ℝ)
      have hmc : a*((C \ N).card : ℝ) ≤ C.card := by
        nlinarith [hh.trans hs]
      apply (mul_le_mul_iff_right₀ ha).mp
      field_simp
      nlinarith
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, mul_zero,
        Finset.filter_empty, le_refl]

lemma leader_radius_le [DecidableEq V] (D C : Finset V) (hn : D.Nonempty)
    (hC : C.Nonempty) (hCD : C ⊆ D) (P : ℝ) (m : ℕ) (w o : V)
    (mean a : ℝ) (hP : 0 < P) (hm : 0 < m) (ha : 0 ≤ a)
    (hmean : ∑ p ∈ C, dist p o = mean * C.card)
    (hnear : dist w o ≤ a * mean) :
    radius D hn P m w ≤ (a+2)*mean + 2*P/((m : ℝ)*C.card) := by
  classical
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm0 : 0 ≤ mean := by
    have hh : 0 ≤ mean*C.card := hmean ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)
    exact nonneg_of_mul_nonneg_left hh hc
  let Q := (a+2)*mean + 2*P/((m : ℝ)*C.card)
  let N := C.filter (fun p => dist p o ≤ 2*mean)
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg (by linarith) hm0)
    (div_nonneg (by positivity) (mul_pos hm' hc).le)
  have hN : (C.card : ℝ)/2 ≤ N.card := by
    have hh := sublevel_card C (fun p => dist p o) (fun _ _ => dist_nonneg)
      mean 2 hmean (by norm_num)
    norm_num at hh
    linarith
  have hsub : N ⊆ ball D w Q := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hCD hp'.1, ?_⟩
    have ht := dist_triangle w o p
    rw [dist_comm o p] at ht
    have hnterm : 0 ≤ 2*P/((m : ℝ)*C.card) := div_nonneg (by positivity) (mul_pos hm' hc).le
    dsimp [Q]
    nlinarith [hp'.2]
  have hcard : (C.card : ℝ)/2 ≤ (ball D w Q).card := hN.trans (by
    exact_mod_cast Finset.card_le_card hsub)
  apply radius_minimal D hn P m w hP hm hQ
  calc
    P/(m : ℝ) = (2*P/((m : ℝ)*C.card)) * ((C.card : ℝ)/2) := by field_simp
    _ ≤ Q * ((C.card : ℝ)/2) := mul_le_mul_of_nonneg_right
      (by dsimp [Q] <;> nlinarith [mul_nonneg (show 0 ≤ a+2 by linarith) hm0]) (by positivity)
    _ ≤ Q * (ball D w Q).card := mul_le_mul_of_nonneg_left hcard hQ

end MetricKMedianRecovery.Population

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
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
lemma cluster_subset (D : Finset V) (c : V → V) (o : V) : cluster D c o ⊆ D :=
  Finset.filter_subset _ _

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

lemma clusterCost_nonneg (D : Finset V) (c : V → V) (o : V) : 0 ≤ clusterCost D c o :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma clusterMean_mul_card (D : Finset V) (c : V → V) (o : V) :
    clusterMean D c o * (cluster D c o).card = clusterCost D c o := by
  by_cases h : (cluster D c o).card = 0
  · have he := Finset.card_eq_zero.mp h
    simp [clusterMean, clusterCost, he]
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

lemma comparisonCost_eq (D O : Finset V) (c : V → V) (hc : ∀ p ∈ D, c p ∈ O) :
    (∑ o ∈ O, clusterCost D c o) = comparisonCost D c := by
  have hh := cluster_partition D O c hc (fun p => dist p (c p))
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p hp
  rw [(cluster_mem D c p o).mp hp |>.2]

namespace Comparison
variable {D S O : Finset V}

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
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

lemma covered_population_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, (cluster D C.assign o).card *
      Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) ≤
      (26/5:ℝ)*comparisonCost D C.assign := by
  have hpoint : ∀ o ∈ C.covered s,
      (cluster D C.assign o).card *
        Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 ≤
          (16/5:ℝ)*clusterCost D C.assign o+2*comparisonCost D C.assign/C.bad.card := by
    intro o ho
    have hp := C.leaderPair_spec s o ho
    have hc := hs.2.2 _ hp.1
    have hC : (cluster D C.assign o).Nonempty :=
      ⟨(C.leaderPair s o).1,(cluster_mem _ _ _ _).mpr ⟨hc.1,hp.2⟩⟩
    have hn : (0:ℝ) < (cluster D C.assign o).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
    have hmR : (0:ℝ) < C.bad.card := Nat.cast_pos.mpr hm
    have hnear : dist (C.leaderPair s o).1 o ≤ (6/5:ℝ)*clusterMean D C.assign o := by
      simpa only [hp.2] using hc.2.2.1
    have hh := Population.leader_radius_le D (cluster D C.assign o) hD hC
      (cluster_subset _ _ _) (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 o
      (clusterMean D C.assign o) (6/5) hP hm (by norm_num)
      (clusterMean_mul_card _ _ _).symm hnear
    have he : ((6/5+2:ℝ)*clusterMean D C.assign o+
        2*comparisonCost D C.assign/((C.bad.card:ℝ)*(cluster D C.assign o).card))*
          (cluster D C.assign o).card =
        (16/5:ℝ)*clusterCost D C.assign o+2*comparisonCost D C.assign/C.bad.card := by
      rw [add_mul,mul_assoc,clusterMean_mul_card]
      field_simp
      ring
    have hh' := mul_le_mul_of_nonneg_right hh hn.le
    rw [he] at hh'
    simpa only [mul_comm] using hh'
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hsum
  have hsub := C.correct_covered_subset hD kappa s hs
  have hcard : ((C.covered s).card:ℝ) ≤ C.bad.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hmR : (0:ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hc := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ 2*comparisonCost D C.assign/(C.bad.card:ℝ) by positivity)
  have he : (C.bad.card:ℝ)*(2*comparisonCost D C.assign/C.bad.card) =
      2*comparisonCost D C.assign := by field_simp
  rw [he] at hc
  have hPA : (∑ o ∈ C.covered s, clusterCost D C.assign o) ≤ comparisonCost D C.assign := by
    rw [← comparisonCost_eq D O C.assign C.assigned]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsub.trans Finset.sdiff_subset)
      (fun o _ _ => clusterCost_nonneg _ _ o)
  linarith

lemma covered_completion_sum_s238r_oai (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (hk : 0 ≤ kappa) (ht : 0 ≤ theta)
    (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
      (dist p o + theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
      (1+theta*(2+kappa)*(6/5:ℝ))*(∑ o ∈ C.covered s, clusterCost D C.assign o)+
        theta*kappa*(26/5:ℝ)*comparisonCost D C.assign := by
  have hpoint : ∀ o ∈ C.covered s,
      (∑ p ∈ cluster D C.assign o,
        (dist p o+theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
      (1+theta*(2+kappa)*(6/5:ℝ))*clusterCost D C.assign o+
        theta*kappa*((cluster D C.assign o).card *
          Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) := by
    intro o ho
    have hp := C.leaderPair_spec s o ho
    have hc := hs.2.2 _ hp.1
    have hnear : dist (C.leaderPair s o).1 o ≤ (6/5:ℝ)*clusterMean D C.assign o := by
      simpa only [hp.2] using hc.2.2.1
    have hrad : (C.leaderPair s o).2 ≤ (1+kappa)*dist (C.leaderPair s o).1 o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 := by
      simpa only [hp.2] using hc.2.2.2.2.2
    have hadd : dist (C.leaderPair s o).1 o+(C.leaderPair s o).2 ≤
        (2+kappa)*(6/5:ℝ)*clusterMean D C.assign o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 := by
      have hh := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 2+kappa by linarith)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hadd
      (mul_nonneg (Nat.cast_nonneg (cluster D C.assign o).card) ht)
    have he : (cluster D C.assign o).card * theta *
        ((2+kappa)*(6/5:ℝ)*clusterMean D C.assign o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) =
      theta*(2+kappa)*(6/5:ℝ)*clusterCost D C.assign o+
        theta*kappa*((cluster D C.assign o).card *
          Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) := by
      rw [← clusterMean_mul_card D C.assign o]
      ring
    rw [he] at hh
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    change clusterCost D C.assign o + _ ≤ _
    nlinarith
  have hh := Finset.sum_le_sum hpoint
  conv at hh => rhs; rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hp := mul_le_mul_of_nonneg_left (C.covered_population_sum hD kappa s hs hP hm)
    (mul_nonneg ht hk)
  nlinarith

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238r_oai.{u_1}

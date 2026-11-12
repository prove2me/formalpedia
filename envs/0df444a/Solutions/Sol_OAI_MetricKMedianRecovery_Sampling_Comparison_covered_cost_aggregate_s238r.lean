-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:31:35.620127+00:00
-- url     : https://prove2.me/submissions/3a23f29c-db2d-4556-af9b-b4241fc3153f

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma leaf_mem_tags (S : Finset V) (s : State V) (j : ℕ) :
    leafTag j ∈ tags S s ↔ j ≤ s.leaves.length := by
  simp [tags, realTag, leafTag]

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

lemma reference_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) : reference S Δ s x ≤ tagDistance Δ s x t :=
  Prod.Lex.monotone_fst _ _ (chosen_key_le S Δ s x ht)

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
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
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

lemma clusterMean_mul_card (D : Finset V) (c : V → V) (o : V) :
    clusterMean D c o * (cluster D c o).card = clusterCost D c o := by
  by_cases h : (cluster D c o).card = 0
  · have he := Finset.card_eq_zero.mp h
    simp [clusterMean, clusterCost, he]
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

namespace Comparison
variable {D S O : Finset V}

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma reference_leaf_mem (Δ : ℝ) (s : State V) (z : V × ℝ) (hz : z ∈ s.leaves) (p : V) :
    reference S Δ s p ≤ dist p z.1+z.2 := by
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hz
  exact reference_le_leaf S Δ s p j z hj

lemma covered_client_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (_hs : C.Correct hD kappa s)
    (z : V × ℝ) (hz : z ∈ s.leaves) (p : V) :
    reference S Δ s p ≤ dist p (C.assign z.1) + dist z.1 (C.assign z.1) + z.2 := by
  have hh := reference_leaf_mem (S := S) Δ s z hz p
  have ht := dist_triangle p (C.assign z.1) z.1
  rw [dist_comm (C.assign z.1) z.1] at ht
  linarith

lemma covered_cluster_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hk : 0 ≤ kappa) (hm : 0 < C.bad.card)
    (o : V) (ho : o ∈ C.covered s) :
    (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (17/5+(22/5)*kappa)*clusterCost D C.assign o +
        2*kappa*comparisonCost D C.assign/C.bad.card := by
  obtain ⟨z,hz,he⟩ := C.covered_witness s o ho
  have hc := hs.2.2 z hz
  have hC : (cluster D C.assign o).Nonempty :=
    ⟨z.1,(cluster_mem D C.assign z.1 o).mpr ⟨hc.1,he⟩⟩
  have hn : (0 : ℝ) < (cluster D C.assign o).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hmR : (0 : ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hnear : dist z.1 o ≤ (6/5 : ℝ)*clusterMean D C.assign o := by simpa only [he] using hc.2.2.1
  have hrad : z.2 ≤ (1+kappa)*dist z.1 o +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1 := by
    simpa only [he] using hc.2.2.2.2.2
  have hq := Population.leader_radius_le D (cluster D C.assign o) hD hC
    (cluster_subset D C.assign o) (comparisonCost D C.assign) C.bad.card z.1 o
    (clusterMean D C.assign o) (6/5) hP hm (by norm_num)
    (clusterMean_mul_card D C.assign o).symm hnear
  have hsumb : (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      clusterCost D C.assign o +
        (dist z.1 o+z.2)*(cluster D C.assign o).card := by
    calc
      _ ≤ ∑ p ∈ cluster D C.assign o, (dist p o+(dist z.1 o+z.2)) := by
        apply Finset.sum_le_sum
        intro p _
        have hp := C.covered_client_bound hD kappa Δ s hs z hz p
        simpa only [he, add_assoc] using hp
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, clusterCost] <;> ring
  have hu : dist z.1 o+z.2 ≤
      (12/5+(22/5)*kappa)*clusterMean D C.assign o +
        kappa*(2*comparisonCost D C.assign/((C.bad.card : ℝ)*(cluster D C.assign o).card)) := by
    have hqk := mul_le_mul_of_nonneg_left hq hk
    have hnk := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 2+kappa by linarith)
    nlinarith
  have hum := mul_le_mul_of_nonneg_right hu hn.le
  have heq : (kappa*(2*comparisonCost D C.assign /
      ((C.bad.card : ℝ)*(cluster D C.assign o).card)))*(cluster D C.assign o).card =
      2*kappa*comparisonCost D C.assign/C.bad.card := by field_simp
  have hrhs : ((12/5+(22/5)*kappa)*clusterMean D C.assign o +
      kappa*(2*comparisonCost D C.assign/((C.bad.card : ℝ)*(cluster D C.assign o).card)))*
        (cluster D C.assign o).card =
      (12/5+(22/5)*kappa)*clusterCost D C.assign o+
        2*kappa*comparisonCost D C.assign/C.bad.card := by
    rw [add_mul, mul_assoc, clusterMean_mul_card, heq]
  rw [hrhs] at hum
  linarith

lemma covered_cost_aggregate_s238r_oai (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hk : 0 ≤ kappa) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (17/5+(22/5)*kappa)*(∑ o ∈ C.covered s, clusterCost D C.assign o) +
        2*kappa*comparisonCost D C.assign := by
  have hh := Finset.sum_le_sum (fun o ho => C.covered_cluster_bound hD kappa Δ s hs hP hk hm o ho)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
  have hcard : ((C.covered s).card : ℝ) ≤ C.bad.card := by
    exact_mod_cast Finset.card_le_card (C.correct_covered_subset hD kappa s hs)
  have hmR : (0 : ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hc : 0 ≤ 2*kappa*comparisonCost D C.assign/(C.bad.card : ℝ) :=
    div_nonneg (by positivity) hmR.le
  have hn := mul_le_mul_of_nonneg_right hcard hc
  have he : (C.bad.card : ℝ)*(2*kappa*comparisonCost D C.assign/C.bad.card) =
      2*kappa*comparisonCost D C.assign := by field_simp
  rw [he] at hn
  linarith

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238r_oai.{u_1}

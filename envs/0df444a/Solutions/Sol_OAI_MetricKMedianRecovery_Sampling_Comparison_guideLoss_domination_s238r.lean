-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:41:42.15142+00:00
-- url     : https://prove2.me/submissions/c3a910ef-d949-46e8-8b15-fec738650853

import Mathlib
import Definitions.Def_Q238L021
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_covered_cost_aggregate_s238r

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

omit [LinearOrder V] in
lemma tagDistance_triangle (Δ : ℝ) (s : State V) (x y : V) (t : Tag V) :
    tagDistance Δ s x t ≤ dist x y + tagDistance Δ s y t := by
  cases ht : ofLex t with
  | inl v => simpa only [tagDistance, ht] using dist_triangle x y v
  | inr j =>
    cases j with
    | zero => simp only [tagDistance, ht] <;> linarith [dist_nonneg (x := x) (y := y)]
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simp only [tagDistance, ht, hz] <;> linarith [dist_nonneg (x := x) (y := y)]
      | some z =>
        simp only [tagDistance, ht, hz]
        linarith [dist_triangle x y z.1]

lemma reference_triangle (S : Finset V) (Δ : ℝ) (s : State V) (x y : V) :
    reference S Δ s x ≤ dist x y + reference S Δ s y :=
  (reference_le S Δ s x (chosen_mem S Δ s y)).trans
    (tagDistance_triangle Δ s x y (chosen S Δ s y))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearMass
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.NearClients
variable {V : Type*}

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

lemma exists_le_average [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (f : V → ℝ) :
    ∃ p ∈ C, f p ≤ (∑ q ∈ C, f q)/(C.card : ℝ) := by
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image C f hC
  refine ⟨p,hp,?_⟩
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Finset.card_pos.mpr hC))).mpr
  calc
    _ = ∑ _q ∈ C, f p := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun q hq => hmin q hq)

lemma nearMass_nonneg [PseudoMetricSpace V] (C : Finset V)
    (o : V) (mean a : ℝ) (H : V → ℝ) (hH : ∀ p ∈ C, 0 ≤ H p) :
    0 ≤ nearMass C o mean a H := by
  classical
  exact Finset.sum_nonneg (fun p hp => hH p (Finset.mem_filter.mp hp).1)

variable [PseudoMetricSpace V]

lemma center_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o : V)
    (mean a b : ℝ) (H : V → ℝ) (hmean : ∑ p ∈ C, dist p o = mean*C.card)
    (hb : 1 < b) (hba : b ≤ a) (hH : ∀ p ∈ C, 0 ≤ H p)
    (htri : ∀ p ∈ C, H o ≤ dist p o + H p) :
    H o ≤ b*mean + nearMass C o mean a H / ((1-1/b)*(C.card : ℝ)) := by
  classical
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hm : 0 ≤ mean := by
    have hh : 0 ≤ mean*C.card := hmean ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)
    exact nonneg_of_mul_nonneg_left hh hc
  let N := C.filter (fun p => dist p o ≤ b*mean)
  have hb0 : 0 < 1-1/b := by
    have hh := (div_lt_one (by linarith : 0 < b)).mpr hb
    linarith
  have hpop : (1-1/b)*(C.card : ℝ) ≤ N.card :=
    sublevel_card C (fun p => dist p o) (fun _ _ => dist_nonneg) mean b hmean (by linarith)
  have hN : N.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp ((mul_pos hb0 hc).trans_le hpop))
  obtain ⟨p,hp,hw⟩ := exists_le_average N hN H
  have hsub : N ⊆ C.filter (fun p => dist p o ≤ a*mean) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq'.1,hq'.2.trans (mul_le_mul_of_nonneg_right hba hm)⟩
  have hsum : (∑ q ∈ N, H q) ≤ nearMass C o mean a H :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hH q (Finset.mem_filter.mp hq).1)
  have hand : (∑ q ∈ N, H q)/(N.card : ℝ) ≤
      nearMass C o mean a H / ((1-1/b)*(C.card : ℝ)) := by
    apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans
    exact div_le_div_of_nonneg_left (nearMass_nonneg C o mean a H hH) (mul_pos hb0 hc) hpop
  have hp' := Finset.mem_filter.mp hp
  exact (htri p hp'.1).trans (add_le_add hp'.2 (hw.trans hand))

lemma main_center_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o : V)
    (mean : ℝ) (H : V → ℝ) (hmean : ∑ p ∈ C, dist p o = mean*C.card)
    (hH : ∀ p ∈ C, 0 ≤ H p) (htri : ∀ p ∈ C, H o ≤ dist p o + H p) :
    H o ≤ (51/50 : ℝ)*mean + 60*nearMass C o mean (6/5) H/(C.card : ℝ) := by
  have hh := center_bound C hC o mean (6/5) (51/50) H hmean (by norm_num) (by norm_num) hH htri
  norm_num at hh
  have hT := nearMass_nonneg C o mean (6/5) H hH
  have hc : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have he : nearMass C o mean (6/5) H / ((1/51 : ℝ)*C.card) =
      51*nearMass C o mean (6/5) H/(C.card : ℝ) := by field_simp
  rw [he] at hh
  apply hh.trans
  exact add_le_add_right (div_le_div_of_nonneg_right (by nlinarith : 51*nearMass C o mean (6/5) H ≤ 60*nearMass C o mean (6/5) H) hc.le) _

lemma main_far_bound [DecidableEq V] (C : Finset V) (hC : C.Nonempty) (o p : V)
    (mean : ℝ) (H : V → ℝ) (hmean : ∑ q ∈ C, dist q o = mean*C.card)
    (hH : ∀ q ∈ C, 0 ≤ H q) (htri : ∀ q ∈ C, H o ≤ dist q o + H q)
    (hp : H p ≤ dist p o + H o) (hfar : (6/5 : ℝ)*mean < dist p o) :
    H p ≤ (37/20 : ℝ)*dist p o + 60*nearMass C o mean (6/5) H/(C.card : ℝ) := by
  have hh := main_center_bound C hC o mean H hmean hH htri
  linarith

lemma ball_progress (P T W kappa : ℝ) (_hP : 0 < P) (hk : 0 < kappa)
    (hW : 0 < W) (hT : kappa*P < T) (hbound : W ≤ (171/50 : ℝ)*P+61*T) :
    progressConstant kappa ≤ T/(2*W) := by
  unfold progressConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

lemma removal_progress (P T I W kappa : ℝ) (_hP : 0 < P) (hk : 0 < kappa)
    (hW : 0 < W) (hT : T ≤ kappa*P) (hI : kappa*P < I)
    (hbound : W ≤ (171/50 : ℝ)*P+61*T) :
    progressConstant kappa ≤ I/(2*W) := by
  unfold progressConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

end MetricKMedianRecovery.NearClients

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
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

lemma proxy_survives (C : Comparison D S O) (s : State V) (hq : s.deleted ⊆ C.nonproxy)
    (o : V) (ho : o ∈ C.good) : C.proxy o ∈ S \ s.deleted := by
  refine Finset.mem_sdiff.mpr ⟨C.proxy_mem o ho, ?_⟩
  intro hh
  have hn := (Finset.mem_sdiff.mp (hq hh)).2
  exact hn (Finset.mem_image.mpr ⟨o,ho,rfl⟩)

lemma good_reference_bound (C : Comparison D S O) (Δ : ℝ) (s : State V)
    (hq : s.deleted ⊆ C.nonproxy) :
    (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (∑ o ∈ C.good, clusterCost D C.assign o) +
        (1/100 : ℝ)*comparisonCost D C.assign := by
  apply le_trans ?_ C.proxy_cost
  apply Finset.sum_le_sum
  intro o ho
  apply Finset.sum_le_sum
  intro p _
  exact reference_le_real S Δ s p (C.proxy o) (C.proxy_survives s hq o ho)

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma uncovered_cluster_bound (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) (o : V) :
    (∑ p ∈ cluster D C.assign o, reference S Δ s p) ≤
      (37/20 : ℝ)*clusterCost D C.assign o +
        61*(∑ p ∈ C.near o, reference S Δ s p) := by
  classical
  let X := cluster D C.assign o
  let H := reference S Δ s
  have hH : ∀ p : V, 0 ≤ H p := fun p => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs)
  by_cases hX : X.Nonempty
  · have hn : (0 : ℝ) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
    let T := ∑ p ∈ C.near o, H p
    have hT : 0 ≤ T := Finset.sum_nonneg (fun p _ => hH p)
    have hb : ∀ p ∈ X \ C.near o, H p ≤ (37/20 : ℝ)*dist p o + 60*T/X.card := by
      intro p hp
      have hpX := (Finset.mem_sdiff.mp hp).1
      have hfar : (6/5 : ℝ)*clusterMean D C.assign o < dist p o := by
        apply lt_of_not_ge
        intro hh
        exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpX,hh⟩)
      exact NearClients.main_far_bound X hX o p (clusterMean D C.assign o) H
        (clusterMean_mul_card D C.assign o).symm (fun q _ => hH q)
        (fun q _ => by simpa only [dist_comm o q] using reference_triangle S Δ s o q)
        (reference_triangle S Δ s p o) hfar
    have hnear : C.near o ⊆ X := Finset.filter_subset _ _
    have hpart := Finset.sum_sdiff hnear (f := H)
    have hcost : (∑ p ∈ X \ C.near o, dist p o) ≤ clusterCost D C.assign o :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => dist_nonneg)
    have hcard : ((X \ C.near o).card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have hfars : (∑ p ∈ X \ C.near o, H p) ≤ (37/20 : ℝ)*clusterCost D C.assign o + 60*T := by
      have hh := Finset.sum_le_sum hb
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
      have heq : (X.card : ℝ)*(60*T/X.card) = 60*T := by field_simp
      have htpos : 0 ≤ 60*T/(X.card : ℝ) := div_nonneg (by positivity) hn.le
      have hm := mul_le_mul_of_nonneg_right hcard htpos
      rw [heq] at hm
      nlinarith
    change (∑ p ∈ X, H p) ≤ (37/20 : ℝ)*clusterCost D C.assign o+61*T
    linarith
  · have he : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have hnear : C.near o = ∅ := by
      have hh : C.near o ⊆ X := Finset.filter_subset _ _
      rw [he] at hh
      exact Finset.subset_empty.mp hh
    simp only [show cluster D C.assign o = ∅ from he, Finset.sum_empty, clusterCost,
      hnear, mul_zero, add_zero, le_refl]

lemma center_sum_partition (C : Comparison D S O) (s : State V)
    (hA : C.covered s ⊆ C.bad) (f : V → ℝ) :
    (∑ o ∈ O, f o) = (∑ o ∈ C.good, f o) + (∑ o ∈ C.covered s, f o) +
      ∑ o ∈ C.bad \ C.covered s, f o := by
  have hg := Finset.sum_sdiff C.good_subset (f := f)
  have ha := Finset.sum_sdiff hA (f := f)
  change (∑ o ∈ C.bad, f o)+(∑ o ∈ C.good, f o) = ∑ o ∈ O, f o at hg
  linarith

lemma correct_weight_bound (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    totalWeight D S Δ s ≤ (171/50 : ℝ)*comparisonCost D C.assign+61*C.nearTotal Δ s := by
  have hA := C.correct_covered_subset hD (1/1000000) s hs
  have hW : totalWeight D S Δ s = ∑ p ∈ D, reference S Δ s p := by
    apply Finset.sum_congr rfl
    intro p _
    exact clientWeight_eq S Δ s p hΔ (C.correct_radii_nonneg hD (1/1000000) s hs)
  have hpart := C.center_sum_partition s hA (clusterCost D C.assign)
  rw [comparisonCost_eq D O C.assign C.assigned] at hpart
  have hRef := C.center_sum_partition s hA (fun o =>
    ∑ p ∈ cluster D C.assign o, reference S Δ s p)
  rw [cluster_partition D O C.assign C.assigned] at hRef
  have hG := C.good_reference_bound Δ s hs.1
  have hAA := C.covered_cost_aggregate_s238r hD (1/1000000) Δ s hs hP (by norm_num) hm
  have hBB := Finset.sum_le_sum (s := C.bad \ C.covered s) (fun o _ =>
    C.uncovered_cluster_bound hD (1/1000000) Δ s hs hΔ o)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hBB
  have hG0 : 0 ≤ ∑ o ∈ C.good, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg D C.assign o)
  have hB0 : 0 ≤ ∑ o ∈ C.bad \ C.covered s, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg D C.assign o)
  unfold nearTotal
  rw [hW]
  linarith

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedBest
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*} [Fintype A]
open scoped Classical

variable {I : Type*} [Fintype I]

lemma routed_at (q : Kernel S I) (route : S → I → A) (s : S)
    (hinj : Function.Injective (route s)) (i : I) :
    (routed q route).weight s (route s i) = q.weight s i := by
  classical
  simp only [routed, hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

lemma routed_pos (q : Kernel S I) (route : S → I → A) (s : S) (a : A)
    (h : 0 < (routed q route).weight s a) : ∃ i, route s i = a ∧ 0 < q.weight s i := by
  classical
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (show ∀ i ∈ (Finset.univ : Finset I), 0 ≤ if route s i = a then q.weight s i else 0 from
      fun i _ => by split_ifs; exact q.nonneg s i; exact le_rfl)).mp h
  by_cases he : route s i = a
  · exact ⟨i,he,by simpa only [ite_eq_left he] using hi⟩
  · simp only [ite_eq_right he, lt_self_iff_false] at hi

lemma routed_domination (p : Kernel S A) (q : Kernel S I) (route : S → I → A)
    (hinj : ∀ s, Function.Injective (route s)) (loss : S → A → ℝ)
    (hstep : ∀ s i, loss s (route s i)*q.weight s i ≤ p.weight s (route s i))
    (s : S) (a : A) : loss s a*(routed q route).weight s a ≤ p.weight s a := by
  by_cases hq : 0 < (routed q route).weight s a
  · obtain ⟨i,hi,_⟩ := routed_pos q route s a hq
    rw [← hi,routed_at q route s (hinj s) i]
    exact hstep s i
  · have he : (routed q route).weight s a = 0 := le_antisymm (le_of_not_gt hq) ((routed q route).nonneg s a)
    rw [he,mul_zero]
    exact p.nonneg s a

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

open scoped Classical

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

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
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

lemma weighted_ratio_bound (ρ H T W : ℝ) (hH : 0 ≤ H) (hT : 0 < T)
    (hr : ρ ≤ T/(2*W)) : ρ*(H/T) ≤ H/(2*W) := by
  have hh := mul_le_mul_of_nonneg_right hr (div_nonneg hH hT.le)
  have he : T/(2*W)*(H/T) = H/(2*W) := by
    by_cases hW : W = 0
    · simp [hW]
    · field_simp
  exact he ▸ hh

lemma activeGuide_domination (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s)
    (a : MainAction D C.bad.card) :
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a *
      (C.activeGuide hD Δ hΔ hP hm s hs ht).weight () a ≤
      (mainActual D S Δ C.bad.card).weight (some s) a := by
  have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
  have hbound := C.correct_weight_bound hD Δ s hs hΔ hP hm
  let p : Guided.Kernel Unit (MainAction D C.bad.card) :=
    ⟨fun _ a => (mainActual D S Δ C.bad.card).weight (some s) a,
      fun _ a => (mainActual D S Δ C.bad.card).nonneg (some s) a,
      fun _ => (mainActual D S Δ C.bad.card).total (some s)⟩
  change _ ≤ p.weight () a
  unfold activeGuide
  split_ifs with hb
  · refine Guided.routed_domination p _ _ (fun _ w v he => by
      simp only [Sum.inr.injEq,Prod.mk.injEq] at he; exact he.1)
      (fun _ a => NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a) ?_ () a
    intro u w
    change _ * (if w.val ∈ C.nearEligible s then
      clientWeight S Δ s w/C.nearTotal Δ s else 0) ≤ _
    by_cases hw : w.val ∈ C.nearEligible s
    · rw [ite_eq_left hw]
      have hr := NearClients.ball_progress _ _ _ _ hP mainKappa_pos hW hb hbound
      have hh := weighted_ratio_bound _ _ _ _ (clientWeight_nonneg S Δ s w)
        ((mul_pos mainKappa_pos hP).trans hb) hr
      simp only [p,mainActual,actualKernel,transitionWeight,ite_eq_left hW]
      change _ ≤ clientWeight S Δ s w/(2*totalWeight D S Δ s)*
        menuWeight (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
          (thirdSize mainKappa C.bad.card) (C.prescribedEntry hD hP hm s w)
      simpa only [actionMenuWeight,mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_right hh (menuWeight_nonneg _ _ _ (C.prescribedEntry hD hP hm s w))
    · rw [ite_eq_right hw,mul_zero]
      exact p.nonneg u _
  · refine Guided.routed_domination p _ _ (fun _ w v he => by simpa only [Sum.inr.injEq,Sum.inl.injEq] using he)
      (fun _ a => NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a) ?_ () a
    intro u w
    change _ * (if w.val ∈ C.removalEligible Δ s then
      clientWeight S Δ s w/C.removalTotal Δ s else 0) ≤ _
    by_cases hw : w.val ∈ C.removalEligible Δ s
    · rw [ite_eq_left hw]
      have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
        by_contra hh
        exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
      have hr := NearClients.removal_progress _ _ _ _ _ hP mainKappa_pos hW
        (le_of_not_gt hb) hi hbound
      have hh := weighted_ratio_bound _ _ _ _ (clientWeight_nonneg S Δ s w)
        ((mul_pos mainKappa_pos hP).trans hi) hr
      simpa only [actionMenuWeight,mul_one,p,mainActual,actualKernel,transitionWeight,ite_eq_left hW] using hh
    · rw [ite_eq_right hw,mul_zero]
      exact p.nonneg u _

lemma guideLoss_domination_s238r_oai (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    C.guideLoss hD Δ s a * (C.guideKernel hD Δ hΔ hP hm).weight s a ≤
      (C.stoppedActual hD Δ).weight s a := by
  cases s with
  | none =>
    have hstop : ¬C.stop hD Δ none := fun h => h
    have hg : ¬(C.Valid hD none ∧ ¬C.stop hD Δ none) := fun h => h.1
    simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,
      stoppedActual,Guided.stoppedKernel,ite_eq_right hstop,mainActual,actualKernel,
      transitionWeight,Guided.pure]
    split_ifs <;> norm_num
  | some s =>
    by_cases hs : C.Correct hD mainKappa s
    · by_cases ht : C.Terminal mainKappa Δ s
      · have hstop : C.stop hD Δ (some s) := ⟨hs,ht⟩
        have hg : ¬(C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s)) := fun h => h.2 hstop
        simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,dite_eq_left hs,dite_eq_left ht,
          stoppedActual,Guided.stoppedKernel,ite_eq_left hstop,Guided.pure,le_refl]
      · have hstop : ¬C.stop hD Δ (some s) := fun h => ht h.2
        have hg : C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s) := ⟨hs,hstop⟩
        simp only [guideLoss,ite_eq_left hg,guideKernel,guideAt,dite_eq_left hs,dite_eq_right ht,
          stoppedActual,Guided.stoppedKernel,ite_eq_right hstop]
        exact C.activeGuide_domination hD Δ hΔ hP hm s hs ht a
    · have hstop : ¬C.stop hD Δ (some s) := fun h => hs h.1
      have hg : ¬(C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s)) := fun h => hs h.1
      simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,dite_eq_right hs,
        stoppedActual,Guided.stoppedKernel,ite_eq_right hstop,le_refl]

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r_oai.{u_1}

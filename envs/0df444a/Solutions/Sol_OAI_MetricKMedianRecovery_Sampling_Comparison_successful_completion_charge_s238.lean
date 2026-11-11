-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:34:15.659253+00:00
-- url     : https://prove2.me/submissions/03b6b832-b04d-4e83-9179-1df5371c9ffa

import Mathlib
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_covered_completion_sum_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

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

end MetricKMedianRecovery.NearClients

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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma uncovered_completion_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ)
    (J : Finset V) (o : V) :
    (∑ p ∈ cluster D C.assign o, if p ∈ J then dist p o else reference S Δ s p) ≤
      (37/20:ℝ)*clusterCost D C.assign o+61*(∑ p ∈ C.near o, reference S Δ s p) := by
  classical
  let X := cluster D C.assign o
  let H := reference S Δ s
  have hH : ∀ p, 0 ≤ H p := fun p => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs)
  by_cases hX : X.Nonempty
  · have hn : (0:ℝ) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
    let T := ∑ p ∈ C.near o, H p
    have hT : 0 ≤ T := Finset.sum_nonneg (fun p _ => hH p)
    have htpos : 0 ≤ 60*T/(X.card:ℝ) := div_nonneg (by positivity) hn.le
    have hbound : ∀ p ∈ X, (if p ∈ J then dist p o else H p) ≤
        (37/20:ℝ)*dist p o+(if p ∈ C.near o then H p else 0)+60*T/X.card := by
      intro p hp
      by_cases hpJ : p ∈ J
      · rw [ite_eq_left hpJ]
        have hz : 0 ≤ (if p ∈ C.near o then H p else 0) := by
          split_ifs
          · exact hH p
          · exact le_rfl
        nlinarith [dist_nonneg (x:=p) (y:=o)]
      · rw [ite_eq_right hpJ]
        by_cases hpN : p ∈ C.near o
        · rw [ite_eq_left hpN]
          nlinarith [dist_nonneg (x:=p) (y:=o)]
        · rw [ite_eq_right hpN,add_zero]
          have hfar : (6/5:ℝ)*clusterMean D C.assign o < dist p o := by
            apply lt_of_not_ge
            intro hh
            exact hpN (Finset.mem_filter.mpr ⟨hp,hh⟩)
          exact NearClients.main_far_bound X hX o p (clusterMean D C.assign o) H
            (clusterMean_mul_card D C.assign o).symm (fun q _ => hH q)
            (fun q _ => by simpa only [dist_comm o q] using reference_triangle S Δ s o q)
            (reference_triangle S Δ s p o) hfar
    have hh := Finset.sum_le_sum hbound
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hh
    have hnear : (∑ p ∈ X, if p ∈ C.near o then H p else 0) = T := by
      rw [← Finset.sum_filter]
      have he : X.filter (fun p => p ∈ C.near o) = C.near o := by
        rw [Finset.filter_mem_eq_inter]
        exact Finset.inter_eq_right.mpr (show C.near o ⊆ X from Finset.filter_subset _ _)
      rw [he]
    rw [hnear] at hh
    have he : (X.card:ℝ)*(60*T/X.card) = 60*T := by field_simp
    rw [he] at hh
    change (∑ p ∈ X, if p ∈ J then dist p o else H p) ≤
      (37/20:ℝ)*(∑ p ∈ X, dist p o)+61*T
    linarith
  · have he : cluster D C.assign o = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have ht : 0 ≤ ∑ p ∈ C.near o, reference S Δ s p := Finset.sum_nonneg (fun p _ => hH p)
    simp only [he,Finset.sum_empty,clusterCost,mul_zero,zero_add]
    positivity

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_SuccessfulCompletionCharge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma successful_completion_charge_s238_oai (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (J : Finset V) (I : ℝ) (hI : I ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign) :
    2*I + (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
      (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
        (dist p o+(19/50:ℝ)*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
      (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
        if p ∈ J then dist p o else reference S Δ s p) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  have hA := C.covered_completion_sum_s238 hD (1/1000000) (19/50) (by norm_num) (by norm_num)
    s hs hP hm
  have hB := Finset.sum_le_sum (s := C.bad \ C.covered s) (fun o _ =>
    C.uncovered_completion_sum hD (1/1000000) Δ s hs hΔ J o)
  conv at hB => rhs; rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hpart := C.center_sum_partition s (C.correct_covered_subset hD (1/1000000) s hs)
    (clusterCost D C.assign)
  rw [comparisonCost_eq D O C.assign C.assigned] at hpart
  have hG := C.proxy_cost
  have hg0 : 0 ≤ ∑ o ∈ C.good, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg _ _ o)
  have hb0 : 0 ≤ ∑ o ∈ C.bad \ C.covered s, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg _ _ o)
  change (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ C.near o, reference S Δ s p) ≤ _ at hT
  linarith

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238_oai.{u_1}

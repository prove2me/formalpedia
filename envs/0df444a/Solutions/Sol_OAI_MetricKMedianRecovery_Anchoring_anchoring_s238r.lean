-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:30:33.226698+00:00
-- url     : https://prove2.me/submissions/406c3f84-c155-4e62-b29e-7fe49a1594d4

import Mathlib
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_Anchoring_total_assignment_excess_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_local_combined_cost_bound_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring

lemma geometric_half_sum (v : ℝ) (hv : 0 ≤ v) (J : ℕ) :
    (∑ a ∈ Finset.range J, v*(1/2:ℝ)^a) ≤ 2*v := by
  induction J with
  | zero => simp <;> positivity
  | succ J ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ a ∈ Finset.range J, v*(1/2:ℝ)^(a+1)) =
        (1/2:ℝ)*(∑ a ∈ Finset.range J, v*(1/2:ℝ)^a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_succ]; ring
    rw [he]
    norm_num only [pow_zero,mul_one]
    linarith

lemma geometric_half_tail (x v : ℝ) (hx : 0 ≤ x) (hv : 0 ≤ v) (J : ℕ) :
    (∑ a ∈ Finset.range J, if v*(1/2:ℝ)^a < x then v*(1/2:ℝ)^a else 0) ≤ 2*x := by
  induction J generalizing v with
  | zero => simp <;> positivity
  | succ J ih =>
    by_cases hvx : v < x
    · calc
        _ ≤ ∑ a ∈ Finset.range (J+1), v*(1/2:ℝ)^a := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact le_rfl
          · positivity
        _ ≤ 2*v := geometric_half_sum v hv (J+1)
        _ ≤ 2*x := by linarith
    · rw [Finset.sum_range_succ']
      simp only [pow_zero,mul_one,hvx,ite_false, if_false,add_zero]
      have he (a : ℕ) : v*(1/2:ℝ)^(a+1) = (v/2)*(1/2:ℝ)^a := by
        rw [pow_succ]; ring
      simp_rw [he]
      exact ih (v/2) (by positivity)

variable {I : Type*}

lemma bad_count_pointwise (O : Finset I) (scale V : I → ℝ) (b t : ℝ)
    (hV : ∀ i ∈ O, 0 ≤ V i) :
    t*b*((badCenters O scale V b t).card:ℝ) ≤
      t*b*((shortCenters O scale b).card:ℝ)+(∑ i ∈ O, V i) := by
  have he (P : I → Prop) [DecidablePred P] :
      t*b*((O.filter P).card:ℝ) = ∑ i ∈ O, if P i then t*b else 0 := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [badCenters,shortCenters,he,he,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : scale i < b
  · simp only [hs,true_or,ite_true, if_true]
    linarith [hV i hi]
  · simp only [hs,false_or,ite_false, if_false,zero_add]
    split_ifs with hv
    · exact hv.le
    · exact hV i hi

lemma threshold_total_bound (O : Finset I) (scale V : I → ℝ) (b v ell : ℝ) (J : ℕ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hell : 0 ≤ ell) (hV : ∀ i ∈ O, 0 ≤ V i) :
    (∑ a ∈ Finset.range J, (v*(1/2:ℝ)^a)*b*
      ((badCenters O scale V b (v*(1/2:ℝ)^a)).card+ell)) ≤
      2*v*b*((shortCenters O scale b).card+ell)+2*(∑ i ∈ O, V i) := by
  have hsplit (a : ℕ) :
      (v*(1/2:ℝ)^a)*b*((badCenters O scale V b (v*(1/2:ℝ)^a)).card+ell) ≤
      ((v*b)*(1/2:ℝ)^a)*((shortCenters O scale b).card+ell)+
      ∑ i ∈ O, if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0 := by
    let z := (v*b)*(1/2:ℝ)^a
    have hz : 0 ≤ z := by dsimp [z] <;> positivity
    have he (P : I → Prop) [DecidablePred P] :
        z*((O.filter P).card:ℝ) = ∑ i ∈ O, if P i then z else 0 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]; ring
    have ht : v*(1/2:ℝ)^a*b = z := by dsimp [z] <;> ring
    rw [ht,mul_add,mul_add,add_right_comm,add_le_add_iff_right]
    unfold badCenters shortCenters
    rw [he,he,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [ht]
    change (if scale i < b ∨ z < V i then z else 0) ≤
      (if scale i < b then z else 0)+(if z < V i then z else 0)
    by_cases hs : scale i < b <;> by_cases hv : z < V i <;> simp [hs,hv,hz]
  calc
    _ ≤ ∑ a ∈ Finset.range J, (((v*b)*(1/2:ℝ)^a)*
        ((shortCenters O scale b).card+ell)+
        ∑ i ∈ O, if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0) :=
      Finset.sum_le_sum (fun a _ => hsplit a)
    _ = (∑ a ∈ Finset.range J, (v*b)*(1/2:ℝ)^a)*
        ((shortCenters O scale b).card+ell)+
        ∑ i ∈ O, ∑ a ∈ Finset.range J,
          if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0 := by
      rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_comm]
    _ ≤ (2*(v*b))*((shortCenters O scale b).card+ell)+∑ i ∈ O, 2*V i := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (geometric_half_sum (v*b) (by positivity) J)
          (by positivity)
      · exact Finset.sum_le_sum (fun i hi => geometric_half_tail (V i) (v*b) (hV i hi)
          (by positivity) J)
    _ = _ := by rw [Finset.mul_sum]; ring

lemma threshold_pos {mu : ℝ} (hmu : 0 < mu) (a : ℕ) : 0 < threshold mu a := by
  unfold threshold; positivity
lemma threshold_le {mu : ℝ} (hmu : 0 ≤ mu) (a : ℕ) : threshold mu a ≤ mu/100 := by
  unfold threshold
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
lemma rounds_bound {mu : ℝ} (hmu : 0 < mu) : 40 ≤ (rounds mu:ℝ)*mu := by
  have h := Nat.le_ceil (40/mu)
  exact (div_le_iff₀ hmu).mp h
lemma rounds_pos {mu : ℝ} (hmu : 0 < mu) : 0 < rounds mu := by
  have h := rounds_bound hmu
  by_contra hh
  have hh0 : rounds mu = 0 := by omega
  simp only [hh0,Nat.cast_zero,zero_mul] at h
  norm_num at h

theorem selected_threshold (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 < P) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P) :
    ∃ a ∈ Finset.range (rounds mu),
      threshold mu a*b*((badCenters O scale V b (threshold mu a)).card+ell) ≤ mu*P/2 := by
  have ht := threshold_total_bound O scale V b (mu/100) ell (rounds mu)
    hb.le (by positivity) hell hV
  have htotal : (∑ a ∈ Finset.range (rounds mu), threshold mu a*b*
      ((badCenters O scale V b (threshold mu a)).card+ell)) ≤ (12+mu/5)*P := by
    dsimp only [threshold]
    calc
      _ ≤ 2*(mu/100)*b*((shortCenters O scale b).card+ell)+2*(∑ i ∈ O, V i) := ht
      _ ≤ 2*(mu/100)*(10*P)+2*(6*P) := by
        apply add_le_add
        · nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2*(mu/100) by positivity)]
        · linarith
      _ = _ := by ring
  by_contra h
  push Not at h
  have hlt : (rounds mu:ℝ)*(mu*P/2) <
      ∑ a ∈ Finset.range (rounds mu), threshold mu a*b*
        ((badCenters O scale V b (threshold mu a)).card+ell) := by
    have hn : (Finset.range (rounds mu)).Nonempty := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (rounds_pos hmu))
    have htlt := Finset.sum_lt_sum_of_nonempty hn (fun a ha => h a ha)
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using htlt
  have h40 := rounds_bound hmu
  have hlo : 20*P ≤ (rounds mu:ℝ)*(mu*P/2) := by nlinarith [mul_le_mul_of_nonneg_right h40 hP.le]
  have hup : (12+mu/5)*P ≤ (61/5:ℝ)*P := by nlinarith
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ThresholdTimesPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring

lemma threshold_times_power (mu : ℝ) (a : ℕ) :
    threshold mu a*(2:ℝ)^a = mu/100 := by
  rw [threshold,mul_assoc,← mul_pow]
  norm_num

lemma threshold_count_factor {mu : ℝ} (hmu : 0 < mu) {a : ℕ} (ha : a < rounds mu) :
    10*threshold mu a+6 ≤ threshold mu a*countConstant mu := by
  have he : threshold mu a*((600/mu)*(2:ℝ)^a) = 6 := by
    calc
      _ = (threshold mu a*(2:ℝ)^a)*(600/mu) := by ring
      _ = _ := by rw [threshold_times_power]; field_simp [ne_of_gt hmu] <;> ring
  have hpow : (2:ℝ)^a ≤ (2:ℝ)^(rounds mu-1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ threshold mu a*(600/mu) from mul_nonneg (threshold_pos hmu a).le (by positivity))
  unfold countConstant
  nlinarith

variable {I : Type*}

lemma selected_count_bound (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 ≤ P) (hmu : 0 < mu) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P)
    (a : ℕ) (ha : a < rounds mu) :
    ((badCenters O scale V b (threshold mu a)).card:ℝ) ≤ countConstant mu*P/b := by
  have ht := threshold_pos hmu a
  have hc := bad_count_pointwise O scale V b (threshold mu a) hV
  have hq : b*(shortCenters O scale b).card ≤ 10*P := by nlinarith
  have hfac := threshold_count_factor hmu ha
  have hm : threshold mu a*b*(badCenters O scale V b (threshold mu a)).card ≤
      threshold mu a*(countConstant mu*P) := by
    nlinarith [mul_le_mul_of_nonneg_left hq ht.le,mul_le_mul_of_nonneg_right hfac hP]
  apply (le_div_iff₀ hb).mpr
  have hm' : threshold mu a*(b*(badCenters O scale V b (threshold mu a)).card) ≤
      threshold mu a*(countConstant mu*P) := by nlinarith [hm]
  have hh := (mul_le_mul_iff_right₀ ht).mp hm'
  nlinarith

theorem threshold_with_count (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 < P) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P) :
    ∃ a ∈ Finset.range (rounds mu),
      0 < threshold mu a ∧ threshold mu a ≤ mu/100 ∧
      threshold mu a*b*((badCenters O scale V b (threshold mu a)).card+ell) ≤ mu*P/2 ∧
      ((badCenters O scale V b (threshold mu a)).card:ℝ) ≤ countConstant mu*P/b := by
  obtain ⟨a,ha,ha'⟩ := selected_threshold O scale V b P mu ell hb hP hmu hmu1 hell hV hsum hscale
  exact ⟨a,ha,threshold_pos hmu a,threshold_le hmu.le a,ha',
    selected_count_bound O scale V b P mu ell hb hP.le hmu hell hV hsum hscale a
      (Finset.mem_range.mp ha)⟩

end MetricKMedianRecovery.Anchoring

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma separation_le {O : Finset V} {i j : V} (hj : j ∈ O) (hji : j ≠ i) :
    separation O i ≤ dist i j := connection_le (Finset.mem_erase.mpr ⟨hji,hj⟩)

lemma separation_pos (O : Finset V) (hO : 2 ≤ O.card) (i : V) : 0 < separation O i := by
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp hO
  have hne : (O.erase i).Nonempty := by
    by_cases hji : j = i
    · exact ⟨k,Finset.mem_erase.mpr ⟨by intro hki; exact hjk (hji.trans hki.symm),hk⟩⟩
    · exact ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩⟩
  rw [separation,← nearest_distance (O.erase i) hne i]
  exact dist_pos.mpr (Ne.symm (Finset.mem_erase.mp (nearest_mem (O.erase i) hne i)).1)

lemma clusterWeight_nonneg (D S : Finset V) (assign : V → V) (i : V) :
    0 ≤ clusterWeight D S assign i :=
  Finset.sum_nonneg (fun p _ => add_nonneg (connection_nonneg S p) dist_nonneg)

lemma nearest_cluster_radius (D S : Finset V) (hS : S.Nonempty) (assign : V → V) (i : V) :
    ((cluster D assign i).card:ℝ)*dist i (nearest S hS i) ≤ clusterWeight D S assign i := by
  have hp (p : V) : dist i (nearest S hS i) ≤ (connection S p + dist p i) := by
    rw [nearest_distance]
    calc
      connection S i ≤ dist i (nearest S hS p) := connection_le (nearest_mem S hS p)
      _ ≤ dist i p+dist p (nearest S hS p) := dist_triangle _ _ _
      _ = _ := by rw [nearest_distance,dist_comm i p]; ring
  simpa only [clusterWeight,Finset.sum_const,nsmul_eq_mul] using
    (Finset.sum_le_sum (s := cluster D assign i) (fun p _ => hp p))

lemma good_radius_bound (D O S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (i : V) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (hscale : b ≤ ((cluster D assign i).card:ℝ)*separation O i)
    (hweight : clusterWeight D S assign i ≤ t*b) :
    0 < (cluster D assign i).card ∧ dist i (nearest S hS i) ≤ t*separation O i := by
  have hn : 0 < (cluster D assign i).card := by
    by_contra h
    have hz : (cluster D assign i).card = 0 := by omega
    simp only [hz,Nat.cast_zero,zero_mul] at hscale
    linarith
  have hnr : (0:ℝ) < (cluster D assign i).card := by exact_mod_cast hn
  refine ⟨hn,?_⟩
  have hh := nearest_cluster_radius D S hS assign i
  have hh2 := mul_le_mul_of_nonneg_left hscale ht
  nlinarith

lemma ballFacilities_disjoint (O S : Finset V) {i j : V} (hi : i ∈ O) (hj : j ∈ O)
    (hij : i ≠ j) : Disjoint (ballFacilities O S i) (ballFacilities O S j) := by
  apply Finset.disjoint_left.mpr
  intro s his hjs
  have his' := (Finset.mem_filter.mp his).2
  have hjs' := (Finset.mem_filter.mp hjs).2
  have hsi := separation_le hj (Ne.symm hij)
  have hsj := separation_le hi hij
  have htri := dist_triangle i s j
  rw [dist_comm s j] at htri
  rw [dist_comm j i] at hsj
  linarith [dist_nonneg (x := i) (y := j)]

lemma proxy_in_ball (O S : Finset V) (hO : 2 ≤ O.card) (hS : S.Nonempty)
    (i : V) (t : ℝ) (ht : t ≤ 1/100)
    (hr : dist i (nearest S hS i) ≤ t*separation O i) :
    nearest S hS i ∈ ballFacilities O S i := by
  refine Finset.mem_filter.mpr ⟨nearest_mem S hS i,?_⟩
  have hp := separation_pos O hO i
  nlinarith

lemma proxies_injective (O S G : Finset V) (hGO : G ⊆ O) (hS : S.Nonempty)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    Set.InjOn (nearest S hS) G := by
  intro i hi j hj he
  by_contra hij
  exact Finset.disjoint_left.mp (ballFacilities_disjoint O S (hGO hi) (hGO hj) hij)
    (hball i hi) (he ▸ hball j hj)

omit [MetricSpace V] in

lemma crowded_card_bound {I : Type*} [DecidableEq I] (G : Finset I) (S : Finset V)
    (boxes : I → Finset V) (hsub : ∀ i ∈ G, boxes i ⊆ S)
    (hne : ∀ i ∈ G, (boxes i).Nonempty) (hd : (G : Set I).PairwiseDisjoint boxes) :
    G.card+(G.filter (fun i => 2 ≤ (boxes i).card)).card ≤ S.card := by
  have hsum : G.card+(G.filter (fun i => 2 ≤ (boxes i).card)).card ≤
      ∑ i ∈ G, (boxes i).card := by
    have he : (G.filter (fun i => 2 ≤ (boxes i).card)).card =
        ∑ i ∈ G, if 2 ≤ (boxes i).card then 1 else 0 := by
      rw [← Finset.sum_filter]; simp
    rw [he,Finset.card_eq_sum_ones,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hc := Finset.card_pos.mpr (hne i hi)
    split_ifs <;> omega
  calc
    _ ≤ ∑ i ∈ G, (boxes i).card := hsum
    _ = (G.biUnion boxes).card := (Finset.card_biUnion hd).symm
    _ ≤ S.card := Finset.card_le_card (by
      intro s hs
      obtain ⟨i,hi,hs⟩ := Finset.mem_biUnion.mp hs
      exact hsub i hi hs)

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IncomingSwapBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma cluster_weight_identity (D S : Finset V) (assign : V → V) (i : V) :
    clusterWeight D S assign i =
      ∑ p ∈ cluster D assign i, (connection S p+dist p (assign p)) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

lemma all_cluster_weights (D O S : Finset V) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) :
    (∑ i ∈ O, clusterWeight D S assign i) =
      ∑ p ∈ D, (connection S p+dist p (assign p)) := by
  simp_rw [cluster_weight_identity,cluster]
  exact Finset.sum_fiberwise_of_maps_to hassign _

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TotalAssignmentExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem anchoring_s238r_oai (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hSF : S ⊆ F) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) (hlocal : WidthLocalMin F D S 5)
    (b mu : ℝ) (hb : 0 < b) (hP : 0 < cost D O) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hscale : b*((S.card:ℝ)-O.card+
      (shortCenters O (clusterScale D O (nearest O hO)) b).card) ≤ 10*cost D O) :
    ∃ G B : Finset V,
      G ∪ B = O ∧ Disjoint G B ∧
      Set.InjOn (nearest S hS) G ∧
      (∀ i ∈ G, nearest S hS i ∈ S) ∧
      (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p (nearest S hS i)) ≤
        (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p i)+mu*cost D O ∧
      (B.card:ℝ) ≤ countConstant mu*cost D O/b := by
  classical
  let assign := nearest O hO
  let w := clusterWeight D S assign
  let sc := clusterScale D O assign
  let ell : ℝ := S.card-O.card
  have hell : 0 ≤ ell := sub_nonneg.mpr (by exact_mod_cast hcard)
  have hass : ∀ p ∈ D, assign p ∈ O := fun p _ => nearest_mem O hO p
  have hsum : (∑ i ∈ O, w i) ≤ 6*cost D O := by
    rw [all_cluster_weights D O S assign hass]
    simpa only [assign,nearest_distance] using
      local_combined_cost_bound_s238r F D S O hS hO hSF hlocal hOF hcard
  obtain ⟨a,ha,ht,htmu,htcost,hcount⟩ := threshold_with_count O sc w b (cost D O) mu ell
    hb hP hmu hmu1 hell (fun i _ => clusterWeight_nonneg D S assign i) hsum hscale
  let t := threshold mu a
  let B := badCenters O sc w b t
  let G := O \ B
  have hBO : B ⊆ O := Finset.filter_subset _ _
  have hGO : G ⊆ O := Finset.sdiff_subset
  have hpart : G ∪ B = O := Finset.sdiff_union_of_subset hBO
  have hdis : Disjoint G B := Finset.sdiff_disjoint
  have ht01 : t ≤ 1/100 := le_trans htmu (by linarith)
  have ht1 : t < 1 := lt_of_le_of_lt ht01 (by norm_num)
  have hgood (i : V) (hi : i ∈ G) : b ≤ sc i ∧ w i ≤ t*b := by
    have hmem := Finset.mem_sdiff.mp hi
    have hn : ¬ (sc i < b ∨ t*b < w i) := by
      intro hh
      exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1,hh⟩)
    push Not at hn
    exact hn
  have hr (i : V) (hi : i ∈ G) : dist i (nearest S hS i) ≤ t*separation O i :=
    (good_radius_bound D O S hS assign i b t hb ht.le (hgood i hi).1 (hgood i hi).2).2
  have hball (i : V) (hi : i ∈ G) : nearest S hS i ∈ ballFacilities O S i :=
    proxy_in_ball O S hO2 hS i t ht01 (hr i hi)
  have hinj := proxies_injective O S G hGO hS hball
  have hcrowd := crowded_card_bound G S (ballFacilities O S)
    (fun _ _ => Finset.filter_subset _ _) (fun i hi => ⟨_,hball i hi⟩)
    (fun i hi j hj hij => ballFacilities_disjoint O S (hGO hi) (hGO hj) hij)
  have hparts : G.card+B.card = O.card := by
    rw [← Finset.card_union_of_disjoint hdis,hpart]
  have hcrowdr : ((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) ≤
      B.card+ell := by
    have hc : (G.card:ℝ)+(G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card ≤ S.card :=
      by exact_mod_cast hcrowd
    have hp : (G.card:ℝ)+B.card = O.card := by exact_mod_cast hparts
    dsimp [ell]
    linarith
  have htotal := total_assignment_excess_s238r F D O S G hS hSF hOF hGO hlocal assign hass b t
    ht.le ht1 (fun i hi => (hgood i hi).2) hr hball
  have hsumw : (∑ p ∈ D, (connection S p+dist p (assign p))) ≤ 6*cost D O := by
    rw [← all_cluster_weights D O S assign hass]
    exact hsum
  have hct : 0 ≤ 4*t+t/(1-t) := by positivity
  have hfirst : t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) ≤
      mu*cost D O/2 := by
    exact (mul_le_mul_of_nonneg_left hcrowdr (mul_nonneg ht.le hb.le)).trans htcost
  have hfrac : t/(1-t) ≤ 2*t := by
    apply (div_le_iff₀ (by linarith : 0 < 1-t)).mpr
    nlinarith
  have hcoef : (4*t+t/(1-t))*(6*cost D O) ≤ mu*cost D O/2 := by
    have h36 : 36*t ≤ mu/2 := by dsimp [t] at * <;> linarith
    have hmul := mul_le_mul_of_nonneg_right h36 hP.le
    nlinarith [mul_le_mul_of_nonneg_right hfrac hP.le]
  have hsecond := (mul_le_mul_of_nonneg_left hsumw hct).trans hcoef
  refine ⟨G,B,hpart,hdis,hinj,(fun i _ => nearest_mem S hS i),?_,hcount⟩
  have he : (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) =
      (∑ i ∈ G, ∑ p ∈ cluster D assign i, dist p (nearest S hS i))-
        (∑ i ∈ G, ∑ p ∈ cluster D assign i, dist p i) := by
    simp only [Finset.sum_sub_distrib]
  rw [he] at htotal
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r_oai.{u_1}

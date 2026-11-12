-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:46.201194+00:00
-- url     : https://prove2.me/submissions/dc0a2247-50f4-4425-a126-e1b78fd559c4

import Mathlib
import Definitions.Def_Q238L010

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma connection_mono {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) (p : V) :
    connection T p ≤ connection S p := by
  simp only [connection,dite_eq_left hS,dite_eq_left (hS.mono hST)]
  exact Finset.le_inf' hS _ (fun _ hs => Finset.inf'_le _ (hST hs))
lemma cost_mono (D : Finset V) {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) :
    cost D T ≤ cost D S := Finset.sum_le_sum (fun p _ => connection_mono hS hST p)

variable [DecidableEq V]

lemma padded_not_worse (F D S T : Finset V) (hSF : S ⊆ F) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hts : T.card ≤ S.card) :
    ∃ U ⊆ F, U.card = S.card ∧ T ⊆ U ∧ S \ U ⊆ S \ T ∧ U \ S ⊆ T \ S ∧
      cost D U ≤ cost D T := by
  obtain ⟨U,hTU,hU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : T ⊆ T ∪ S) hts
    (Finset.card_le_card (Finset.subset_union_right : S ⊆ T ∪ S))
  refine ⟨U,hU.trans (Finset.union_subset hTF hSF),hcard,hTU,?_,?_,cost_mono D hT hTU⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun hxt => (Finset.mem_sdiff.mp hx).2 (hTU hxt)⟩
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp (hU hxu) with hxt | hxs'
    · exact Finset.mem_sdiff.mpr ⟨hxt,hxs⟩
    · exact (hxs hxs').elim

lemma local_min_le_smaller (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (T : Finset V) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hcard : T.card ≤ S.card)
    (hremove : (S \ T).card ≤ w) (hadd : (T \ S).card ≤ w) : cost D S ≤ cost D T := by
  obtain ⟨U,hUF,hUS,_,hrem,hnew,hcost⟩ := padded_not_worse F D S T hSF hTF hT hcard
  exact (hlocal U hUF hUS ((Finset.card_le_card hrem).trans hremove)
    ((Finset.card_le_card hnew).trans hadd)).trans hcost

omit [PseudoMetricSpace V] in
lemma exchange_card_le (S R A : Finset V) (hRS : R ⊆ S) (hAR : A.card ≤ R.card) :
    ((S \ R) ∪ A).card ≤ S.card := by
  have hh := Finset.card_sdiff_add_card_eq_card hRS
  exact (Finset.card_union_le _ _).trans (by omega)
omit [PseudoMetricSpace V] in
lemma exchange_diff_bounds (S R A : Finset V) :
    S \ ((S \ R) ∪ A) ⊆ R ∧ ((S \ R) ∪ A) \ S ⊆ A := by
  constructor
  · intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hn⟩))
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp hxu with hx | hx
    · exact (hxs (Finset.mem_sdiff.mp hx).1).elim
    · exact hx
lemma local_exchange (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (R A : Finset V)
    (hRS : R ⊆ S) (hAF : A ⊆ F) (hA : A.Nonempty)
    (hcard : A.card ≤ R.card) (hR : R.card ≤ w) (ha : A.card ≤ w) :
    cost D S ≤ cost D ((S \ R) ∪ A) := by
  have hd := exchange_diff_bounds S R A
  exact local_min_le_smaller F D S w hSF hlocal _
    (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF)
    (hA.mono Finset.subset_union_right) (exchange_card_le S R A hRS hcard)
    ((Finset.card_le_card hd.1).trans hR) ((Finset.card_le_card hd.2).trans ha)

end MetricKMedianRecovery.LocalSearch

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
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma separation_le {O : Finset V} {i j : V} (hj : j ∈ O) (hji : j ≠ i) :
    separation O i ≤ dist i j := connection_le (Finset.mem_erase.mpr ⟨hji,hj⟩)

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

lemma proxies_injective (O S G : Finset V) (hGO : G ⊆ O) (hS : S.Nonempty)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    Set.InjOn (nearest S hS) G := by
  intro i hi j hj he
  by_contra hij
  exact Finset.disjoint_left.mp (ballFacilities_disjoint O S (hGO hi) (hGO hj) hij)
    (hball i hi) (he ▸ hball j hj)

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

lemma incoming_swap_bound (F D S : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V) (i proxy : V)
    (hi : i ∈ F) (hproxy : proxy ∈ S) :
    (∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
      (connection S p - dist p i)) ≤
      dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) := by
  classical
  let T := (S \ {proxy}) ∪ {i}
  have hc : cost D S ≤ cost D T := local_exchange F D S 5 hSF hlocal {proxy} {i}
    (by simpa) (by simpa) (Finset.singleton_nonempty i) (by simp) (by simp) (by simp)
  have hpoint (p : V) : connection T p-connection S p ≤
      (if nearest S hS p = proxy then
        (if assign p = i then dist p i-connection S p else dist i proxy) else 0) := by
    by_cases hp : nearest S hS p = proxy
    · simp only [hp,ite_true, if_true]
      have hn : connection T p ≤ dist p i :=
        connection_le (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      by_cases ha : assign p = i
      · simpa only [ha,ite_true, if_true] using sub_le_sub_right hn (connection S p)
      · simp only [ha,ite_false, if_false]
        have hd : dist p proxy = connection S p := hp ▸ nearest_distance S hS p
        have htri := dist_triangle p proxy i
        rw [hd,dist_comm proxy i] at htri
        linarith
    · simp only [hp,ite_false, if_false]
      have hn : connection T p ≤ dist p (nearest S hS p) := connection_le
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,by simpa⟩))
      rw [nearest_distance] at hn
      linarith
  have hsum : 0 ≤ ∑ p ∈ D, (if nearest S hS p = proxy then
      (if assign p = i then dist p i-connection S p else dist i proxy) else 0) := by
    have hle := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
    rw [Finset.sum_sub_distrib] at hle
    change cost D T-cost D S ≤ _ at hle
    linarith
  have he : (∑ p ∈ D, if nearest S hS p = proxy then
      (if assign p = i then dist p i-connection S p else dist i proxy) else 0) =
      -(∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
        (connection S p - dist p i))+
      dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) := by
    have hconst : dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) =
        ∑ _p ∈ D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy), dist i proxy := by
      simp [mul_comm]
    rw [hconst,← Finset.sum_neg_distrib]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : nearest S hS p = proxy <;> by_cases ha : assign p = i <;>
      simp [hp,ha]
  rw [he] at hsum
  linarith

lemma cluster_excess_bound (D S : Finset V) (hS : S.Nonempty) (assign : V → V) (i : V) :
    (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      ((cluster D assign i).card:ℝ)*dist i (nearest S hS i) := by
  have hh := Finset.sum_le_sum (s := cluster D assign i) (fun p _ =>
    (show dist p (nearest S hS i)-dist p i ≤ dist i (nearest S hS i) by
      linarith [dist_triangle p i (nearest S hS i)]))
  simpa using hh

lemma singleton_ball_client_bound (O S : Finset V) (hS : S.Nonempty) (i p : V) (t : ℝ)
    (ht : 0 ≤ t) (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i)
    (hp : nearest S hS p ≠ nearest S hS i) :
    dist p (nearest S hS i)-dist p i ≤ 4*t*(dist p i+connection S p) := by
  have hout : nearest S hS p ∉ ballFacilities O S i := fun hm => hp (hbox _ hm)
  have hd : separation O i/4 ≤ dist i (nearest S hS p) := by
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨nearest_mem S hS p,lt_of_not_ge h⟩)
  have htri := dist_triangle i p (nearest S hS p)
  rw [dist_comm i p,nearest_distance] at htri
  have he := dist_triangle p i (nearest S hS i)
  nlinarith [mul_le_mul_of_nonneg_left (hd.trans htri) (show 0 ≤ 4*t by positivity)]

lemma incoming_charge_bound (O S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (i p : V) (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hassign : assign p ∈ O) (hpi : assign p ≠ i)
    (hp : nearest S hS p = nearest S hS i) :
    dist i (nearest S hS i) ≤ (t/(1-t))*(dist p (assign p)+connection S p) := by
  have hsep := separation_le hassign hpi
  have htri1 := dist_triangle i (nearest S hS i) (assign p)
  have htri2 := dist_triangle (nearest S hS i) p (assign p)
  have he : dist (nearest S hS i) p = connection S p := by
    rw [← hp,dist_comm,nearest_distance]
  rw [he] at htri2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-t)).mpr
  nlinarith

end MetricKMedianRecovery.Anchoring

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

omit [MetricSpace V] in
lemma disjoint_family_sum_le {I : Type*} [DecidableEq I] (G : Finset I) (D : Finset V)
    (boxes : I → Finset V) (f : V → ℝ) (hsub : ∀ i ∈ G, boxes i ⊆ D)
    (hd : (G : Set I).PairwiseDisjoint boxes) (hf : ∀ p ∈ D, 0 ≤ f p) :
    (∑ i ∈ G, ∑ p ∈ boxes i, f p) ≤ ∑ p ∈ D, f p := by
  rw [← Finset.sum_biUnion hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi hp
  · intro p hp _; exact hf p hp

lemma singleton_cluster_charge (F D O S : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) (i : V) (hi : i ∈ F) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i) :
    (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      4*t*clusterWeight D S assign i +
      (t/(1-t))*(∑ p ∈ D.filter (fun p => assign p ≠ i ∧
        nearest S hS p = nearest S hS i), (connection S p+dist p (assign p))) := by
  classical
  let proxy := nearest S hS i
  have hextra (p : V) : 0 ≤ 4*t*(connection S p+dist p i) :=
    mul_nonneg (by positivity) (add_nonneg (connection_nonneg _ _) dist_nonneg)
  have hpoint (p : V) : dist p proxy-dist p i ≤
      (if nearest S hS p = proxy then dist p proxy-dist p i else 0)+
        4*t*(connection S p+dist p i) := by
    by_cases hp : nearest S hS p = proxy
    · simp only [hp,ite_true, if_true]
      linarith [hextra p]
    · simp only [hp,ite_false, if_false,zero_add]
      have h := singleton_ball_client_bound O S hS i p t ht hr hbox hp
      linarith
  have hpoints := Finset.sum_le_sum (s := cluster D assign i) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hpoints
  change (∑ p ∈ cluster D assign i, (dist p proxy-dist p i)) ≤
    (∑ p ∈ cluster D assign i, if nearest S hS p = proxy then dist p proxy-dist p i else 0)+
      4*t*clusterWeight D S assign i at hpoints
  have he : (∑ p ∈ cluster D assign i, if nearest S hS p = proxy then
        dist p proxy-dist p i else 0) =
      ∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
        (connection S p-dist p i) := by
    simp only [cluster,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases ha : assign p = i <;> by_cases hp : nearest S hS p = proxy <;>
      simp only [ha,hp,ite_true, if_true,ite_false, if_false,true_and,false_and]
    rw [← hp,nearest_distance]
  rw [he] at hpoints
  have hswap := incoming_swap_bound F D S hS hSF hlocal assign i proxy hi (nearest_mem S hS i)
  have hcharges : dist i proxy*((D.filter (fun p => assign p ≠ i ∧
        nearest S hS p = proxy)).card:ℝ) ≤
      (t/(1-t))*(∑ p ∈ D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy),
        (connection S p+dist p (assign p))) := by
    have q := Finset.sum_le_sum (s := D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy))
      (fun p hp => incoming_charge_bound O S hS assign i p t ht ht1 hr
        (hassign p (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2.1
        (Finset.mem_filter.mp hp).2.2)
    simpa only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,add_comm,mul_comm] using q
  linarith

lemma incoming_fibers_disjoint (D G S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (hinj : Set.InjOn (nearest S hS) G) :
    (G : Set V).PairwiseDisjoint (fun i => D.filter (fun p => assign p ≠ i ∧
      nearest S hS p = nearest S hS i)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  exact hij (hinj hi hj ((Finset.mem_filter.mp hpi).2.2.symm.trans
    (Finset.mem_filter.mp hpj).2.2))

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

lemma total_assignment_excess_s238r_oai (F D O S G : Finset V) (hS : S.Nonempty)
    (hSF : S ⊆ F) (hOF : O ⊆ F) (hGO : G ⊆ O)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) (b t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hwt : ∀ i ∈ G, clusterWeight D S assign i ≤ t*b)
    (hr : ∀ i ∈ G, dist i (nearest S hS i) ≤ t*separation O i)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ)+
      (4*t+t/(1-t))*(∑ p ∈ D, (connection S p+dist p (assign p))) := by
  classical
  let cc := t/(1-t)
  let incoming := fun i => D.filter (fun p => assign p ≠ i ∧ nearest S hS p = nearest S hS i)
  let w := fun p => connection S p+dist p (assign p)
  have hcc : 0 ≤ cc := div_nonneg ht (by linarith)
  have hw : ∀ p ∈ D, 0 ≤ w p := fun p _ => add_nonneg (connection_nonneg S p) dist_nonneg
  have hinc : (∑ i ∈ G, ∑ p ∈ incoming i, w p) ≤ ∑ p ∈ D, w p :=
    disjoint_family_sum_le G D incoming w (fun _ _ => Finset.filter_subset _ _)
      (incoming_fibers_disjoint D G S hS assign (proxies_injective O S G hGO hS hball)) hw
  have hweights : (∑ i ∈ G, clusterWeight D S assign i) ≤ ∑ p ∈ D, w p := by
    rw [← all_cluster_weights D O S assign hassign]
    exact Finset.sum_le_sum_of_subset_of_nonneg hGO (fun i _ _ => clusterWeight_nonneg D S assign i)
  have hpoint (i : V) (hi : i ∈ G) :
      (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
        (if 2 ≤ (ballFacilities O S i).card then t*b else 0)+
          4*t*clusterWeight D S assign i+cc*(∑ p ∈ incoming i, w p) := by
    by_cases hc : 2 ≤ (ballFacilities O S i).card
    · simp only [hc,ite_true, if_true]
      have hE := (cluster_excess_bound D S hS assign i).trans
        ((nearest_cluster_radius D S hS assign i).trans (hwt i hi))
      have h1 : 0 ≤ 4*t*clusterWeight D S assign i :=
        mul_nonneg (by positivity) (clusterWeight_nonneg D S assign i)
      have h2 : 0 ≤ cc*(∑ p ∈ incoming i, w p) := mul_nonneg hcc
        (Finset.sum_nonneg (fun p hp => hw p (Finset.mem_filter.mp hp).1))
      linarith
    · simp only [hc,ite_false, if_false,zero_add]
      have hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i := by
        intro s hs
        have hcard : (ballFacilities O S i).card ≤ 1 := by omega
        exact Finset.card_le_one.mp hcard s hs _ (hball i hi)
      exact singleton_cluster_charge F D O S hS hSF hlocal assign hassign i
        (hOF (hGO hi)) t ht ht1 (hr i hi) hbox
  have hsum := Finset.sum_le_sum (s := G) hpoint
  have hcount : (∑ i ∈ G, if 2 ≤ (ballFacilities O S i).card then t*b else 0) =
      t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  rw [hcount] at hsum
  have hm1 := mul_le_mul_of_nonneg_left hweights (show 0 ≤ 4*t by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hinc hcc
  change _ ≤ t*b*(G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card+
    (4*t+cc)*(∑ p ∈ D, w p)
  nlinarith

end MetricKMedianRecovery.Anchoring

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238r_oai.{u_1}

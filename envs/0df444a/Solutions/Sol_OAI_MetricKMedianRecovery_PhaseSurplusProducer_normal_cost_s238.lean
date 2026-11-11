-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:15.004416+00:00
-- url     : https://prove2.me/submissions/44785e92-7ea4-4e70-81ec-94e35bea23f1

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015
import Definitions.Def_Q238K016
import Theorems.Thm_OAI_MetricKMedianRecovery_Anchoring_anchoring_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Surplus_protected_partition_cost_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_ExtendBudget
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma extendBudget_at {V : Type*} (D : Finset V) (alpha : D → ℝ) (p : D) :
    extendBudget D alpha p.val = alpha p := by simp only [extendBudget,dite_eq_left p.property]

lemma sum_liftSubset {V : Type*} [DecidableEq V] (D C : Finset V) (hCD : C ⊆ D) (f : V → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j : D => j.val ∈ C), f j.val) = ∑ p ∈ C, f p := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_coe_sort D (fun p => if p ∈ C then f p else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun hp => hp.2,fun hp => ⟨hCD hp,hp⟩⟩

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_ClusterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma cluster_sum (D I : Finset V) (assign : V → V) (f : V → V → ℝ) :
    (∑ i ∈ I, ∑ p ∈ cluster D assign i, f p i) =
      ∑ p ∈ D.filter (fun p => assign p ∈ I), f p (assign p) := by
  classical
  calc
    _ = ∑ i ∈ I, ∑ p ∈ D.filter (fun p => assign p = i), f p (assign p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_eq_sum_filter D I assign _

lemma total_cluster_cost (D O : Finset V) (hO : O.Nonempty) :
    partCost D O (nearest O hO) = cost D O := by
  classical
  unfold partCost clusterCost
  rw [cluster_sum]
  have hf : D.filter (fun p => nearest O hO p ∈ O) = D :=
    Finset.filter_eq_self.mpr (fun p _ => nearest_mem O hO p)
  rw [hf]
  exact Finset.sum_congr rfl (fun p _ => nearest_distance O hO p)

lemma partition_cost (D O G B : Finset V) (hO : O.Nonempty)
    (hpart : G ∪ B = O) (hdis : Disjoint G B) :
    partCost D G (nearest O hO)+partCost D B (nearest O hO) = cost D O := by
  classical
  rw [← total_cluster_cost D O hO,partCost,partCost,partCost,← Finset.sum_union hdis,hpart]

omit [DecidableEq V] in
lemma cluster_dual_bound (D C : Finset V) (hCD : C ⊆ D) (alpha : V → ℝ) (lam : ℝ)
    (i : V) (hdual : (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam) :
    (∑ p ∈ C, alpha p) ≤ lam+2*(∑ p ∈ C, dist p i) := by
  have hsub : (∑ p ∈ C, max (alpha p-2*dist i p) 0) ≤ lam :=
    (Finset.sum_le_sum_of_subset_of_nonneg hCD (fun _ _ _ => le_max_right _ _)).trans hdual
  have hpoint (p : V) : alpha p ≤ 2*dist p i+max (alpha p-2*dist i p) 0 := by
    rw [dist_comm p i]
    linarith only [le_max_left (alpha p-2*dist i p) 0]
  have hsum := Finset.sum_le_sum (s := C) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  linarith

lemma any_solution_dual (F D H : Finset V) (hHF : H ⊆ F) (hH : H.Nonempty)
    (alpha : V → ℝ) (lam : ℝ)
    (hdual : ∀ i ∈ F, (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam) :
    (∑ p ∈ D, alpha p) ≤ H.card*lam+2*cost D H := by
  classical
  let assign := nearest H hH
  have hsum := Finset.sum_le_sum (s := H) (fun i hi => cluster_dual_bound D
    (cluster D assign i) (Finset.filter_subset _ _) alpha lam i (hdual i (hHF hi)))
  have hleft : (∑ i ∈ H, ∑ p ∈ cluster D assign i, alpha p) = ∑ p ∈ D, alpha p :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => nearest_mem H hH p) alpha
  rw [hleft,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hsum
  have he := total_cluster_cost D H hH
  change (∑ i ∈ H, ∑ p ∈ cluster D assign i, dist p i) = cost D H at he
  rwa [he] at hsum

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Chosen
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ShortSelection

lemma product_event {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (p : I → X → ℝ) (E : I → X → Prop) [∀ i, DecidablePred (E i)] :
    (∑ f : I → X, if ∀ i, E i (f i) then ∏ i, p i (f i) else 0) =
      ∏ i, ∑ x, if E i x then p i x else 0 := by
  classical
  have hh := Finset.sum_prod_piFinset (ι := I) (Finset.univ : Finset X)
    (fun i x => if E i x then p i x else 0)
  simpa only [Fintype.piFinset_univ, Fintype.prod_ite_zero] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma pair_probability (i j : I) (hij : i ≠ j) :
    (∑ c : I → Bool, if c i = false ∧ c j = true then (1/2:ℝ)^(Fintype.card I) else 0) =
      1/4 := by
  classical
  let E := fun k : I => fun b : Bool => (k=i → b=false) ∧ (k=j → b=true)
  have he (c : I → Bool) : (∀ k, E k (c k)) ↔ c i = false ∧ c j = true := by
    constructor
    · intro h; exact ⟨(h i).1 rfl,(h j).2 rfl⟩
    · rintro ⟨hi,hj⟩ k
      exact ⟨fun h => h ▸ hi,fun h => h ▸ hj⟩
  have hh := product_event (fun (_ : I) (_ : Bool) => (1/2:ℝ)) E
  simp only [Finset.prod_const,Finset.card_univ,he] at hh
  rw [hh]
  have hs (k : I) : (∑ b : Bool, if E k b then (1/2:ℝ) else 0) =
      if k ∈ ({i,j}:Finset I) then 1/2 else 1 := by
    by_cases hki : k=i
    · subst k; simp [E,hij]
    · by_cases hkj : k=j
      · subst k; simp [E,Ne.symm hij]
      · simp [E,hki,hkj]
  simp_rw [hs]
  rw [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter]
  norm_num [hij]

lemma uniform_total : (∑ _c : I → Bool, (1/2:ℝ)^(Fintype.card I)) = 1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

lemma mean_chosen (Q : Finset I) (neighbor : I → I) (hn : ∀ i ∈ Q, i ≠ neighbor i) :
    (∑ c : I → Bool, (chosen Q neighbor c).card*(1/2:ℝ)^(Fintype.card I)) = Q.card/4 := by
  have hc (c : I → Bool) : ((chosen Q neighbor c).card:ℝ) =
      ∑ i ∈ Q, if c i = false ∧ c (neighbor i) = true then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [chosen]
  simp_rw [hc,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi (i : I) (hiQ : i ∈ Q) :
      (∑ c : I → Bool, (if c i = false ∧ c (neighbor i) = true then (1:ℝ) else 0)*
        (1/2:ℝ)^(Fintype.card I)) = 1/4 := by
    simpa only [ite_mul,one_mul,zero_mul] using pair_probability i (neighbor i) (hn i hiQ)
  rw [Finset.sum_congr rfl hi]
  simp [div_eq_mul_inv]

theorem exists_simultaneous (Q : Finset I) (neighbor : I → I)
    (hn : ∀ i ∈ Q, i ≠ neighbor i) :
    ∃ R : Finset I, R ⊆ Q ∧ (Q.card:ℝ)/4 ≤ R.card ∧ ∀ i ∈ R, neighbor i ∉ R := by
  classical
  obtain ⟨c,hc⟩ := Finset.exists_max_image Finset.univ
    (fun c : I → Bool => (chosen Q neighbor c).card) Finset.univ_nonempty
  have hmax := hc.2
  have hbound : (Q.card:ℝ)/4 ≤ (chosen Q neighbor c).card := by
    rw [← mean_chosen Q neighbor hn]
    calc
      _ ≤ ∑ _d : I → Bool, ((chosen Q neighbor c).card:ℝ)*(1/2:ℝ)^(Fintype.card I) :=
        Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right
          (by exact_mod_cast hmax d hd) (by positivity))
      _ = _ := by rw [← Finset.mul_sum,uniform_total,mul_one]
  refine ⟨chosen Q neighbor c,Finset.filter_subset _ _,hbound,?_⟩
  intro i hi hni
  have hi' := (Finset.mem_filter.mp hi).2.2
  have hn' := (Finset.mem_filter.mp hni).2.1
  exact Bool.noConfusion (hi'.symm.trans hn')

end MetricKMedianRecovery.ShortSelection

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma neighbor_mem (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ∈ O :=
  Finset.mem_of_mem_erase (nearest_mem _ _ _)
lemma neighbor_ne (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ≠ i :=
  (Finset.mem_erase.mp (nearest_mem _ _ _)).1
lemma neighbor_dist (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) :
    dist i (neighbor O hO2 i) = separation O i := nearest_distance _ _ _

omit [MetricSpace V] in
lemma remaining_nonempty (O R : Finset V) (hO : O.Nonempty) (nu : V → V)
    (hnu : ∀ i ∈ O, nu i ∈ O) (hret : ∀ i ∈ R, nu i ∉ R) : (O \ R).Nonempty := by
  obtain ⟨i,hi⟩ := hO
  by_cases hiR : i ∈ R
  · exact ⟨nu i,Finset.mem_sdiff.mpr ⟨hnu i hi,hret i hiR⟩⟩
  · exact ⟨i,Finset.mem_sdiff.mpr ⟨hi,hiR⟩⟩

lemma removal_routing_bound (D O R : Finset V) (hO : O.Nonempty) (hO2 : 2 ≤ O.card)
    (hRO : R ⊆ O) (hret : ∀ i ∈ R, neighbor O hO2 i ∉ R) :
    cost D (O \ R) ≤ cost D O+
      ∑ i ∈ R, ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  let assign := nearest O hO
  let extra := fun p => if assign p ∈ R then separation O (assign p) else 0
  have hpoint (p : V) : connection (O \ R) p ≤ connection O p+extra p := by
    by_cases hi : assign p ∈ R
    · have hm : neighbor O hO2 (assign p) ∈ O \ R :=
        Finset.mem_sdiff.mpr ⟨neighbor_mem O hO2 _,hret _ hi⟩
      calc
        _ ≤ dist p (neighbor O hO2 (assign p)) := connection_le hm
        _ ≤ dist p (assign p)+dist (assign p) (neighbor O hO2 (assign p)) := dist_triangle _ _ _
        _ = _ := by simp only [assign,nearest_distance,neighbor_dist,extra,hi,ite_true, if_true]
    · calc
        _ ≤ dist p (assign p) := connection_le (Finset.mem_sdiff.mpr ⟨nearest_mem O hO p,hi⟩)
        _ = _ := by simp only [assign,nearest_distance,extra,hi,ite_false, if_false,add_zero]
  have he : (∑ p ∈ D, extra p) = ∑ i ∈ R, ((cluster D assign i).card:ℝ)*separation O i := by
    have hf := Finset.sum_fiberwise_of_maps_to
      (fun p (_ : p ∈ D) => nearest_mem O hO p) extra
    change (∑ i ∈ O, ∑ p ∈ cluster D assign i, extra p) = ∑ p ∈ D, extra p at hf
    rw [← hf]
    have hinner (i : V) : (∑ p ∈ cluster D assign i, extra p) =
        if i ∈ R then (cluster D assign i).card*separation O i else 0 := by
      have hx (p : V) (hp : p ∈ cluster D assign i) : extra p =
          if i ∈ R then separation O i else 0 := by
        simp only [extra,(Finset.mem_filter.mp hp).2]
      rw [Finset.sum_congr rfl hx]
      split_ifs <;> simp
    simp_rw [hinner]
    rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hRO]
  have hh := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,he] at hh
  exact hh

variable [Fintype V]

theorem short_removal (D O : Finset V) (hO : O.Nonempty) (hO2 : 2 ≤ O.card) (b : ℝ) :
    ∃ R : Finset V,
      R ⊆ O ∧ (O \ R).Nonempty ∧
      ((O.filter (fun i => ((cluster D (nearest O hO) i).card:ℝ)*separation O i < b)).card:ℝ)/4 ≤
        R.card ∧
      cost D (O \ R) ≤ cost D O+b*R.card := by
  classical
  let Q := O.filter (fun i => ((cluster D (nearest O hO) i).card:ℝ)*separation O i < b)
  obtain ⟨R,hRQ,hcard,hret⟩ := ShortSelection.exists_simultaneous Q (neighbor O hO2)
    (fun i _ => Ne.symm (neighbor_ne O hO2 i))
  have hRO : R ⊆ O := hRQ.trans (Finset.filter_subset _ _)
  refine ⟨R,hRO,remaining_nonempty O R hO (neighbor O hO2) (fun i _ => neighbor_mem O hO2 i)
    hret,hcard,?_⟩
  have hh := removal_routing_bound D O R hO hO2 hRO hret
  have hs : (∑ i ∈ R, ((cluster D (nearest O hO) i).card:ℝ)*separation O i) ≤ b*R.card := by
    calc
      _ ≤ ∑ _i ∈ R, b := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp (hRQ hi)).2.le)
      _ = _ := by simp [mul_comm]
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ShortPrice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus

lemma short_price (lam P e n r : ℝ) (hlam : 0 ≤ lam) (hn : n/4 ≤ r)
    (hremove : lam*r ≤ 2*P+2*(lam/8)*r+e) :
    lam*n ≤ (32/3:ℝ)*P+(16/3:ℝ)*e := by
  have h := mul_le_mul_of_nonneg_left hn hlam
  nlinarith only [h,hremove]

lemma anchoring_scale (lam P e L n xi v : ℝ)
    (hP : 0 ≤ P) (hxi : xi ≤ 1) (hv : v ≤ 1/12) (he : e ≤ v*P)
    (hprice : L*lam ≤ 2*(1+xi)*P+e)
    (hshort : lam*n ≤ (32/3:ℝ)*P+(16/3:ℝ)*e) :
    (lam/8)*(L+n) ≤ 10*P := by
  have hx := mul_le_mul_of_nonneg_right hxi hP
  have hvP := mul_le_mul_of_nonneg_right hv hP
  nlinarith only [hprice,hshort,hx,hvP,he,hP]

lemma small_bad_cost (S P Pb Pg : ℝ) (hPb : Pb ≤ P/10)
    (hpart : Pg+Pb = P) (hS : S ≤ (6/5:ℝ)*(Pg+P/100)+(17/5:ℝ)*Pb) :
    S ≤ (179/125:ℝ)*P := by
  linarith

lemma small_bad_strict (S P c : ℝ) (hP : 0 ≤ P) (hc : c ≤ 1)
    (hS : S ≤ (179/125:ℝ)*P) : S ≤ (2-c/100)*P := by
  have h := mul_le_mul_of_nonneg_right hc hP
  nlinarith only [h,hP,hS]

lemma bounded_mass {I : Type*} (B : Finset I) (p : I → ℝ) (lam C P : ℝ)
    (hC : 0 < C) (hlam : 0 ≤ lam) (hP : 0 < P) (hPb : P/10 < ∑ i ∈ B, p i)
    (hprice : (B.card:ℝ)*lam ≤ 8*C*P) :
    P/20 < ∑ i ∈ B.filter (fun i => lam ≤ 200*C*p i), p i := by
  classical
  let good := B.filter (fun i => lam ≤ 200*C*p i)
  let bad := B.filter (fun i => ¬lam ≤ 200*C*p i)
  have hsplit : (∑ i ∈ good, p i)+(∑ i ∈ bad, p i) = ∑ i ∈ B, p i :=
    Finset.sum_filter_add_sum_filter_not B _ p
  have hbad : (200*C)*(∑ i ∈ bad, p i) ≤ (B.card:ℝ)*lam := by
    have hcard : bad.card ≤ B.card := Finset.card_filter_le _ _
    calc
      _ = ∑ i ∈ bad, (200*C)*p i := by rw [Finset.mul_sum]
      _ ≤ ∑ _i ∈ bad, lam := Finset.sum_le_sum (fun i hi =>
        (not_le.mp (Finset.mem_filter.mp hi).2).le)
      _ = (bad.card:ℝ)*lam := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlam
  have hh := hbad.trans hprice
  have hmass : (∑ i ∈ bad, p i) ≤ P/25 := by nlinarith only [hh,hC]
  change P/20 < ∑ i ∈ good, p i
  linarith

lemma normal_strict (U P c v e : ℝ) (hP : 0 < P) (hc : 0 < c)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000) (he : e ≤ v*P)
    (hU : (1-3*v)*U ≤ (2-c/40)*P+e) :
    U ≤ (2-c/100)*P := by
  have ht : 0 < 1-3*v := by linarith
  have hvcP := mul_le_mul_of_nonneg_right hvc hP.le
  have hvP : 0 ≤ v*P := mul_nonneg hv.le hP.le
  have hsmall : (2-c/100)*(3*v)*P ≤ 6*v*P := by
    have hcv : 0 ≤ c*(v*P) := mul_nonneg hc.le hvP
    nlinarith only [hcv]
  have htar : (2-c/40)*P+e ≤ (1-3*v)*((2-c/100)*P) := by
    nlinarith only [hsmall,hvcP,he,hP,hc]
  exact (mul_le_mul_iff_right₀ ht).mp (hU.trans htar)

end MetricKMedianRecovery.Surplus

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] in
lemma aggregate_gain (D O B : Finset V) (hO : O.Nonempty) (hBO : B ⊆ O)
    (alpha : V → ℝ) (lam c : ℝ)
    (hrow : ∀ i ∈ O, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+2*clusterCost D (nearest O hO) i)
    (hstrict : ∀ i ∈ B, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+(2-c/2)*clusterCost D (nearest O hO) i) :
    (∑ p ∈ D, alpha p) ≤ O.card*lam+2*cost D O-(c/2)*partCost D B (nearest O hO) := by
  classical
  let assign := nearest O hO
  have hpoint (i : V) (hi : i ∈ O) : (∑ p ∈ cluster D assign i, alpha p) ≤
      lam+2*clusterCost D assign i-(if i ∈ B then (c/2)*clusterCost D assign i else 0) := by
    by_cases hb : i ∈ B
    · rw [ite_eq_left hb]
      linarith only [hstrict i hb]
    · rw [ite_eq_right hb,sub_zero]
      exact hrow i hi
  have hsum := Finset.sum_le_sum (s := O) hpoint
  have hleft : (∑ i ∈ O, ∑ p ∈ cluster D assign i, alpha p) = ∑ p ∈ D, alpha p :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => nearest_mem O hO p) alpha
  have hf : O.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun hi => hi.2,fun hi => ⟨hBO hi,hi⟩⟩
  have hcost : (∑ i ∈ O, clusterCost D assign i) = cost D O := total_cluster_cost D O hO
  rw [hleft,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    nsmul_eq_mul,← Finset.mul_sum,hcost,← Finset.sum_filter,hf,← Finset.mul_sum] at hsum
  exact hsum

theorem low_sensitive_cost (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
    (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    (alpha : V → ℝ) (lam Q e xi v c C : ℝ)
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000) (he : e ≤ v*cost D O)
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 < C) (hCeq : C = countConstant (1/100))
    (hpayment : (1-3*v)*Q+O.card*lam-e ≤ ∑ p ∈ D, alpha p)
    (hdual : ∀ i ∈ F, (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam)
    (hstrict : ∀ i ∈ O, lam ≤ (200*C)*clusterCost D (nearest O hO) i →
      (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i) :
    cost D S ≤ (2-c/100)*cost D O := by
  classical
  let P := cost D O
  let assign := nearest O hO
  let b := lam/8
  have hb : 0 < b := by dsimp [b] <;> positivity
  have ht : 0 ≤ 1-3*v := by linarith
  have hprice (A : Finset V) (hAF : A ⊆ F) (hA : A.Nonempty) :
      ((O.card:ℝ)-A.card)*lam ≤ 2*cost D A+e := by
    have hh := any_solution_dual F D A hAF hA alpha lam hdual
    have hq := mul_nonneg ht hQ
    nlinarith only [hh,hpayment,hq]
  have hsur : (L:ℝ)*lam ≤ 2*(1+xi)*P+e := by
    have hh := hprice H hHF hH
    have heq : (H.card:ℝ)+L = O.card := by exact_mod_cast hHL
    have heqlam : ((O.card:ℝ)-H.card)*lam = L*lam := by rw [← heq]; ring
    rw [heqlam] at hh
    dsimp [P]
    linarith only [hh,hHcost]
  obtain ⟨R,hRO,hrem,hRcard,hRcost⟩ := short_removal D O hO hO2 b
  have hshort : lam*((shortCenters O (clusterScale D O assign) b).card:ℝ) ≤
      (32/3:ℝ)*P+(16/3:ℝ)*e := by
    have hh := hprice (O \ R) (Finset.sdiff_subset.trans hOF) hrem
    have heq : ((O \ R).card:ℝ)+R.card = O.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hRO
    have heqlam : ((O.card:ℝ)-(O \ R).card)*lam = R.card*lam := by rw [← heq]; ring
    rw [heqlam] at hh
    have hr : lam*(R.card:ℝ) ≤ 2*P+2*(lam/8)*R.card+e := by
      dsimp [P,b] at *
      nlinarith only [hh,hRcost]
    apply short_price lam P e _ R.card hlam.le _ hr
    exact hRcard
  have hell : (S.card:ℝ)-O.card = L := by
    have hh : (S.card:ℝ) = O.card+L := by exact_mod_cast hcard
    linarith only [hh]
  have hscale : b*((S.card:ℝ)-O.card+(shortCenters O (clusterScale D O assign) b).card) ≤ 10*P := by
    rw [hell]
    exact anchoring_scale lam P e L _ xi v hP.le hxi hv1 he hsur hshort
  obtain ⟨G,B,hpart,hdis,hinj,hproxy,hcharge,hcount⟩ := anchoring_s238 F D O S hO hS hO2 hSF hOF
    (by omega) hlocal b (1/100) hb hP (by norm_num) (by norm_num) hscale
  have hp : partCost D G assign+partCost D B assign = P := partition_cost D O G B hO hpart hdis
  have hcharge' : partCharge D G assign (nearest S hS) ≤ partCost D G assign+P/100 := by
    change _ ≤ _+ (1/100:ℝ)*P at hcharge
    simpa only [partCharge,partCost,clusterCost,assign,div_eq_mul_inv,mul_comm,one_mul] using hcharge
  have hrow (i : V) (hi : i ∈ O) : (∑ p ∈ cluster D assign i, alpha p) ≤
      lam+2*clusterCost D assign i :=
    cluster_dual_bound D _ (Finset.filter_subset _ _) alpha lam i (hdual i (hOF hi))
  by_cases hbad : partCost D B assign ≤ P/10
  · have hs := protected_partition_cost_s238 F D S O G B hS hO hSF hOF hlocal (by omega) hpart hdis hinj
    have hsub : cost D S ≤ (6/5:ℝ)*(partCost D G assign+P/100)+(17/5:ℝ)*partCost D B assign := by
      change cost D S ≤ (17/5:ℝ)*partCost D B assign+(6/5:ℝ)*partCharge D G assign (nearest S hS) at hs
      linarith
    exact small_bad_strict _ P c hP.le hc1 (small_bad_cost _ P _ _ hbad hp hsub)
  · have hBprice : (B.card:ℝ)*lam ≤ 8*C*P := by
      rw [← hCeq] at hcount
      have hh := (le_div_iff₀ hb).mp hcount
      dsimp [b] at hh
      nlinarith only [hh]
    let BT := B.filter (fun i => lam ≤ 200*C*clusterCost D assign i)
    have hm : P/20 < partCost D BT assign := bounded_mass B (clusterCost D assign) lam C P
      hC hlam.le hP (lt_of_not_ge hbad) hBprice
    have hBO : B ⊆ O := by rw [← hpart]; exact Finset.subset_union_right
    have hBTO : BT ⊆ O := (Finset.filter_subset _ _).trans hBO
    have hgain := aggregate_gain D O BT hO hBTO alpha lam c hrow (fun i hi =>
      hstrict i (hBTO hi) (Finset.mem_filter.mp hi).2)
    have hmass := mul_le_mul_of_nonneg_left hm.le (by positivity : 0 ≤ c/2)
    have hbudget : (∑ p ∈ D, alpha p) ≤ O.card*lam+(2-c/40)*P := by
      change (∑ p ∈ D, alpha p) ≤ O.card*lam+2*P-(c/2)*partCost D BT assign at hgain
      nlinarith only [hgain,hmass]
    have hq : (1-3*v)*Q ≤ (2-c/40)*P+e := by linarith only [hpayment,hbudget]
    exact hSQ.trans (normal_strict Q P c v e hP hc hv hv1 hvc he hq)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGapPos
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_pos {T : ℝ} (hT : 0 < T) : 0 < strictnessGap T := by
  unfold strictnessGap
  positivity
lemma strictnessGap_le_one {T : ℝ} (hT : 0 < T) : strictnessGap T ≤ 1 := by
  have hd : 1 ≤ 200*(T+2) := by linarith
  have ht : 0 < 200*(T+2) := by positivity
  have hq : 1/(200*(T+2)) ≤ (1:ℝ) := (div_le_iff₀ ht).mpr (by nlinarith only [hd])
  have hq0 : 0 ≤ 1/(200*(T+2)) := by positivity
  unfold strictnessGap
  nlinarith

variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] [MetricSpace V] [DecidableEq V] in
lemma sum_extended_budget (D : Finset V) (alpha : D → ℝ) :
    (∑ p ∈ D, extendBudget D alpha p) = ∑ j, alpha j := by
  rw [← Finset.sum_coe_sort D (extendBudget D alpha)]
  exact Finset.sum_congr rfl (fun j _ => extendBudget_at D alpha j)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_IndexedCost
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma dual_on_points (D F : Finset V) {v lam : ℝ} {alpha : D → ℝ}
    (h : Dual (fun j : D => j.val) F v lam alpha) (i : V) (hi : i ∈ F) :
    (∑ p ∈ D, max (extendBudget D alpha p-2*dist i p) 0) ≤ lam := by
  have hh := h.2.1 i hi
  rw [← Finset.sum_coe_sort D (fun p => max (extendBudget D alpha p-2*dist i p) 0)]
  simpa only [extendBudget_at] using hh

lemma strict_on_points (D C F : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    {v lam b : ℝ} {alpha : D → ℝ} (h : Dual (fun j : D => j.val) F v lam alpha)
    (i : V) (hi : i ∈ F) (hb : 0 < b)
    (hP : 0 < ∑ p ∈ C, dist p i) (hprice : lam ≤ b*(∑ p ∈ C, dist p i))
    (hsmall : v^2 ≤ strictnessGap b/(6*(b+2))) :
    (∑ p ∈ C, extendBudget D alpha p) ≤ lam+(2-strictnessGap b/2)*(∑ p ∈ C, dist p i) := by
  classical
  let C' := Finset.univ.filter (fun j : D => j.val ∈ C)
  have hC' : C'.Nonempty := by
    obtain ⟨p,hp⟩ := hC
    exact ⟨⟨p,hCD hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hd : (∑ j ∈ C', dist i j.val) = ∑ p ∈ C, dist p i := by
    simpa only [dist_comm] using sum_liftSubset D C hCD (fun p => dist p i)
  have ha : (∑ j ∈ C', alpha j) = ∑ p ∈ C, extendBudget D alpha p := by
    calc
      _ = ∑ j ∈ C', extendBudget D alpha j.val :=
        Finset.sum_congr rfl (fun j _ => (extendBudget_at D alpha j).symm)
      _ = _ := sum_liftSubset D C hCD _
  have hh := h.2.2 C' hC' i hi b hb (hd ▸ hP) (hd ▸ hprice) hsmall
  simpa only [ha,hd] using hh

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

variable [Fintype V]

lemma normal_cost_s238_oai (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
    (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    (alpha : D → ℝ) (lam Q eta xi v : ℝ) (hdual : Dual (fun j : D => j.val) F v lam alpha)
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (herr : (O.card:ℝ)*D.card*eta ≤ v*cost D O)
    (hpayment : (1-3*v)*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*eta) ≤ ∑ j, alpha j) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) countConstant_ge_ten
  have hT : 0 < 200*C := by positivity
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hpay : (1-3*v)*Q+O.card*lam-(O.card:ℝ)*D.card*eta ≤
      ∑ p ∈ D, extendBudget D alpha p := by
    rw [sum_extended_budget]
    nlinarith only [hpayment]
  have hstrict (i : V) (hi : i ∈ O)
      (hprice : lam ≤ (200*C)*clusterCost D (nearest O hO) i) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    have hP' : 0 < clusterCost D (nearest O hO) i := by
      by_contra hg
      have hle := le_of_not_gt hg
      nlinarith only [hT,hprice,hlam,hle]
    have hne : (cluster D (nearest O hO) i).Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [clusterCost,hz,Finset.sum_empty] at hP'
      exact (lt_irrefl _ hP')
    exact strict_on_points D _ F (Finset.filter_subset _ _) hne hdual i (hOF hi) hT hP' hprice hsmall
  exact low_sensitive_cost F D O S H hO hS hH hOF hSF hHF hO2 L hcard hHL hlocal hP
    (extendBudget D alpha) lam Q ((O.card:ℝ)*D.card*eta) xi v c C hlam hQ hSQ
    hHcost hxi hv hv1 hvc herr hc hc1 hC rfl hpay (dual_on_points D F hdual) hstrict

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238_oai.{u_1}

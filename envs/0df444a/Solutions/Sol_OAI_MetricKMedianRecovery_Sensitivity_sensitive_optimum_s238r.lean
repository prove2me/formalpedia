-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:32:36.546103+00:00
-- url     : https://prove2.me/submissions/15b1d406-96f3-427c-bdf6-c83dba31e449

import Mathlib
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_exact_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sensitivity
lemma power_bound (L : ℕ) (hL : 0 < L) (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    (1+xi/(4*L))^(2*L) < 1+xi := by
  have hLR : (0:ℝ) < L := by exact_mod_cast hL
  have hb : 0 < xi/(4*L) := by positivity
  have hlog := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1+xi/(4*L))
      (by linarith : 1+xi/(4*(L:ℝ)) ≠ 1)
  have hlow := Real.le_log_one_add_of_nonneg hxi.le
  have hfrac : xi/2 ≤ 2*xi/(xi+2) := by
    apply (le_div_iff₀ (by linarith : 0 < xi+2)).mpr
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < (2*L:ℝ))
  have hbeta : (2*L:ℝ)*(xi/(4*L)) = xi/2 := by field_simp <;> ring
  have hc : Real.log ((1+xi/(4*L))^(2*L)) < Real.log (1+xi) := by
    rw [Real.log_pow]
    push_cast
    rw [show 1+xi/(4*(L:ℝ))-1 = xi/(4*L) by ring,hbeta] at hmul
    exact hmul.trans_le (hfrac.trans hlow)
  exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hc

lemma chain_bound_length (P : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (a d : ℕ)
    (hstep : ∀ j, a < j → j ≤ a+d → P (j-1) ≤ q*P j) :
    P a ≤ q^d*P (a+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hi : P a ≤ q^d*P (a+d) := ih (fun j hj hjd => hstep j hj (by omega))
    have hs := hstep (a+d+1) (by omega) (by omega)
    have he : a+d+1-1=a+d := by omega
    rw [he] at hs
    have hs' : P (a+d) ≤ q*P (a+(d+1)) := by simpa only [Nat.add_assoc] using hs
    calc
      _ ≤ q^d*P (a+d) := hi
      _ ≤ q^d*(q*P (a+(d+1))) := mul_le_mul_of_nonneg_left hs' (pow_nonneg hq _)
      _ = _ := by rw [pow_succ]; ring

lemma chain_bound (P : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → P (j-1) ≤ q*P j) :
    P a ≤ q^(b-a)*P b := by
  have he : a+(b-a)=b := Nat.add_sub_of_le hab
  simpa only [he] using chain_bound_length P q hq a (b-a)
    (fun j hj hjb => hstep j hj (by simpa only [he] using hjb))

theorem exists_sensitive (P : ℕ → ℝ) (k L : ℕ) (hL : 0 < L) (hk : 2*L < k)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hPk : 0 ≤ P k)
    (hsens : (1+xi)*P k < P (k-2*L)) :
    ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
      (1+xi/(4*L))*P h ≤ P (h-1) ∧ P h ≤ (1+xi)*P k := by
  classical
  let q := 1+xi/(4*L)
  have hq1 : 1 ≤ q := by
    have hb : 0 ≤ xi/(4*(L:ℝ)) := div_nonneg hxi.le (by positivity)
    dsimp [q] <;> linarith
  have hq : 0 ≤ q := le_trans (by norm_num) hq1
  let A := (Finset.Ioc (k-2*L) k).filter (fun j => q*P j ≤ P (j-1))
  have hA : A.Nonempty := by
    by_contra hn
    have hstep (j : ℕ) (hja : k-2*L < j) (hjk : j ≤ k) : P (j-1) ≤ q*P j := by
      by_contra hh
      apply hn
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hja,hjk⟩,(lt_of_not_ge hh).le⟩⟩
    have hh := chain_bound P q hq (k-2*L) k (by omega) hstep
    have hex : k-(k-2*L)=2*L := by omega
    rw [hex] at hh
    have hp := mul_le_mul_of_nonneg_right (power_bound L hL xi hxi hxi1).le hPk
    exact (not_lt_of_ge (hh.trans hp)) hsens
  let h := A.max' hA
  have hm : h ∈ A := Finset.max'_mem A hA
  have hmem := Finset.mem_filter.mp hm
  have hr := Finset.mem_Ioc.mp hmem.1
  have hstep (j : ℕ) (hhj : h < j) (hjk : j ≤ k) : P (j-1) ≤ q*P j := by
    by_contra hn
    have hjA : j ∈ A := Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨lt_trans hr.1 hhj,hjk⟩,(lt_of_not_ge hn).le⟩
    have hmax : j ≤ h := Finset.le_max' A j hjA
    omega
  have hc := chain_bound P q hq h k hr.2 hstep
  have hex : k-h ≤ 2*L := by omega
  have hpow : q^(k-h) ≤ q^(2*L) := pow_le_pow_right₀ hq1 hex
  have hp : q^(k-h) ≤ 1+xi := hpow.trans (power_bound L hL xi hxi hxi1).le
  exact ⟨h,hr.1,hr.2,hmem.2,hc.trans (mul_le_mul_of_nonneg_right hp hPk)⟩

end MetricKMedianRecovery.Sensitivity

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Chosen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma neighbor_mem (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ∈ O :=
  Finset.mem_of_mem_erase (nearest_mem _ _ _)
lemma neighbor_ne (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) : neighbor O hO2 i ≠ i :=
  (Finset.mem_erase.mp (nearest_mem _ _ _)).1
lemma neighbor_dist (O : Finset V) (hO2 : 2 ≤ O.card) (i : V) :
    dist i (neighbor O hO2 i) = separation O i := nearest_distance _ _ _

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

end MetricKMedianRecovery.Anchoring

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
lemma optimum_nonneg (F D : Finset V) (r : ℕ) : 0 ≤ optimum F D r := by
  unfold optimum
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => cost_nonneg _ _)
  · rfl
lemma optimum_le (F D S : Finset V) (r : ℕ) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hSr : S.card ≤ r) : optimum F D r ≤ cost D S := by
  have hm : S ∈ feasibleSets F r := (mem_feasibleSets F S r).mpr ⟨hSF,hS,hSr⟩
  rw [optimum,dite_eq_left ⟨S,hm⟩]
  exact Finset.inf'_le _ hm

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_OptimumClusterSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sensitivity
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma optimum_cluster_separation (F D O : Finset V) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hO2 : 2 ≤ O.card) (beta : ℝ)
    (hcost : cost D O = optimum F D O.card)
    (hratio : (1+beta)*optimum F D O.card ≤ optimum F D (O.card-1)) :
    ∀ i ∈ O, beta*cost D O ≤ ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  intro i hi
  have hrem : ∀ j ∈ ({i}:Finset V), neighbor O hO2 j ∉ ({i}:Finset V) := by
    intro j hj
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    simpa only [Finset.mem_singleton] using neighbor_ne O hO2 i
  have hr := removal_routing_bound D O {i} hO hO2 (Finset.singleton_subset_iff.mpr hi) hrem
  simp only [Finset.sdiff_singleton_eq_erase,Finset.sum_singleton] at hr
  have hop := optimum_le F D (O.erase i) (O.card-1)
    ((Finset.erase_subset i O).trans hOF) (erase_nonempty_of_two O hO2 i)
    (by rw [Finset.card_erase_of_mem hi])
  rw [← hcost] at hratio
  linarith

theorem sensitive_optimum_s238r_oai (F D : Finset V) (hF : F.Nonempty) (k L : ℕ)
    (hL : 0 < L) (hk : 2*L < k) (hkF : k ≤ F.card)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hsens : (1+xi)*optimum F D k < optimum F D (k-2*L)) :
    ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
      (1+xi/(4*L))*optimum F D h ≤ optimum F D (h-1) ∧
      optimum F D h ≤ (1+xi)*optimum F D k ∧
      ∃ O : Finset V, ∃ hO : O.Nonempty, O ⊆ F ∧ O.card = h ∧
        cost D O = optimum F D h ∧
        ∀ i ∈ O, (xi/(4*L))*cost D O ≤
          ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  obtain ⟨h,hlo,hhi,hratio,hcost⟩ := exists_sensitive (optimum F D) k L hL hk xi hxi hxi1
    (optimum_nonneg F D k) hsens
  obtain ⟨O,hOF,hO,hOh,hopt⟩ := optimum_attained_exact_s238r F D hF h (by omega) (hhi.trans hkF)
  refine ⟨h,hlo,hhi,hratio,hcost,O,hO,hOF,hOh,hopt,?_⟩
  apply optimum_cluster_separation F D O hOF hO (by omega) (xi/(4*L))
  · simpa only [hOh] using hopt
  · simpa only [hOh] using hratio

end MetricKMedianRecovery.Sensitivity

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r_oai.{u_1}

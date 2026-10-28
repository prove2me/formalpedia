-- Prove2me | solution 1 for MinLatency.Approx.corollary_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-27T00:58:56.633668+00:00
-- url     : https://prove2.me/submissions/17529a59-ce9a-45bc-ae5b-c8b91d09d145

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting
namespace Queelius.MinLatency
open MinLatency.Approx
variable {V : Type} [Fintype V] [DecidableEq V]

theorem pcCost_const (d : V → V → ℝ) (P : ℝ) (T : List V) :
    pcCost d (fun _ => P) T = tourLen d T + (missed T : ℝ) * P := by
  simp [pcCost, missed, nsmul_eq_mul]

theorem comparison_cost (d : V → V → ℝ) (p : V) (L : ℝ) (hL : 0 ≤ L)
    (k : ℕ) (hk : 1 ≤ k) (T : List V) (_hT : IsRootedTour p T)
    (hlen : tourLen d T ≤ L) (hmiss : missed T ≤ k) :
    pcCost d (fun _ => 2 * L / k) T ≤ 3 * L := by
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hp : 0 ≤ 2 * L / (k : ℝ) := by positivity
  rw [pcCost_const]
  calc
    tourLen d T + (missed T : ℝ) * (2 * L / k) ≤ L + (k : ℝ) * (2 * L / k) :=
      add_le_add hlen (mul_le_mul_of_nonneg_right (by exact_mod_cast hmiss) hp)
    _ = 3 * L := by field_simp; ring

theorem distance_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (u v : V) : 0 ≤ d u v := by
  by_cases h : u=v
  · subst v
    rw [hd.self]
  · exact (hd.pos u v h).le

theorem pathLen_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (T : List V) : 0 ≤ pathLen d T := by
  induction T with
  | nil => simp [pathLen]
  | cons u T ih =>
    cases T with
    | nil => simp [pathLen]
    | cons v T => exact add_nonneg (distance_nonnegative d hd u v) ih

theorem tourLen_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (T : List V) : 0 ≤ tourLen d T := by
  cases T with
  | nil => simp [tourLen]
  | cons u T => exact add_nonneg (pathLen_nonnegative d hd _) (distance_nonnegative d hd _ _)

theorem oracle_bounds (d : V → V → ℝ) (p : V) (hd : IsMetric d)
    (O : (V → ℝ) → List V) (hO : PCAdmissible d p O)
    (L : ℝ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k)
    (hex : ∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) :
    IsRootedTour p (O (fun _ => 2 * L / k)) ∧
      tourLen d (O (fun _ => 2 * L / k)) ≤ 6 * L ∧
      missed (O (fun _ => 2 * L / k)) ≤ 3 * k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpen : 0 < 2 * L / (k : ℝ) := by positivity
  obtain ⟨T,hT,hlen,hmiss⟩ := hex
  obtain ⟨hroot,hcost⟩ := hO (fun _ => 2 * L / k) (fun _ => hpen.le)
  have hc : pcCost d (fun _ => 2 * L / k) (O (fun _ => 2 * L / k)) ≤ 6 * L :=
    (hcost T hT).trans (by have hh := comparison_cost d p L hL.le k hk T hT hlen hmiss; linarith)
  rw [pcCost_const] at hc
  refine ⟨hroot, ?_, ?_⟩
  · have hm : 0 ≤ (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) := by positivity
    linarith
  · have hnonneg := tourLen_nonnegative d hd (O (fun _ => 2 * L / k))
    have heq : (3 * k : ℝ) * (2 * L / k) = 6 * L := by field_simp; ring
    have hb : (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) ≤
        (3 * k : ℝ) * (2 * L / k) := by rw [heq]; linarith
    have hm := (mul_le_mul_iff_left₀ hpen).mp hb
    exact_mod_cast hm
end Queelius.MinLatency

section
namespace Queelius.MinLatency
open MinLatency.Approx
variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable section

def candidateTours (d : V → V → ℝ) (O : (V → ℝ) → List V) (L : ℝ) : List (List V) :=
  (((List.range (Fintype.card V)).map (fun k => O (fun _ => penalty L k))).filter
    (fun T => decide (tourLen d T ≤ 6*L)))

theorem penalty_nonnegative (L : ℝ) (hL : 0 ≤ L) (k : ℕ) : 0 ≤ penalty L k := by
  unfold penalty
  split_ifs <;> positivity

theorem missed_card (T : List V) : missed T = Fintype.card V - T.toFinset.card := by
  have he : Finset.univ.filter (fun v => v ∉ T) = T.toFinsetᶜ := by ext v; simp
  unfold missed
  rw [he, Finset.card_compl]

theorem candidate_properties (d : V → V → ℝ) (p : V) (O : (V → ℝ) → List V)
    (hO : PCAdmissible d p O) (L : ℝ) (hL : 0 < L) (T : List V)
    (hm : T ∈ candidateTours d O L) : IsRootedTour p T ∧ tourLen d T ≤ 6*L := by
  simp only [candidateTours,List.mem_filter,decide_eq_true_eq,List.mem_map,List.mem_range] at hm
  rcases hm with ⟨⟨k,hk,rfl⟩,hlen⟩
  exact ⟨(hO _ (fun _ => penalty_nonnegative L hL.le k)).1,hlen⟩

theorem scan_properties (d : V → V → ℝ) (p : V) (hd : IsMetric d)
    (O : (V → ℝ) → List V) (hO : PCAdmissible d p O) (L : ℝ) (hL : 0 < L) :
    IsRootedTour p (cor4Approx d p O L) ∧ tourLen d (cor4Approx d p O L) ≤ 6*L ∧
      ∀ T ∈ candidateTours d O L, missed (cor4Approx d p O L) ≤ missed T := by
  classical
  change (IsRootedTour p (match (candidateTours d O L).argmax (fun T => T.toFinset.card) with
    | some T => T | none => [p])) ∧ _
  cases he : (candidateTours d O L).argmax (fun T => T.toFinset.card) with
  | none =>
    have hn := List.argmax_eq_none.mp he
    have hc : cor4Approx d p O L = [p] := by unfold cor4Approx; change (match (candidateTours d O L).argmax _ with | some T => T | none => [p]) = _; rw [he]
    simp only [he]
    refine ⟨by simp [IsRootedTour], ?_, ?_⟩
    · rw [hc]
      simpa [tourLen,pathLen,hd.self] using (show (0:ℝ)≤6*L by positivity)
    · intro T hm
      rw [hn] at hm
      simp at hm
  | some S =>
    have hs : S ∈ (candidateTours d O L).argmax (fun T => T.toFinset.card) := by rw [he]; simp
    have hm := List.argmax_mem hs
    have hp := candidate_properties d p O hO L hL S hm
    have hc : cor4Approx d p O L = S := by unfold cor4Approx; change (match (candidateTours d O L).argmax _ with | some T => T | none => [p]) = _; rw [he]
    simp only [he]
    refine ⟨hp.1, ?_, ?_⟩
    · simpa [hc] using hp.2
    · intro T hT
      rw [hc,missed_card,missed_card]
      exact Nat.sub_le_sub_left (List.le_of_mem_argmax hT hs) _
end
end Queelius.MinLatency

end

section
namespace Queelius.MinLatency
open MinLatency.Approx
variable {V : Type} [Fintype V] [DecidableEq V]

theorem penalized_oracle_bounds (d : V → V → ℝ) (p : V) (hd : IsMetric d)
    (O : (V → ℝ) → List V) (hO : PCAdmissible d p O)
    (L : ℝ) (hL : 0 < L) (k : ℕ)
    (hex : ∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) :
    IsRootedTour p (O (fun _ => penalty L k)) ∧
      tourLen d (O (fun _ => penalty L k)) ≤ 6 * L ∧
      missed (O (fun _ => penalty L k)) ≤ 3 * k := by
  by_cases hk : k=0
  · subst k
    simp only [penalty,ite_true]
    obtain ⟨T,hT,hlen,hmiss⟩ := hex
    have hm0 : missed T = 0 := by omega
    obtain ⟨hroot,hcost⟩ := hO (fun _ => 4*L) (fun _ => by positivity)
    have hc : pcCost d (fun _ => 4*L) (O (fun _ => 4*L)) ≤ 2*L :=
      (hcost T hT).trans (by rw [pcCost_const,hm0]; simp; linarith)
    rw [pcCost_const] at hc
    have hnonneg := tourLen_nonnegative d hd (O (fun _ => 4*L))
    have hmiss0 : missed (O (fun _ => 4*L)) = 0 := by
      by_contra hh
      have hn : (1 : ℝ) ≤ missed (O (fun _ => 4*L)) := by exact_mod_cast (by omega : 1 ≤ missed (O (fun _ => 4*L)))
      nlinarith
    refine ⟨hroot,?_,?_⟩
    · rw [hmiss0] at hc
      simp only [Nat.cast_zero,zero_mul,add_zero] at hc
      linarith
    · simp [hmiss0]
  · simpa [penalty,hk] using oracle_bounds d p hd O hO L hL k (by omega) hex

theorem cor4_approximator (d : V → V → ℝ) (p : V) (hd : IsMetric d)
    (O : (V → ℝ) → List V) (hO : PCAdmissible d p O) :
    IsTSPApprox d p 3 6 (cor4Approx d p O) := by
  intro L hL k hex
  obtain ⟨hr,hlen,hbest⟩ := scan_properties d p hd O hO L hL
  refine ⟨hr,hlen,?_⟩
  by_cases hk : k < Fintype.card V
  · have hb := penalized_oracle_bounds d p hd O hO L hL k hex
    have hm : O (fun _ => penalty L k) ∈ candidateTours d O L := by
      simp only [candidateTours,List.mem_filter,decide_eq_true_eq,List.mem_map,List.mem_range]
      exact ⟨⟨k,hk,rfl⟩,hb.2.1⟩
    have h := (hbest _ hm).trans hb.2.2
    exact_mod_cast h
  · have hm : missed (cor4Approx d p O L) ≤ Fintype.card V := by
      unfold missed
      simpa using Finset.card_filter_le (Finset.univ : Finset V) (fun v => v ∉ cor4Approx d p O L)
    have h := hm.trans (Nat.le_of_not_gt hk)
    have hh : missed (cor4Approx d p O L) ≤ 3*k := h.trans (by omega)
    exact_mod_cast hh
end Queelius.MinLatency

end

open MinLatency.Approx

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (hd : IsMetric d) (O : (V → ℝ) → List V)
    (hO : PCAdmissible d p O) :
    IsTSPApprox d p 3 6 (cor4Approx d p O) := by
  exact Queelius.MinLatency.cor4_approximator d p hd O hO


section
open MinLatency.Approx
namespace Queelius.MinLatency.Controls

def discrete (i j : Fin 2) : ℝ := if i=j then 0 else 1

theorem discrete_metric : IsMetric discrete := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [discrete]
  · intro i; simp [discrete]
  · intro i j h; simp [discrete,h]
  · intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [discrete]

theorem singleton_cost : pcCost discrete (fun _ => 3) [0] = 3 := by
  norm_num [pcCost,discrete,tourLen,pathLen,Fin.sum_univ_two,Finset.sum_filter] <;> decide

theorem zero_penalty_misses : pcCost discrete (fun _ => 0) [0] = 0 ∧ missed ([0] : List (Fin 2)) = 1 := by
  norm_num [pcCost,discrete,tourLen,pathLen,missed,Fin.sum_univ_two,Finset.sum_filter,
    Finset.univ_fin2] <;> decide

theorem zero_miss_penalty_positive : penalty 2 0 = 8 := by norm_num [penalty]
end Queelius.MinLatency.Controls

namespace Queelius.MinLatency.Controls

theorem finite_scan_keeps_short_tour : cor4Approx discrete 0 (fun _ => [0,1]) 1 = [0,1] := by
  norm_num [cor4Approx,discrete,tourLen,pathLen,List.argmax,List.argAux]
  simp [List.replicate_succ,List.argAux]

theorem finite_scan_falls_back : cor4Approx discrete 0 (fun _ => [0,1]) (1/4) = [0] := by
  norm_num [cor4Approx,discrete,tourLen,pathLen,List.argmax,List.argAux]
end Queelius.MinLatency.Controls

end

-- Prove2me | solution 1 for HyperCheeger.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:30.581878+00:00
-- url     : https://prove2.me/submissions/cfdba825-a8c9-418a-a5b1-9d43b1856276

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2

section
set_option autoImplicit false

open scoped Matrix

namespace HyperCheeger.Dev.Eq5

open HyperCheeger HyperCheeger.Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in

theorem adj_apply_eq (H : Hypergraph V) (u v : V) :
    H.adj u v = ∑ e ∈ H.edges,
      (if u ∈ e then (if v ∈ e then (if u = v then 0 else H.w e / ((e.card : ℝ) - 1)) else 0)
        else 0) := by
  simp only [Hypergraph.adj, Matrix.of_apply]
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, if_false, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hu : u ∈ e <;> by_cases hv : v ∈ e <;>
      simp [hu, hv, Finset.insert_subset_iff]

theorem sum_adj_mul (H : Hypergraph V) (u : V) (f : V → ℝ) :
    ∑ v, H.adj u v * f v = ∑ e ∈ H.edges,
      (if u ∈ e then H.w e / ((e.card : ℝ) - 1) * ∑ v ∈ e, (if u = v then 0 else f v)
        else 0) := by
  simp_rw [adj_apply_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hu : u ∈ e
  · simp only [hu, if_true, ite_mul, zero_mul, Finset.mul_sum]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  · simp [hu]

theorem degree_eq_sum_adj (H : Hypergraph V) (u : V) :
    H.degree u = ∑ v, H.adj u v := by
  have h := sum_adj_mul H u (fun _ => 1)
  simp only [mul_one] at h
  rw [h, Hypergraph.degree, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  by_cases hu : u ∈ e
  · simp only [hu, if_true]
    have hsum : ∑ v ∈ e, (if u = v then (0 : ℝ) else 1) = (e.card : ℝ) - 1 := by
      have : ∑ v ∈ e, (if u = v then (0 : ℝ) else 1)
          = ∑ v ∈ e, ((1 : ℝ) - if u = v then 1 else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp [hu]
    rw [hsum]
    have hpos : (1 : ℕ) ≤ e.card := Finset.card_pos.mpr ⟨u, hu⟩
    have hne : e.card ≠ 1 := H.card_ne_one e he
    have h2 : (2 : ℝ) ≤ e.card := by exact_mod_cast (by omega : 2 ≤ e.card)
    field_simp [show (e.card : ℝ) - 1 ≠ 0 by linarith]
  · simp [hu]

theorem sum_sum_adj_mul (H : Hypergraph V) (f : V → V → ℝ) :
    ∑ u, ∑ v, H.adj u v * f u v = ∑ e ∈ H.edges,
      H.w e / ((e.card : ℝ) - 1) * ∑ u ∈ e, ∑ v ∈ e, (if u = v then 0 else f u v) := by
  simp_rw [sum_adj_mul H _ (f _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

omit [Fintype V] in
theorem pair_sum (s : Finset V) (x : V → ℝ) :
    ∑ u ∈ s, ∑ v ∈ s, (if u = v then 0 else x u * x u - x u * x v) =
      1 / 2 * ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 := by
  have h1 : ∀ u v, (if u = v then 0 else x u * x u - x u * x v) = x u * x u - x u * x v := by
    intro u v
    split_ifs with h
    · subst h; ring
    · rfl
  simp_rw [h1]
  have h2 : ∑ u ∈ s, ∑ v ∈ s, (x u - x v) ^ 2 =
      ∑ u ∈ s, ∑ v ∈ s, (x u * x u - x u * x v) +
        ∑ u ∈ s, ∑ v ∈ s, (x v * x v - x v * x u) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h2, Finset.sum_comm (f := fun u v => x v * x v - x v * x u)]
  ring

end HyperCheeger.Dev.Eq5

namespace HyperCheeger

open HyperCheeger.Dev.Eq5 in
theorem chk_eq_5 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) (x : V → ℝ) :
    x ⬝ᵥ (H.lap *ᵥ x) =
      ∑ e ∈ H.edges, H.w e / ((e.card : ℝ) - 1) * (1 / 2 * ∑ u ∈ e, ∑ v ∈ e, (x u - x v) ^ 2) := by
  have hL : x ⬝ᵥ (H.lap *ᵥ x) = ∑ u, ∑ v, H.adj u v * (x u * x u - x u * x v) := by
    simp only [dotProduct, Matrix.mulVec, Hypergraph.lap, Hypergraph.degMat, Matrix.sub_apply,
      Matrix.diagonal_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [degree_eq_sum_adj, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hL, sum_sum_adj_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pair_sum]

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_5 := @HyperCheeger.chk_eq_5

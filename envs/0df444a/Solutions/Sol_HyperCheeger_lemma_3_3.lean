-- Prove2me | solution 1 for HyperCheeger.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:30.684201+00:00
-- url     : https://prove2.me/submissions/e22258fb-8903-4225-9792-f0b0c64c3451

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Lemma33

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

omit [Fintype V] in
theorem ae_adj (H : Hypergraph V) : H.aeGraph.adj = H.adj := by
  ext u v
  simp only [Hypergraph.adj, Matrix.of_apply]
  by_cases huv : u = v
  · simp [huv]
  simp only [huv, if_false]
  have key : H.aeGraph.edges.filter (fun p => {u, v} ⊆ p) ⊆ {{u, v}} := by
    intro p hp
    obtain ⟨hp, hsub⟩ := Finset.mem_filter.mp hp
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    have hc : p.card = 2 := (Finset.mem_powersetCard.mp hpe).2
    have : ({u, v} : Finset V) = p :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hc, Finset.card_pair huv])
    simp [this]
  by_cases hm : ({u, v} : Finset V) ∈ H.aeGraph.edges
  · have hf : H.aeGraph.edges.filter (fun p => {u, v} ⊆ p) = {{u, v}} :=
      Finset.Subset.antisymm key
        (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hm, subset_refl _⟩))
    rw [hf, Finset.sum_singleton, Finset.card_pair huv]
    norm_num
    rfl
  · have hf : H.aeGraph.edges.filter (fun p => {u, v} ⊆ p) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      have := key hp
      rw [Finset.mem_singleton] at this
      subst this
      exact hm (Finset.mem_filter.mp hp).1
    rw [hf, Finset.sum_empty]
    symm
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨he, hsub⟩ := Finset.mem_filter.mp he
    exact absurd (Finset.mem_biUnion.mpr
      ⟨e, he, Finset.mem_powersetCard.mpr ⟨hsub, Finset.card_pair huv⟩⟩) hm

theorem ae_degree (H : Hypergraph V) : H.aeGraph.degree = H.degree := by
  funext u
  rw [degree_eq_sum_adj, degree_eq_sum_adj, ae_adj]

end HyperCheeger.Dev.Lemma33

namespace HyperCheeger

open HyperCheeger.Dev.Lemma33 in
theorem chk_lemma_3_3 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    H.aeGraph.IsTwoGraph ∧ H.aeGraph.adj = H.adj ∧ H.aeGraph.lap = H.lap ∧
      H.aeGraph.normLap = H.normLap := by
  have hlap : H.aeGraph.lap = H.lap := by
    simp only [Hypergraph.lap, Hypergraph.degMat, ae_adj, ae_degree]
  refine ⟨?_, ae_adj H, hlap, ?_⟩
  · intro p hp
    obtain ⟨_, _, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_powersetCard.mp hp).2
  · simp only [Hypergraph.normLap, Hypergraph.degInvSqrt, hlap, ae_degree]

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_lemma_3_3 := @HyperCheeger.chk_lemma_3_3

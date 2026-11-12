-- Prove2me | solution 1 for HararySachs.Hyper.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T03:06:48.445712+00:00
-- url     : https://prove2.me/submissions/24d30697-342d-4613-95e7-f4a061ed9cac

import Mathlib
import Definitions.Def_HararySachs_Hyper_Veblen

open HararySachs.Hyper

namespace Lemma9Aux

variable {n : ℕ}

/-- Every edge listed by a rooting is an edge of the multigraph. -/
lemma edge_mem {S : MultiGraph n} {R : Fin S.card → Fin n × Finset (Fin n)}
    (hR : IsRooting S R) (i : Fin S.card) : (R i).2 ∈ S := by
  rw [← hR.2.2]
  simp

/-- The degree of `v` in `S` counts the positions of the rooting whose edge contains `v`. -/
lemma deg_eq {S : MultiGraph n} {R : Fin S.card → Fin n × Finset (Fin n)}
    (hR : IsRooting S R) (v : Fin n) :
    vertexDegree S v = ∑ i, if v ∈ (R i).2 then 1 else 0 := by
  classical
  unfold vertexDegree
  conv_lhs => rw [← hR.2.2, ← Fin.univ_val_map]
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val,
    Finset.card_filter]
  rfl

/-- Out-degree of `u` in the rooted digraph: `k - 1` arcs for every edge rooted at `u`. -/
lemma outDeg_eq {k : ℕ} {S : MultiGraph n} (hS : IsUniform S k)
    {R : Fin S.card → Fin n × Finset (Fin n)} (hR : IsRooting S R) (u : Fin n) :
    outDeg (rootedArcs R) u = ∑ i, if (R i).1 = u then k - 1 else 0 := by
  classical
  unfold outDeg rootedArcs
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : (R i).1 = u
  · simp only [h, true_and, if_true]
    rw [← Finset.card_filter, ← hS _ (edge_mem hR i)]
    have hu : u ∈ (R i).2 := h ▸ hR.1 i
    rw [← Finset.card_erase_of_mem hu]
    congr 1
    ext v
    simp [Finset.mem_erase, and_comm]
  · simp [h]

/-- In-degree of `v` in the rooted digraph: one arc for every edge containing `v`
that is rooted elsewhere. -/
lemma inDeg_eq {S : MultiGraph n} {R : Fin S.card → Fin n × Finset (Fin n)} (v : Fin n) :
    inDeg (rootedArcs R) v = ∑ i, if v ∈ (R i).2 ∧ (R i).1 ≠ v then 1 else 0 := by
  classical
  unfold inDeg rootedArcs
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single (R i).1]
  · simp [eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The degree identity `deg_S v = k · #(roots at v)` for an Euler rooting. -/
lemma deg_eq_mul {k : ℕ} (hk : 2 ≤ k) {S : MultiGraph n} (hS : IsUniform S k)
    {R : Fin S.card → Fin n × Finset (Fin n)} (hR : IsEulerRooting S R) (v : Fin n) :
    vertexDegree S v = k * (Finset.univ.filter (fun i => (R i).1 = v)).card := by
  classical
  have hbal := hR.2.2.1 v
  rw [outDeg_eq hS hR.1, inDeg_eq] at hbal
  rw [deg_eq hR.1, Finset.card_filter]
  have hsplit : ∀ i, (if v ∈ (R i).2 then 1 else 0) =
      (if (R i).1 = v then 1 else 0) + (if v ∈ (R i).2 ∧ (R i).1 ≠ v then 1 else 0) := by
    intro i
    by_cases h : (R i).1 = v
    · have : v ∈ (R i).2 := h ▸ hR.1.1 i
      simp [h, this]
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, ← hbal,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

end Lemma9Aux

open Lemma9Aux in
theorem solution {n k : ℕ} (hk : 2 ≤ k) (S : MultiGraph n)
    (hS : IsUniform S k)
    (R : Fin S.card → Fin n × Finset (Fin n))
    (hR : IsEulerRooting S R) :
    IsVeblen S k ∧ IsConnected S ∧
      ∀ v ∈ covered S,
        vertexDegree S v = k *
          (Finset.univ.filter (fun i => (R i).1 = v)).card := by
  classical
  have hdeg := deg_eq_mul hk hS hR
  refine ⟨⟨hS, fun v => ⟨_, hdeg v⟩⟩, ⟨?_, ?_⟩, fun v _ => hdeg v⟩
  · -- `S` is nonempty: an Eulerian digraph has an active vertex, hence an arc, hence an edge.
    intro h0
    obtain ⟨w, hw⟩ := hR.2.1
    have hcard : S.card = 0 := by simp [h0]
    have hzero : ∀ a b, rootedArcs R a b = 0 := by
      intro a b
      unfold rootedArcs
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i
      exact absurd i.2 (by omega)
    simp [active, outDeg, inDeg, hzero] at hw
  · intro u hu v hv
    -- covered vertices are active in `D_R`
    have hact : ∀ w ∈ covered S, w ∈ active (rootedArcs R) := by
      intro w hw
      simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [hdeg w] at hw
      have hr : 0 < (Finset.univ.filter (fun i => (R i).1 = w)).card :=
        Nat.pos_of_mul_pos_left hw
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      have : 0 < outDeg (rootedArcs R) w := by
        rw [outDeg_eq hS hR.1, ← Finset.sum_filter]
        simp only [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_pos hr (by omega)
      omega
    have hpath := hR.2.2.2 u (hact u hu) v (hact v hv)
    refine Relation.ReflTransGen.mono ?_ u v hpath
    -- a positive arc lies inside an edge of `S`
    have harc : ∀ a b, 0 < rootedArcs R a b → EdgeAdjacent S a b := by
      intro a b hab
      unfold rootedArcs at hab
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨(R i).2, edge_mem hR.1 i, hi.1 ▸ hR.1.1 i, hi.2.1⟩
    intro a b hab
    rcases hab with h | h
    · exact harc a b h
    · obtain ⟨e, he, hb, ha⟩ := harc b a h
      exact ⟨e, he, ha, hb⟩

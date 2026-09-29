-- Prove2me | solution 1 for KServer.tree_four_point
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T19:35:40.14652+00:00
-- url     : https://prove2.me/submissions/0bbd54d0-75b5-4274-ad5c-0b3416337171

import Mathlib
import Definitions.Def_KServer_tree_metric

open KServer

section Tree
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

private theorem walkWeight_append (w : V → V → ℝ) {u v z : V}
    (p : G.Walk u v) (q : G.Walk v z) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
  unfold walkWeight
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

end Tree

/-- In a tree vertex space, a vertex on the path between `u` and `v` is metrically
between them. -/
private theorem dist_of_mem_support {M : Type} [MetricSpace M] [DecidableEq M]
    {G : SimpleGraph M} (w : M → M → ℝ)
    (hw : ∀ (u v : M) (p : G.Path u v), dist u v = walkWeight w (p : G.Walk u v))
    {u v : M} (p : G.Walk u v) (hp : p.IsPath) (z : M) (hz : z ∈ p.support) :
    dist u z + dist z v = dist u v := by
  have h1 := hw u z ⟨p.takeUntil z hz, hp.takeUntil hz⟩
  have h2 := hw z v ⟨p.dropUntil z hz, hp.dropUntil hz⟩
  have h3 := hw u v ⟨p, hp⟩
  have h4 : walkWeight w ((p.takeUntil z hz).append (p.dropUntil z hz))
      = walkWeight w (p.takeUntil z hz) + walkWeight w (p.dropUntil z hz) :=
    walkWeight_append w _ _
  rw [p.take_spec hz] at h4
  simp only at h1 h2 h3
  rw [h1, h2, h3, h4]

/-- A vertex lying beyond `m` on a path is farther from the start than `m` is. -/
private theorem dist_after {M : Type} [MetricSpace M] [DecidableEq M]
    {G : SimpleGraph M} (w : M → M → ℝ)
    (hw : ∀ (u v : M) (p : G.Path u v), dist u v = walkWeight w (p : G.Walk u v))
    {u v : M} (p : G.Walk u v) (hp : p.IsPath) (m : M) (hm : m ∈ p.support)
    (z : M) (hz : z ∈ (p.dropUntil m hm).support) :
    dist u z = dist u m + dist m z := by
  have hzp : z ∈ p.support := SimpleGraph.Walk.support_dropUntil_subset p hm hz
  have h1 := dist_of_mem_support w hw p hp z hzp
  have h2 := dist_of_mem_support w hw p hp m hm
  have h3 := dist_of_mem_support w hw (p.dropUntil m hm) (hp.dropUntil hm) z hz
  linarith

/-- **Medians exist in a tree**: for any three points there is a point on the path
between the first two lying metrically between each pair. -/
private theorem exists_median_on {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    {G : SimpleGraph M} (hG : G.IsTree) (w : M → M → ℝ)
    (hw : ∀ (u v : M) (p : G.Path u v), dist u v = walkWeight w (p : G.Walk u v))
    {a b : M} (P : G.Walk a b) (hP : P.IsPath) (c : M) :
    ∃ m, m ∈ P.support ∧ dist a m + dist m b = dist a b ∧ dist a m + dist m c = dist a c
      ∧ dist b m + dist m c = dist b c := by
  classical
  obtain ⟨Q, hQ, -⟩ := hG.existsUnique_path a c
  have haS : a ∈ Finset.univ.filter (fun z => z ∈ P.support ∧ z ∈ Q.support) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨P.start_mem_support, Q.start_mem_support⟩
  obtain ⟨m, hmS, hmax⟩ := (Finset.univ.filter
    (fun z => z ∈ P.support ∧ z ∈ Q.support)).exists_max_image (fun z => dist a z) ⟨a, haS⟩
  obtain ⟨hmP, hmQ⟩ : m ∈ P.support ∧ m ∈ Q.support := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmS
  refine ⟨m, hmP, dist_of_mem_support w hw P hP m hmP,
    dist_of_mem_support w hw Q hQ m hmQ, ?_⟩
  have hWpath : (((P.dropUntil m hmP).reverse).append (Q.dropUntil m hmQ)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse]
    refine List.Nodup.append ?_ ?_ ?_
    · exact List.nodup_reverse.mpr (hP.dropUntil hmP).support_nodup
    · exact ((hQ.dropUntil hmQ).support_nodup).sublist (List.tail_sublist _)
    · intro z hz1 hz2
      have hz1' : z ∈ (P.dropUntil m hmP).support := by simpa using hz1
      have hz2' : z ∈ (Q.dropUntil m hmQ).support := List.mem_of_mem_tail hz2
      have hzne : z ≠ m := by
        intro h
        subst h
        have hnd := (hQ.dropUntil hmQ).support_nodup
        rw [SimpleGraph.Walk.support_eq_cons] at hnd
        exact (List.nodup_cons.mp hnd).1 hz2
      have hzP : z ∈ P.support := SimpleGraph.Walk.support_dropUntil_subset P hmP hz1'
      have hzQ : z ∈ Q.support := SimpleGraph.Walk.support_dropUntil_subset Q hmQ hz2'
      have hin : z ∈ Finset.univ.filter (fun y => y ∈ P.support ∧ y ∈ Q.support) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hzP, hzQ⟩
      have hle := hmax z hin
      have heq := dist_after w hw P hP m hmP z hz1'
      have hpos : 0 < dist m z := dist_pos.mpr (Ne.symm hzne)
      try simp only at hle
      linarith
  have hmW : m ∈ (((P.dropUntil m hmP).reverse).append (Q.dropUntil m hmQ)).support :=
    SimpleGraph.Walk.mem_support_append_iff .. |>.mpr (Or.inr (Q.dropUntil m hmQ).start_mem_support)
  exact dist_of_mem_support w hw _ hWpath m hmW

/-- Two vertices of a path are comparable along it. -/
private theorem support_total {M : Type} [MetricSpace M] [DecidableEq M]
    {G : SimpleGraph M} (w : M → M → ℝ)
    (hw : ∀ (u v : M) (p : G.Path u v), dist u v = walkWeight w (p : G.Walk u v))
    {a b : M} (P : G.Walk a b) (hP : P.IsPath) (m n : M)
    (hm : m ∈ P.support) (hn : n ∈ P.support) :
    dist a n = dist a m + dist m n ∨ dist a m = dist a n + dist n m := by
  have hsplit : n ∈ (P.takeUntil m hm).support ∨ n ∈ (P.dropUntil m hm).support := by
    have : n ∈ ((P.takeUntil m hm).append (P.dropUntil m hm)).support := by
      rw [P.take_spec hm]; exact hn
    exact SimpleGraph.Walk.mem_support_append_iff .. |>.mp this
  rcases hsplit with h | h
  · right
    exact (dist_of_mem_support w hw (P.takeUntil m hm) (hP.takeUntil hm) n h).symm
  · left
    exact dist_after w hw P hP m hm n h

/-- **Tree metrics are quasiconcave**: the four-point condition. -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (a b c d : M) :
    dist a b + dist c d ≤ max (dist a c + dist b d) (dist a d + dist b c) := by
  classical
  obtain ⟨G, hG, w, hw⟩ := hM
  obtain ⟨P, hP, -⟩ := hG.existsUnique_path a b
  obtain ⟨m, hmP, hm1, hm2, hm3⟩ := exists_median_on hG w hw P hP c
  obtain ⟨n, hnP, hn1, hn2, hn3⟩ := exists_median_on hG w hw P hP d
  have tri : dist c d ≤ dist c m + dist m n + dist n d := by
    have t1 : dist c d ≤ dist c m + dist m d := dist_triangle c m d
    have t2 : dist m d ≤ dist m n + dist n d := dist_triangle m n d
    linarith
  have ecm : dist m c = dist c m := dist_comm m c
  have end' : dist n d = dist d n := dist_comm n d
  have ebm : dist b m = dist m b := dist_comm b m
  have ebn : dist b n = dist n b := dist_comm b n
  rcases support_total w hw P hP m n hmP hnP with h | h
  · refine le_trans ?_ (le_max_right _ _)
    linarith
  · refine le_trans ?_ (le_max_left _ _)
    have emn : dist n m = dist m n := dist_comm n m
    linarith

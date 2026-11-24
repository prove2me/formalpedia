-- Prove2me | solution 1 for MTWalkSAT3CNF.TwoOcc.display_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T14:04:37.379279+00:00
-- url     : https://prove2.me/submissions/5d4e53a7-cd8b-4c04-8e84-15623579b6d2

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

open MTWalkSAT3CNF.TwoOcc

theorem solution {W : Type*} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : W) :
    ∑ u ∈ T.neighborFinset r, treeWeight T u =
      ((T.degree r + 3 : ℝ) / 2) * treeWeight T r - 3 / 2 := by
  classical
  have key : ∀ v, v ≠ r → ∃ s ∈ T.neighborFinset r, T.dist s v + 1 = T.dist r v ∧
      ∀ u ∈ T.neighborFinset r, u ≠ s → T.dist u v = T.dist r v + 1 := by
    intro v hv
    obtain ⟨p, hp, hlen⟩ := hT.connected.exists_path_of_dist r v
    cases p with
    | nil => exact absurd rfl hv
    | @cons _ s _ h q =>
      have hq : T.dist s v ≤ q.length := SimpleGraph.dist_le q
      rw [SimpleGraph.Walk.length_cons] at hlen
      have e1 : T.dist v r = T.dist r v := SimpleGraph.dist_comm
      have e2 : T.dist v s = T.dist s v := SimpleGraph.dist_comm
      have hs : T.dist s v + 1 = T.dist r v := by
        rcases hT.dist_eq_dist_add_one_of_adj v h with h1 | h1 <;> omega
      refine ⟨s, (SimpleGraph.mem_neighborFinset _ _ _).mpr h, hs, fun u hu hus => ?_⟩
      rw [SimpleGraph.mem_neighborFinset] at hu
      have e3 : T.dist v u = T.dist u v := SimpleGraph.dist_comm
      rcases hT.dist_eq_dist_add_one_of_adj v hu with h1 | h1
      · exfalso
        obtain ⟨q', hq', hlen'⟩ := hT.connected.exists_path_of_dist u v
        have hp' : (SimpleGraph.Walk.cons hu q').IsPath := by
          apply SimpleGraph.Walk.isPath_of_length_eq_dist
          rw [SimpleGraph.Walk.length_cons, hlen']
          omega
        have := (hT.existsUnique_path r v).unique hp' hp
        simp only [SimpleGraph.Walk.cons.injEq] at this
        exact hus this.1
      · omega
  have hsplit : ∀ v, ∑ u ∈ T.neighborFinset r, (1 / 2 : ℝ) ^ T.dist u v =
      if v = r then (T.degree r : ℝ) / 2
      else ((T.degree r + 3 : ℝ) / 2) * (1 / 2 : ℝ) ^ T.dist r v := by
    intro v
    split_ifs with hv
    · subst hv
      have : ∀ u ∈ T.neighborFinset v, (1 / 2 : ℝ) ^ T.dist u v = 1 / 2 := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm, pow_one]
      rw [Finset.sum_congr rfl this, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
      ring
    · obtain ⟨s, hs, hs1, hsu⟩ := key v hv
      rw [← Finset.add_sum_erase _ _ hs]
      have hrest : ∀ u ∈ (T.neighborFinset r).erase s,
          (1 / 2 : ℝ) ^ T.dist u v = (1 / 2 : ℝ) ^ (T.dist r v + 1) := by
        intro u hu
        rw [hsu u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)]
      rw [Finset.sum_congr rfl hrest, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((T.neighborFinset r).erase s).card + 1 = T.degree r := by
        rw [Finset.card_erase_add_one hs, SimpleGraph.card_neighborFinset_eq_degree]
      have hc : (((T.neighborFinset r).erase s).card : ℝ) = (T.degree r : ℝ) - 1 := by
        rw [← hcard]
        push_cast
        ring
      rw [hc, ← hs1]
      ring
  have hA : ∑ v, (if v = r then (T.degree r : ℝ) / 2
      else ((T.degree r + 3 : ℝ) / 2) * (1 / 2 : ℝ) ^ T.dist r v)
      = (T.degree r : ℝ) / 2 + ((T.degree r + 3 : ℝ) / 2) *
          ∑ v ∈ Finset.univ.erase r, (1 / 2 : ℝ) ^ T.dist r v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), if_pos rfl, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun v hv => if_neg (Finset.ne_of_mem_erase hv))
  have hB : ∑ v, (1 / 2 : ℝ) ^ T.dist r v
      = 1 + ∑ v ∈ Finset.univ.erase r, (1 / 2 : ℝ) ^ T.dist r v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), SimpleGraph.dist_self, pow_zero]
  unfold treeWeight distWeight
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun v _ => hsplit v), hA, hB]
  ring

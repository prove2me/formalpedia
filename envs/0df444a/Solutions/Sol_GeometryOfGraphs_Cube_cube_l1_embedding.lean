-- Prove2me | solution 1 for GeometryOfGraphs.Cube.cube_l1_embedding
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:32:26.842802+00:00
-- url     : https://prove2.me/submissions/8737d6bd-d99f-4ec4-b68a-1929ad8cb7d5

import Definitions.Def_GeometryOfGraphs_Cube_Hypercube
open GeometryOfGraphs.Cube

private theorem cube_walk (m : ℕ) (x y : Fin m → Bool) :
    ∃ p : (hypercube m).Walk x y, p.length = hammingDist x y := by
  classical
  generalize hd : hammingDist x y = d
  induction d using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases hz : d = 0
    · have hxy : x = y := hammingDist_eq_zero.mp (hd.trans hz)
      subst x
      exact ⟨.nil, by simp [← hd]⟩
    · have hne : (Finset.univ.filter (fun i => x i ≠ y i)).Nonempty := by
        apply Finset.card_pos.mp
        change 0 < hammingDist x y
        omega
      obtain ⟨i, hi⟩ := hne
      have hxi : x i ≠ y i := (Finset.mem_filter.mp hi).2
      let z := Function.update x i (y i)
      have hzfilter : Finset.univ.filter (fun j => z j ≠ y j) =
          (Finset.univ.filter (fun j => x j ≠ y j)).erase i := by
        ext j
        by_cases hj : j = i
        · subst j; simp [z]
        · simp [z, Function.update_of_ne hj, hj]
      have hdz : hammingDist z y + 1 = d := by
        unfold hammingDist
        rw [hzfilter, Finset.card_erase_add_one hi]
        exact hd
      have hadj : (hypercube m).Adj x z := by
        change (Finset.univ.filter (fun j => x j ≠ z j)).card = 1
        have hf : Finset.univ.filter (fun j => x j ≠ z j) = {i} := by
          ext j
          by_cases hj : j = i
          · subst j; simp [z, hxi]
          · simp [z, Function.update_of_ne hj, hj]
        rw [hf]
        simp
      obtain ⟨p, hp⟩ := ih (hammingDist z y) (by omega) z rfl
      exact ⟨.cons hadj p, by simp [hp]; omega⟩

private theorem hamming_le_walk {m : ℕ} {x y : Fin m → Bool}
    (p : (hypercube m).Walk x y) : hammingDist x y ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x z y h p ih =>
    have ht := hammingDist_triangle x z y
    have hh : hammingDist x z = 1 := h
    simp only [SimpleGraph.Walk.length_cons]
    omega

private theorem cube_dist (m : ℕ) (x y : Fin m → Bool) :
    (hypercube m).dist x y = hammingDist x y := by
  obtain ⟨p, hp⟩ := cube_walk m x y
  apply Nat.le_antisymm
  · simpa [hp] using (hypercube m).dist_le p
  · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    simpa [hq] using hamming_le_walk q

theorem solution (m : ℕ) :
    ∃ φ : (Fin m → Bool) → (Fin m → ℝ), ∀ x y,
      (∑ k : Fin m, |φ x k - φ y k|) = ((hypercube m).dist x y : ℝ) := by
  classical
  refine ⟨fun x k => if x k then 1 else 0, ?_⟩
  intro x y
  rw [cube_dist]
  simp only [hammingDist, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  cases hx : x k <;> cases hy : y k <;> simp [hx, hy]

#print axioms solution

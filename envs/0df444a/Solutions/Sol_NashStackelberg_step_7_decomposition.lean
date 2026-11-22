-- Prove2me | solution 1 for NashStackelberg.step_7_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:28:10.124147+00:00
-- url     : https://prove2.me/submissions/273f4e36-25f7-4bbd-96b2-ad550375cf58

import Mathlib

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (K : Fin k → Set E) (hK : ∀ j, Convex ℝ (K j)) {x : E} (hx : x ∈ convexHull ℝ (⋃ j, K j)) :
    ∃ (p : Fin k → ℝ) (pts : Fin k → E), (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
      (∀ j, (K j).Nonempty → pts j ∈ K j) ∧ (∀ j, K j = ∅ → p j = 0) ∧
      x = ∑ j, p j • pts j := by
  classical
  rw [mem_convexHull_iff_exists_fintype] at hx
  obtain ⟨ι, inst, w, z, hw0, hw1, hz, hsum⟩ := hx
  letI : Fintype ι := inst
  -- choose a block for each point
  let g : ι → Fin k := fun i => Classical.choose (Set.mem_iUnion.mp (hz i))
  have hgz : ∀ i, z i ∈ K (g i) := fun i => Classical.choose_spec (Set.mem_iUnion.mp (hz i))
  -- group the points by block
  let fib : Fin k → Finset ι := fun j => Finset.univ.filter (fun i => g i = j)
  let p : Fin k → ℝ := fun j => ∑ i ∈ fib j, w i
  let pts : Fin k → E := fun j =>
    if hp : p j = 0 then (if hj : (K j).Nonempty then Classical.choose hj else 0)
    else (fib j).centerMass w z
  refine ⟨p, pts, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro j
    exact Finset.sum_nonneg (fun i _ => hw0 i)
  · -- the weights sum to one
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
      (fun i _ => Finset.mem_univ (g i)) (fun i => w i)
    simpa [p, fib, hw1] using hfib
  · -- membership in the blocks
    intro j hjne
    by_cases hp : p j = 0
    · simp only [pts, dif_pos hp, dif_pos hjne]
      exact Classical.choose_spec hjne
    · have hpos : 0 < ∑ i ∈ fib j, w i := by
        have h0 : 0 ≤ ∑ i ∈ fib j, w i := Finset.sum_nonneg (fun i _ => hw0 i)
        exact lt_of_le_of_ne h0 (Ne.symm (by simpa [p] using hp))
      simp only [pts, dif_neg hp]
      exact Convex.centerMass_mem (hK j) (fun i _ => hw0 i) hpos (fun i hi => by
        have hgi : g i = j := (Finset.mem_filter.mp hi).2
        rw [← hgi]
        exact hgz i)
  · -- empty blocks get weight zero
    intro j hKj
    by_contra hp
    have h0 : 0 ≤ ∑ i ∈ fib j, w i := Finset.sum_nonneg (fun i _ => hw0 i)
    have hpos : 0 < ∑ i ∈ fib j, w i := lt_of_le_of_ne h0 (Ne.symm (by simpa [p] using hp))
    have hne : (fib j).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hpos
      simp at hpos
    obtain ⟨i, hi⟩ := hne
    have hgi : g i = j := (Finset.mem_filter.mp hi).2
    have hzi : z i ∈ K j := by
      rw [← hgi]
      exact hgz i
    rw [hKj] at hzi
    exact hzi
  · -- the reconstruction identity
    have hkey : ∀ j, ∑ i ∈ fib j, w i • z i = p j • pts j := by
      intro j
      by_cases hp : p j = 0
      · have hwzero : ∀ i ∈ fib j, w i = 0 := by
          apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw0 i)).mp
          simpa [p] using hp
        rw [hp, zero_smul]
        apply Finset.sum_eq_zero
        intro i hi
        rw [hwzero i hi, zero_smul]
      · simp only [pts, dif_neg hp]
        rw [Finset.centerMass, smul_smul]
        have hpsum : (∑ i ∈ fib j, w i) = p j := rfl
        rw [hpsum, mul_inv_cancel₀ hp, one_smul]
    rw [← hsum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
      (fun i _ => Finset.mem_univ (g i)) (fun i => w i • z i)]
    apply Finset.sum_congr rfl
    intro j _
    exact hkey j


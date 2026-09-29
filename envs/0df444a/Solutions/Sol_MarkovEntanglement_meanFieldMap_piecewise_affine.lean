-- Prove2me | solution 1 for MarkovEntanglement.meanFieldMap_piecewise_affine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-30T23:27:08.14195+00:00
-- url     : https://prove2.me/submissions/53469469-b818-492c-aae8-6a7d99f889cd

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

/-- If `y` has strictly higher priority than `x`, the mass strictly above `y`, together with
the mass sitting in `y` itself, is part of the mass strictly above `x`. -/
theorem me_hpm_add_le {S : Type*} [Fintype S] [DecidableEq S] (ν : S → ℝ) (m : S → ℝ)
    (hm : ∀ z, 0 ≤ m z) {x y : S} (hxy : ν x < ν y) :
    higherPriorityMass ν m y + m y ≤ higherPriorityMass ν m x := by
  unfold higherPriorityMass
  have hy : y ∉ Finset.univ.filter (fun z => ν y < ν z) := by simp
  rw [add_comm, ← Finset.sum_insert hy]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hm z)
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  rcases hz with rfl | hz
  · exact hxy
  · exact hxy.trans hz

/-- The activated fraction depends continuously on the configuration. -/
theorem me_activateFraction_continuous {S : Type*} [Fintype S] [DecidableEq S]
    (ν : S → ℝ) (α : ℝ) (x : S) :
    Continuous fun m : S → ℝ => activateFraction ν α m x := by
  unfold activateFraction higherPriorityMass
  exact (continuous_apply x).min (continuous_const.max
    (continuous_const.sub (continuous_finsetSum _ fun y _ => continuous_apply y)))

/-- Inside the priority region of `x` the activated fraction is explicit: states of strictly
higher priority are fully served, states of strictly lower priority are not served at all,
and `x` itself absorbs whatever is left of the budget. -/
theorem me_activateFraction_region {S : Type*} [Fintype S] [DecidableEq S]
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (m : S → ℝ) (hm : ∀ z, 0 ≤ m z)
    {x : S} (hreg : IsPriorityRegion ν α m x) (y : S) :
    activateFraction ν α m y =
      if ν x < ν y then m y else if y = x then α - higherPriorityMass ν m x else 0 := by
  obtain ⟨h1, h2⟩ := hreg
  unfold activateFraction
  split_ifs with hlt hyx
  · have h := me_hpm_add_le ν m hm hlt
    rw [max_eq_right (by linarith [hm y]), min_eq_left (by linarith)]
  · subst hyx
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
  · have hne : ν y ≠ ν x := fun h => hyx (hν h)
    have hyx' : ν y < ν x := lt_of_le_of_ne (not_lt.1 hlt) hne
    have h := me_hpm_add_le ν m hm hyx'
    rw [max_eq_left (by linarith), min_eq_right (hm y)]

theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) :
    Continuous (meanFieldMap P0 P1 ν α) ∧
      ∀ x : S, ∃ (K : Matrix S S ℝ) (b : S → ℝ),
        ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
          meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z := by
  constructor
  · apply continuous_pi
    intro z
    unfold meanFieldMap
    refine continuous_finsetSum _ fun y _ => ?_
    exact (((continuous_apply y).sub (me_activateFraction_continuous ν α y)).mul
      continuous_const).add ((me_activateFraction_continuous ν α y).mul continuous_const)
  · intro x
    refine ⟨fun y z => if ν x < ν y then P1 y z + (P0 x z - P1 x z) else P0 y z,
      fun z => α * (P1 x z - P0 x z), ?_⟩
    intro m hm hreg
    funext z
    have hval := me_activateFraction_region ν hν α m hm hreg
    have hG : ∀ y : S, ((m y - activateFraction ν α m y) * P0 y z
        + activateFraction ν α m y * P1 y z)
        = m y * (if ν x < ν y then P1 y z + (P0 x z - P1 x z) else P0 y z)
          + (if ν x < ν y then -(m y * (P0 x z - P1 x z)) else 0)
          + (if y = x then (higherPriorityMass ν m x - α) * (P0 x z - P1 x z) else 0) := by
      intro y
      rw [hval y]
      by_cases h2 : ν x < ν y
      · have h1 : y ≠ x := by
          intro h
          rw [h] at h2
          exact absurd h2 (lt_irrefl _)
        rw [if_pos h2, if_pos h2, if_pos h2, if_neg h1]
        ring
      · rw [if_neg h2, if_neg h2, if_neg h2]
        by_cases h1 : y = x
        · rw [if_pos h1, if_pos h1, h1]
          ring
        · rw [if_neg h1, if_neg h1]
          ring
    have hDsum : ∀ (c : ℝ) (t : Finset S), ∑ y ∈ t, -(m y * c) = -((∑ y ∈ t, m y) * c) := by
      intro c t
      rw [Finset.sum_mul]
      simp
    have hsum1 : ∑ y : S, (if ν x < ν y then -(m y * (P0 x z - P1 x z)) else 0)
        = -(higherPriorityMass ν m x * (P0 x z - P1 x z)) := by
      rw [← Finset.sum_filter, hDsum]
      unfold higherPriorityMass
      rfl
    have hsum2 : ∑ y : S,
        (if y = x then (higherPriorityMass ν m x - α) * (P0 x z - P1 x z) else 0)
        = (higherPriorityMass ν m x - α) * (P0 x z - P1 x z) := by
      simp
    simp only [meanFieldMap]
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hG y),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hsum1, hsum2]
    ring

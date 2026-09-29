-- Prove2me | solution 1 for NearEnemy.nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:36.91968+00:00
-- url     : https://prove2.me/submissions/238ee413-756a-4e1e-9c63-6cb5bc8d9f29

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

open NearEnemy in
theorem solution {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hgp : a ≠ b → c ≠ a → c ≠ b →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hmid : a + b = c + e)
    (hpar : ∃ t : ℝ, c - e = t • (a - b)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) =
      ({c, e} : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨t, ht⟩ := hpar
  by_cases hab : a = b
  · -- Degenerate chord: the parallel hypothesis collapses `c = e`, and the
    -- shared midpoint then collapses everything to one point.
    subst hab
    have hce : c = e := by simpa [sub_eq_zero] using ht
    subst hce
    have hca : c = a := by
      refine smul_right_injective (EuclideanSpace ℝ ι) (two_ne_zero (α := ℝ)) ?_
      calc (2 : ℝ) • c = c + c := two_smul ℝ c
        _ = a + a := hmid.symm
        _ = (2 : ℝ) • a := (two_smul ℝ a).symm
    rw [hca]
  · by_cases hca : c = a
    · -- `c = a`: equal sums force `e = b`.
      have hbe : b = e := by
        have h := hmid
        rw [hca] at h
        exact add_left_cancel h
      rw [hca, ← hbe]
    · by_cases hcb : c = b
      · -- `c = b`: equal sums force `e = a`.
        have hae : a = e := by
          have h := hmid
          rw [hcb, add_comm a b] at h
          exact add_left_cancel h
        rw [hcb, ← hae, Set.pair_comm a b]
      · -- `a`, `b`, `c` pairwise distinct: equal sums and parallel
        -- differences put `c` on the line through `a` and `b`, contradicting
        -- the no-three-collinear hypothesis.
        exfalso
        apply hgp hab hca hcb
        rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
        refine ⟨a - b, fun p hp => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨-1, by rw [vadd_eq_add]; module⟩
        · refine ⟨(t - 1) / 2, ?_⟩
          refine smul_right_injective (EuclideanSpace ℝ ι) (two_ne_zero (α := ℝ)) ?_
          rw [vadd_eq_add]
          linear_combination (norm := module) -hmid + ht

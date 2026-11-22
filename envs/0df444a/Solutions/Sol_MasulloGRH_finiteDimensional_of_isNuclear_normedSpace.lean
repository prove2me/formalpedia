-- Prove2me | solution 1 for MasulloGRH.finiteDimensional_of_isNuclear_normedSpace
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:39:49.102646+00:00
-- url     : https://prove2.me/submissions/4bc8b22a-d139-4d4c-8bd6-c894f7235884

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact

open Topology

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_finiteDimensional_of_isNuclear_normedSpace

/-- **Riesz, precompact form.** A normed space over `ℂ` in which every closed ball centred at `0`
can be covered, for the radius `1/2`, by finitely many translates of the open ball of radius `1/2`
is finite-dimensional.  No completeness is assumed. -/
theorem finiteDimensional_of_closedBall_covered (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (h : ∀ R : ℝ, ∃ t : Finset E,
      Metric.closedBall (0 : E) R ⊆ ⋃ x ∈ t, {y : E | y - x ∈ Metric.ball (0 : E) (1 / 2)}) :
    FiniteDimensional ℂ E := by
  by_contra hfd
  -- Riesz: a bounded sequence whose terms are pairwise at distance at least `1`.
  obtain ⟨R, f, -, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub (𝕜 := ℂ) (E := E) hfd
  obtain ⟨t, ht⟩ := h R
  -- every term of the sequence lies within `1/2` of some centre of the finite cover
  have hcov : ∀ n : ℕ, ∃ x ∈ t, ‖f n - x‖ < 1 / 2 := by
    intro n
    have hn : f n ∈ Metric.closedBall (0 : E) R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hfR n
    obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (ht hn)
    have hx' : f n - x ∈ Metric.ball (0 : E) (1 / 2) := hx
    exact ⟨x, hxt, mem_ball_zero_iff.mp hx'⟩
  choose g hgt hg using hcov
  -- pigeonhole: two distinct indices are sent to the same centre
  let G : ℕ → (t : Set E) := fun n => ⟨g n, hgt n⟩
  obtain ⟨m, n, hmn, hG⟩ := Finite.exists_ne_map_eq_of_infinite G
  have hgmn : g m = g n := congrArg Subtype.val hG
  have h1 : (1 : ℝ) ≤ ‖f m - f n‖ := hsep hmn
  have h2 : ‖f m - f n‖ < 1 := by
    have heq : f m - f n = (f m - g m) - (f n - g n) := by
      rw [hgmn]; abel
    calc ‖f m - f n‖ = ‖(f m - g m) - (f n - g n)‖ := by rw [heq]
      _ ≤ ‖f m - g m‖ + ‖f n - g n‖ := norm_sub_le _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add (hg m) (hg n)
      _ = 1 := by norm_num
  exact absurd h1 (not_le.mpr h2)

end Sol_MasulloGRH_finiteDimensional_of_isNuclear_normedSpace

theorem solution (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (hN : IsNuclear E) : FiniteDimensional ℂ E := by
  refine Sol_MasulloGRH_finiteDimensional_of_isNuclear_normedSpace.finiteDimensional_of_closedBall_covered
    E ?_
  intro R
  -- closed balls are von Neumann bounded, hence precompact in a nuclear space
  exact MasulloGRH.nuclear_bounded_precompact E hN (Metric.closedBall (0 : E) R)
    (NormedSpace.isVonNBounded_closedBall ℂ E R) (Metric.ball (0 : E) (1 / 2))
    (Metric.ball_mem_nhds (0 : E) (by norm_num))

-- Prove2me | solution 3 for MasulloGRH.completeNuclearDF_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:00:43.754423+00:00
-- url     : https://prove2.me/submissions/bf772028-de0e-495b-9aea-7f8ef9f9b110

import Theorems.Thm_NuclearSpaces_completeDF_bounded_series_expansion

set_option autoImplicit false

open MasulloGRH

private theorem dual_bound_of_bounded_series
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (y : ℕ → G) (c : ℕ → ℝ)
    (hy : Bornology.IsVonNBounded ℂ (Set.range y))
    (hc : ∀ n, 0 ≤ c n) (hcs : Summable c)
    (x : G) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ c n)
    (hs : HasSum (fun n => a n • y n) x) (f : StrongDual ℂ G) :
    ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  obtain ⟨M, hM⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hy.image f)
  have hMy (n : ℕ) : ‖f (y n)‖ ≤ M :=
    hM _ ⟨y n, Set.mem_range_self n, rfl⟩
  have hmajor : Summable (fun n => c n * ‖f (y n)‖) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hc n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hMy n) (hc n))
    exact hcs.mul_right M
  apply (hs.mapL f).norm_le_of_bounded hmajor.hasSum
  intro n
  simpa only [map_smul, norm_smul] using
    mul_le_mul_of_nonneg_right (ha n) (norm_nonneg (f (y n)))

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  obtain ⟨y, c, hy, hc, hcs, hrep⟩ :=
    NuclearSpaces.completeDF_bounded_series_expansion G hC hN hB hDF B hBb
  refine ⟨y, c, hy, hc, hcs, ?_⟩
  intro f x hx
  obtain ⟨a, ha, hs⟩ := hrep x hx
  exact dual_bound_of_bounded_series y c hy hc hcs x a ha hs f

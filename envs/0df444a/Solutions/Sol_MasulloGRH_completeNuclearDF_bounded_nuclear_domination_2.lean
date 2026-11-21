-- Prove2me | solution 2 for MasulloGRH.completeNuclearDF_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T23:59:02.470518+00:00
-- url     : https://prove2.me/submissions/adcc3a65-8105-4b6f-b33f-cd63ef463896

import Theorems.Thm_MasulloGRH_bounded_disk_scalar_expansion

set_option autoImplicit false
open MasulloGRH

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
  obtain ⟨y, c, a, hy, hc0, hc, ha, hxSum⟩ :=
    bounded_disk_scalar_expansion G hC hN (.inr ⟨hB, hDF⟩) B hBb
  obtain ⟨ι, hι, p, hp⟩ := hN.1.1
  letI : Nonempty ι := hι
  letI : IsTopologicalAddGroup G := hp.topologicalAddGroup
  letI : ContinuousSMul ℂ G := hp.continuousSMul
  have hyb := hy.isVonNBounded_range ℂ
  refine ⟨y, c, hyb, hc0, hc, ?_⟩
  intro f x hx
  let v : Submodule.span ℂ B := ⟨x, Submodule.subset_span hx⟩
  obtain ⟨M, hM⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).mp (hyb.image f)
  have hs : Summable (fun n => c n * ‖f (y n)‖) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hM (y n) ⟨n, rfl⟩) (hc0 n)) (hc.mul_right M)
  apply (f.hasSum (hxSum v)).norm_le_of_bounded hs.hasSum
  intro n
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (ha n v hx) (norm_nonneg _)

-- Prove2me | solution 1 for MasulloGRH.strongDual_nuclear_of_complete_nuclear_DF
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:41:22.887822+00:00
-- url     : https://prove2.me/submissions/6057c69b-aa7e-4c1e-86b5-75cae60a5323

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_strongDual_evaluation_seminorm
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Theorems.Thm_MasulloGRH_completeNuclearDF_bounded_nuclear_domination

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G)) :
    IsNuclear (StrongDual ℂ G) := by
  refine nuclear_of_quasinuclear_domination _ (strongDual_isHLCS G hN.1) ?_
  intro p hp
  obtain ⟨B, C, hBb, hC0, hpB⟩ := strongDual_seminorm_le_polar G hN.1 p hp
  obtain ⟨y, c, hy, hc0, hcs, hdom⟩ :=
    completeNuclearDF_bounded_nuclear_domination G hC hN hB hDF B hBb
  obtain ⟨q, φ, hq, hφ, hqy⟩ := strongDual_evaluation_seminorm G hN.1 y hy
  refine ⟨q, φ, fun n => C * c n, hq, fun n => mul_nonneg hC0 (hc0 n), hcs.mul_left C,
    fun n f => by rw [hφ]; exact hqy n f, fun f => ?_⟩
  have hr : 0 ≤ ∑' n, c n * ‖f (y n)‖ := tsum_nonneg fun n => mul_nonneg (hc0 n) (norm_nonneg _)
  have := hpB f _ hr (fun x hx => hdom f x hx)
  calc p f ≤ C * ∑' n, c n * ‖f (y n)‖ := this
    _ = ∑' n, C * c n * ‖φ n f‖ := by
      rw [← tsum_mul_left]; congr 1; funext n; rw [hφ, mul_assoc]

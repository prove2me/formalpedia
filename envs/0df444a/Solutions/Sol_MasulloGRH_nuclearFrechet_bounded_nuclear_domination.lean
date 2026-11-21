-- Prove2me | solution 1 for MasulloGRH.nuclearFrechet_bounded_nuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:31:28.20318+00:00
-- url     : https://prove2.me/submissions/52544a9e-42f6-428a-ae10-feb390758112

import Theorems.Thm_MasulloGRH_strongDual_quasinuclear_domination
import Theorems.Thm_MasulloGRH_strongDual_seminorm_of_bounded
import Theorems.Thm_MasulloGRH_nuclearFrechet_strongBidual_bounded_repr

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → E) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  obtain ⟨p, hp, hpB⟩ := strongDual_seminorm_of_bounded E hN.1 B hB
  obtain ⟨q, F, c, hq, hc0, hcs, hFq, hpF⟩ := strongDual_quasinuclear_domination E hE hN p hp
  obtain ⟨D, hD, hrepr⟩ := nuclearFrechet_strongBidual_bounded_repr E hE hN q hq
  have h : ∀ n, ∃ y ∈ D, ∀ f : StrongDual ℂ E, F n f = f y := fun n => hrepr (F n) (hFq n)
  choose y hyD hy using h
  refine ⟨y, c, hD.subset (Set.range_subset_iff.2 hyD), hc0, hcs, ?_⟩
  intro f x hx
  calc ‖f x‖ ≤ p f := hpB f x hx
    _ ≤ ∑' n, c n * ‖F n f‖ := hpF f
    _ = ∑' n, c n * ‖f (y n)‖ := by simp_rw [hy]

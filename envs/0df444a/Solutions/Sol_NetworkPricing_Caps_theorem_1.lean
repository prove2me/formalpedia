-- Prove2me | solution 1 for NetworkPricing.Caps.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:03:47.350727+00:00
-- url     : https://prove2.me/submissions/da5775ee-b13e-4b25-8855-5205d7989e8f

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model
import Theorems.Thm_NetworkPricing_Caps_strong_nash_of_le_marginal
import Theorems.Thm_NetworkPricing_Caps_nash_unique_of_le_marginal

open KellyStochasticNetworks NetworkPricing.Caps

theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    I.IsCapEquilibrium flow tbar ∧ I.IsStrongCapEquilibrium flow tbar := by
  have hS := NetworkPricing.Caps.strong_nash_of_le_marginal I hI hU flow hflow tbar fstar hopt hcap
  have hN := NetworkPricing.Caps.nash_unique_of_le_marginal I hI hU flow hflow tbar fstar hopt hcap
  have h0 : 0 ≤ tbar := hopt.1
  have hcaps : InCaps tbar tbar := ⟨h0, le_rfl⟩
  -- unilateral deviations inside the caps
  have hupd : ∀ t : Fin J → ℝ, InCaps tbar t → ∀ e s, 0 ≤ s → s ≤ tbar e →
      InCaps tbar (Function.update t e s) := by
    intro t ht e s hs0 hs1
    refine ⟨fun i => ?_, fun i => ?_⟩
    · show (0:ℝ) ≤ Function.update t e s i
      by_cases h : i = e
      · rw [h, Function.update_self]; exact hs0
      · rw [Function.update_of_ne h]; exact ht.1 i
    · show Function.update t e s i ≤ tbar i
      by_cases h : i = e
      · rw [h, Function.update_self]; exact hs1
      · rw [Function.update_of_ne h]; exact ht.2 i
  -- a strong Nash equilibrium of the capped game is a Nash equilibrium
  have hSN : ∀ t, I.IsCappedStrongNash flow tbar t → I.IsCappedNash flow tbar t := by
    intro t ⟨ht, hst⟩
    refine ⟨ht, fun e s hs0 hs1 => ?_⟩
    by_contra hlt
    push Not at hlt
    refine hst {e} (Finset.singleton_nonempty e) (Function.update t e s) (hupd t ht e s hs0 hs1)
      (fun i hi => Function.update_of_ne (by simpa using hi) _ _) ?_
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi]; exact hlt
  have hStrong : I.IsCappedStrongNash flow tbar tbar := by
    refine ⟨hcaps, fun D hD t' ht' hoff hall => ?_⟩
    obtain ⟨e0, he0⟩ := hD
    exact hS D t' ht' hoff ⟨fun e he => (hall e he).le, e0, he0, hall e0 he0⟩
  refine ⟨⟨h0, hSN tbar hStrong, hN⟩, ⟨h0, hStrong, fun t ht => hN t (hSN t ht)⟩⟩

-- Prove2me | solution 1 for GlobalTheory.subst_eq_of_coeff_eq_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:35.525814+00:00
-- url     : https://prove2.me/submissions/a54f3e93-d322-40ce-997d-6bf84835bf28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (C : Type) [Field C] (σ τ : Type) [Fintype σ] [Fintype τ] (P : σ → Prop) (f : σ → MvPowerSeries τ C) (F F' : MvPowerSeries σ C), (∀ w, MvPowerSeries.constantCoeff (f w) = 0) → (∀ w, ¬ P w → f w = 0) → (∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, P w) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F') → MvPowerSeries.subst f F = MvPowerSeries.subst f F' := by
  intro C _ σ τ _ _ P f F F' h0 hk hF
  have hs : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  ext ν
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun μ => ?_
  by_cases h : ∀ w ∈ μ.support, P w
  · rw [hF μ h]
  · push Not at h
    obtain ⟨w, hw, hP⟩ := h
    have hz : (μ.prod fun s e => f s ^ e) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show f w ^ μ w = 0
      rw [hk w hP]
      exact zero_pow (Finsupp.mem_support_iff.mp hw)
    rw [hz]
    simp
end GlobalTheory

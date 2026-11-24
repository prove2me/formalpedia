-- Prove2me | solution 1 for GlobalTheory.ConductorAdicCompletion.exists_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:56.578155+00:00
-- url     : https://prove2.me/submissions/305a951f-9602-4749-acd6-46db6d1ed96d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Theorems.Thm_GlobalTheory_ConductorAdicCompletion_exists_ball_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConductorAdicCompletion
namespace GlobalTheory.ConductorAdicCompletion
theorem _root_.solution {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t₀ : WithZero (Multiplicative ℤ)), fun m hm => by
      have h1 : WithZero.exp m < Valued.v t₀ := lt_of_not_ge fun h => ht₀ (hm _ h)
      exact ((WithZero.lt_log_iff_exp_lt (ne_zero_of_lt h1)).mpr h1).le⟩
    (exists_ball_trivial ψ hc)
  refine ⟨n, fun t => ⟨fun h => ?_, fun h s hs => ?_⟩⟩
  · by_contra hlt
    have h1 : WithZero.exp n < Valued.v t := lt_of_not_ge hlt
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := ne_zero_of_lt h1
    have ht : t ≠ 0 := fun h0 => hv0 (by simp [h0])
    have h2 := (WithZero.lt_log_iff_exp_lt hv0).mpr h1
    have h3 := hmax (WithZero.log (Valued.v t : WithZero (Multiplicative ℤ))) (fun x hx => by
      rw [WithZero.exp_log hv0] at hx
      have h4 := h (x / t) (by
        rw [map_div₀]
        exact div_le_one_of_le₀ hx zero_le)
      rwa [mul_div_cancel₀ _ ht] at h4)
    omega
  · apply hn
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans h
end GlobalTheory.ConductorAdicCompletion

-- Prove2me | solution 1 for GlobalTheory.JR.exists_short_dot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:55.764535+00:00
-- url     : https://prove2.me/submissions/3afb5937-19e4-4d11-9dc1-36b95d6ba151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution {F : Type} [NormedField F] {r : ℕ} (x₀ : F) {ε : ℝ} (hε : 0 < ε) (b : Fin r → F)
    (hb : b ∉ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε)) :
    ∃ t : Fin r → F, ‖t‖ < ε ∧ t ⬝ᵥ b = x₀ := by
  have hR : 0 ≤ ‖x₀‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hb' : ‖x₀‖ / ε < ‖b‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
  obtain ⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by
    by_contra hcon
    push Not at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')
  have hbi : b i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hi
    exact absurd hi (not_lt.2 hR)
  refine ⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hε] at hi
      calc ‖x₀‖ < ‖b j‖ * ε := hi
        _ = ε * ‖b j‖ := mul_comm _ _
    · rw [Pi.single_eq_of_ne hj, norm_zero]
      exact hε
  · rw [single_dotProduct, div_mul_cancel₀ _ hbi]
end GlobalTheory.JR

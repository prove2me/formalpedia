-- Prove2me | solution 1 for GlobalTheory.setIntegral_le_of_expanding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:41.308802+00:00
-- url     : https://prove2.me/submissions/7f1db0a0-cc98-405e-81b0-9bb9a55bb2a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralLeOfExpanding
import Theorems.Thm_GlobalTheory_volume_le_mul_volume_image_of_expanding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ)
    (hA : IsCompact A) (hQ : IsCompact Q) (hK : 0 ≤ K) (c₁ : Continuous h₁) (c₂ : Continuous h₂)
    (n₁ : ∀ t, 0 ≤ h₁ t) (n₂ : ∀ t, 0 ≤ h₂ t) (hm : ∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t))
    (hf : ∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  have i₁ : IntegrableOn h₁ A volume := c₁.continuousOn.integrableOn_compact hA
  have i₂ : IntegrableOn h₂ Q volume := c₂.continuousOn.integrableOn_compact hQ
  have hKN : 0 ≤ K ^ N := pow_nonneg hK N
  have hI₂ : 0 ≤ ∫ t in Q, h₂ t := integral_nonneg n₂
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKN hI₂), ENNReal.ofReal_mul hKN,
    ofReal_integral_eq_lintegral_ofReal i₁ (Filter.Eventually.of_forall n₁),
    ofReal_integral_eq_lintegral_ofReal i₂ (Filter.Eventually.of_forall n₂),
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₁) c₁.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₂) c₂.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  have m₁ : MeasurableSet {a | r < h₁ a} := measurableSet_lt measurable_const c₁.measurable
  have m₂ : MeasurableSet {a | r < h₂ a} := measurableSet_lt measurable_const c₂.measurable
  rw [Measure.restrict_apply m₁, Measure.restrict_apply m₂]
  refine (volume_le_mul_volume_image_of_expanding N _ K f hK
    (fun t ht t' ht' => hf t ht.2 t' ht'.2)).trans ?_
  gcongr
  rintro _ ⟨a, ⟨ha, haA⟩, rfl⟩
  exact ⟨lt_of_lt_of_le ha (hm a haA).2, (hm a haA).1⟩
end GlobalTheory

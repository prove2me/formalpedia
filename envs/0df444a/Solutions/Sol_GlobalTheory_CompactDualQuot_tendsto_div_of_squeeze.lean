-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:07.845829+00:00
-- url     : https://prove2.me/submissions/78254995-1faf-4753-bbf4-c36bf2448334

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompactDualQuot
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal
variable {P Q P' Q' : ℕ}
namespace GlobalTheory.CompactDualQuot
theorem _root_.solution {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by
  have key : ∀ t : ℝ, 0 < t →
      Tendsto (fun r => F (t * r) / V r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ n) * c)) := by
    intro t ht
    have h1 : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos ht hr
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) (hF.comp h1)
      (Or.inr ENNReal.ofReal_ne_top)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h0 : ENNReal.ofReal (t ^ n) ≠ 0 := by simpa using pow_pos ht n
    simp only [Function.comp, hV t r ht hr]
    rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have lim : ∀ u : ℝ → ℝ, ContinuousAt u 1 → u 1 = 1 →
      Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n) * c) (𝓝[>] 1) (𝓝 c) := by
    intro u hu h1
    have h3 : Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n)) (𝓝 1) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.continuousAt.comp (hu.pow n)).tendsto
      simp only [Function.comp, Pi.pow_apply, h1, one_pow, ENNReal.ofReal_one] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := c) h3 (Or.inr hc)
    rw [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t⁻¹) (continuousAt_inv₀ one_ne_zero) inv_one).eventually
      (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t⁻¹ (inv_pos.2 (by linarith))).eventually (lt_mem_nhds h1), hA t ht]
      with r h3 h4 using h3.trans_le (ENNReal.div_le_div_right h4.1 _)
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t) continuousAt_id rfl).eventually
      (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t (by linarith)).eventually (gt_mem_nhds h1), hA t ht]
      with r h3 h4 using (ENNReal.div_le_div_right h4.2 _).trans_lt h3
end GlobalTheory.CompactDualQuot

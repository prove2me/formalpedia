-- Prove2me | solution 1 for GlobalTheory.exists_pos_integral_comp_equiv_haar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:32.984867+00:00
-- url     : https://prove2.me/submissions/2f86ecc6-0c44-4fe8-8810-cc5fe5fcb9f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FourierInversionHaarSymmForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory FourierTransform
open GlobalTheory
open MeasureTheory FourierTransform
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : V ≃L[ℝ] E) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ (∀ g : E → ℂ, ∫ x, g (T x) ∂μ = (a : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (T x)) μ ↔ Integrable g := by
  let e : V ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  set c := (μ.map e).addHaarScalarFactor volume
  have hpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hpos, fun g => ?_, fun g => ?_⟩
  · change ∫ x, g (e x) ∂μ = _
    rw [← integral_map_equiv e, hmap, integral_smul_nnreal_measure]
    simp [NNReal.smul_def, Complex.real_smul]
  · change Integrable (g ∘ e) μ ↔ _
    rw [← integrable_map_equiv e, hmap,
      show c • (volume : Measure E) = (c : ENNReal) • volume from rfl, integrable_smul_measure]
    · simpa using hpos.ne'
    · simp
end _root_.GlobalTheory
end GlobalTheory

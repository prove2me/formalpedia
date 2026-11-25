-- Prove2me | solution 1 for GlobalTheory.TensorLat.setAverage_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:28.029362+00:00
-- url     : https://prove2.me/submissions/d14fda4a-9551-4aff-a295-8857364181dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
namespace GlobalTheory.TensorLat
theorem _root_.solution {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure W) [ν.IsAddHaarMeasure]
    (e : V ≃L[ℝ] W) (s : Set W) (f : W → F) :
    ⨍ w in s, f w ∂ν = ⨍ v in e ⁻¹' s, f (e v) ∂μ := by
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have key : ∀ t : Set W, ⨍ v in e ⁻¹' t, f (e v) ∂μ = ⨍ w in t, f w ∂(μ.map e) := by
    intro t
    rw [average_eq, average_eq, hme.restrict_map μ t, hme.integral_map]
    congr 2
    rw [measureReal_def, measureReal_def, Measure.map_apply hme.measurable MeasurableSet.univ,
      Set.preimage_univ]
  rw [key s]
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map e) ν
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν
  set c := Measure.addHaarScalarFactor (μ.map e) ν
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [hc, average_eq, average_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply, NNReal.smul_def, smul_smul]
  congr 1
  rw [mul_inv, mul_comm (c : ℝ)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
end GlobalTheory.TensorLat

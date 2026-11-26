-- Prove2me | solution 1 for Kyprianou.Ch04.markedFullPredictableMeasureExists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:31:42.06888+00:00
-- url     : https://prove2.me/submissions/e85ac4f5-f770-40c5-a60d-383aab1c3b6e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
open MeasureTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full predictable expected clock measure is a pushforward of intensity times probability. -/
theorem solution
    {Omega : Type} [mO : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal mO) (t : NNReal) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
    ∃ mu : @Measure ((NNReal × Omega) × ℝ) m,
      ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable[m] f →
        (∫⁻ a, f a ∂mu) =
          ∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
            f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P := by
  let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
  let S := (referenceIntensity nu).restrict (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ)
  letI : SigmaFinite (referenceIntensity nu) := by
    unfold referenceIntensity
    infer_instance
  letI : SigmaFinite S := by dsimp [S]; infer_instance
  let Q := P.prod S
  let e : Omega × (ℝ × ℝ) → ((NNReal × Omega) × ℝ) :=
    fun z => ((z.2.1.toNNReal,z.1),z.2.2)
  let mAmb := ((inferInstance : MeasurableSpace NNReal).prod mO).prod
    (inferInstance : MeasurableSpace ℝ)
  have he : Measurable[inferInstance,mAmb] e := by
    dsimp only [e,mAmb]
    exact ((measurable_snd.fst.real_toNNReal).prodMk measurable_fst).prodMk measurable_snd.snd
  have hep : Measurable[inferInstance,m] e :=
    he.mono le_rfl (Kyprianou.Ch04.markedPredictableLeAmbientProduct (E := ℝ) F)
  letI : MeasurableSpace ((NNReal × Omega) × ℝ) := m
  let mu : @Measure ((NNReal × Omega) × ℝ) m := @Measure.map _ _ _ m e Q
  refine ⟨mu,fun f hf => ?_⟩
  change (∫⁻ a, f a ∂mu) = _
  rw [show mu = @Measure.map _ _ _ m e Q from rfl, lintegral_map hf hep]
  change (∫⁻ z, (f ∘ e) z ∂(P.prod S)) = _
  rw [lintegral_prod _ (hf.comp hep).aemeasurable]
  rfl

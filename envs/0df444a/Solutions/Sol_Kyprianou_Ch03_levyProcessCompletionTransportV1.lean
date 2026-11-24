-- Prove2me | solution 1 for Kyprianou.Ch03.levyProcessCompletionTransportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:56:00.620024+00:00
-- url     : https://prove2.me/submissions/7b07b5e7-754f-44f6-a5f3-90f9f9cb105d

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hx : ∀ t, Measurable (X t)) :
    IsLevyProcess (fun t (w : NullMeasurableSpace Ω P) => X t w) P.completion := by
  let Y : NNReal → NullMeasurableSpace Ω P → ℝ := fun t w => X t w
  have hy : ∀ t, Measurable (Y t) := fun t _ h => ((hx t) h).nullMeasurableSet
  have hm : ∀ f : Ω → ℝ, Measurable f →
      P.completion.map (fun w : NullMeasurableSpace Ω P => f w) = P.map f := by
    intro f hf
    have hfc : Measurable (fun w : NullMeasurableSpace Ω P => f w) :=
      fun _ h => (hf h).nullMeasurableSet
    ext A hA
    rw [Measure.map_apply hfc hA, Measure.map_apply hf hA]
    rfl
  change IsLevyProcess Y P.completion
  refine ⟨hX.start_zero, ?_, ?_, hX.cadlag_ae⟩
  · intro n ts hts
    rw [iIndepFun_iff]
    intro I A hA
    exact (iIndepFun_iff _ _ _).mp (hX.indep_increments n ts hts) I hA
  · intro s t
    have h := hX.stationary_increments s t
    refine ⟨((hy (s+t)).sub (hy s)).aemeasurable,
      ((hy t).sub (hy 0)).aemeasurable, ?_⟩
    change P.completion.map (fun w : NullMeasurableSpace Ω P =>
        increment X s (s+t) w) =
      P.completion.map (fun w : NullMeasurableSpace Ω P => increment X 0 t w)
    calc
      _ = P.map (increment X s (s+t)) :=
        hm (increment X s (s+t)) ((hx (s+t)).sub (hx s))
      _ = P.map (increment X 0 t) := h.map_eq
      _ = _ := (hm (increment X 0 t) ((hx t).sub (hx 0))).symm

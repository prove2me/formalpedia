-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PRMIndistinguishableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:15:40.405369+00:00
-- url     : https://prove2.me/submissions/11cec2f0-a1c0-4ca3-9114-b74b6e845bb2

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable almost-sure modification of a Poisson random measure preserves its law. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (Q : Ω → Measure (ℝ × ℝ))
    (hQ : ∀ B : Set (ℝ × ℝ), MeasurableSet B → Measurable (fun w => Q w B))
    (hEq : ∀ᵐ w ∂P, N.N w = Q w) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν, N'.N = Q := by
  have he (B : Set (ℝ × ℝ)) : (fun w => N.N w B) =ᵐ[P] (fun w => Q w B) :=
    hEq.mono fun w hw => congrArg (fun m : Measure (ℝ × ℝ) => m B) hw
  refine ⟨⟨Q,fun h => hQ _ h,?_,?_,?_,?_,?_⟩,rfl⟩
  · intro B hB hfin
    filter_upwards [N.integer_valued hB hfin, he B] with w hw h
    rw [← h]
    exact hw
  · intro B hB hinf
    filter_upwards [N.infinite_at_infinite_intensity hB hinf,he B] with w hw h
    exact h.symm.trans hw
  · intro B hB hfin
    rw [← Measure.map_congr (he B)]
    exact N.poisson_law hB hfin
  · intro ι hι B hB hd
    exact (N.independent_disjoint B hB hd).congr (fun i => he (B i))
  · intro s t hs hst A hA hfin
    let C := {B : Set (ℝ × ℝ) // B ⊆ Iic s ×ˢ univ ∧ MeasurableSet B}
    let f (w : Ω) (B : C) := N.N w B.1
    let g (w : Ω) (B : C) := Q w B.1
    have hcom (R : Ω → Measure (ℝ × ℝ)) :
        MeasurableSpace.comap (fun w (B : C) => R w B.1) inferInstance =
          ⨆ B ∈ {B : Set (ℝ × ℝ) | B ⊆ Iic s ×ˢ univ ∧ MeasurableSet B},
            MeasurableSpace.comap (fun w => R w B) inferInstance := by
      simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp,Function.comp_def]
      exact iSup_subtype
    have h : IndepFun f (fun w => N.N w (Ioc s t ×ˢ A)) P := by
      change Indep (MeasurableSpace.comap f inferInstance) _ P
      rw [show MeasurableSpace.comap f inferInstance = _ from hcom N.N]
      exact N.joint_past_future_independent hs hst hA hfin
    have hfg : f =ᵐ[P] g := hEq.mono fun w hw => funext fun B => congrArg
      (fun m : Measure (ℝ × ℝ) => m B.1) hw
    have h' := h.congr hfg (he (Ioc s t ×ˢ A))
    change Indep (MeasurableSpace.comap g inferInstance) _ P at h'
    rw [show MeasurableSpace.comap g inferInstance = _ from hcom Q] at h'
    exact h'

-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.indepFun_past_compensated_box
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:56:19.9851+00:00
-- url     : https://prove2.me/submissions/c5677a29-a61a-4864-879c-d175b3b00393

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A future compensated Poisson box is independent of every past-measurable weight. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    {E : Type} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {f : Ω → ℝ}
    (hf : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) f) :
    IndepFun f (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) P := by
  have hf_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a :=
    hf.measurable.comap_le
  have hÑ_comap_le :
      MeasurableSpace.comap (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc a b ×ˢ A)) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  rw [IndepFun_iff]
  intro u v hu hv
  have h_indep := hℱ.indep ha hab hA hAf
  rw [Indep_iff] at h_indep
  exact h_indep u v (hf_comap_le u hu) (hÑ_comap_le v hv)

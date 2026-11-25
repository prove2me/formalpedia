-- Prove2me | solution 1 for Kyprianou.Ch04.pastWeightIndependentFutureCompensatedBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:01:28.363802+00:00
-- url     : https://prove2.me/submissions/0bbdb19b-066d-4cd9-9a38-d01f8753a876

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Future compensated-box counts are independent of scalar weights measurable in the past. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set Real) (hB : MeasurableSet B)
    (f : Omega → Real)
    (hf : @StronglyMeasurable Omega Real _ (F u) f) :
    IndepFun f (fun omega => N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) P := by
  have hf_comap_le : MeasurableSpace.comap f inferInstance ≤ F u :=
    hf.measurable.comap_le
  have hÑ_comap_le :
      MeasurableSpace.comap (fun omega =>
        N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) inferInstance ≤
      MeasurableSpace.comap (fun omega =>
        N.N omega (Set.Ioc (u : Real) (t : Real) ×ˢ B)) inferInstance := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := hW
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (referenceIntensity nu (Set.Ioc (u : Real) (t : Real) ×ˢ B)).toReal) ⁻¹' V, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hV
    · ext omega; rfl
  rw [IndepFun_iff]
  intro U V hU hV
  have h_indep := (hFuture u t B hut hB).symm
  rw [Indep_iff] at h_indep
  exact h_indep U V (hf_comap_le U hU) (hÑ_comap_le V hV)

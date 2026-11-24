-- Prove2me | solution 1 for Kyprianou.Ch03.rawRightGermIndepFuturePathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:45:42.476413+00:00
-- url     : https://prove2.me/submissions/4736995e-af5b-4e7b-ac92-378e0df78d3f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_levyCommonMeasurableVersionV1
import Theorems.Thm_Kyprianou_Ch03_rawRightGermRestrictedVersionLawV1
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    Indep (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) (MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance) P := by
  obtain ⟨Y, hY, hMeas, hEq⟩ := Kyprianou.Ch03.levyCommonMeasurableVersionV1 P X hX
  let U (w : Omega) (u : NNReal) := X (t+u) w - X t w
  let V (w : Omega) (u : NNReal) := Y (t+u) w - Y t w
  have hUV : U =ᵐ[P] V := by
    filter_upwards [hEq] with w hw
    funext u
    simp [U, V, hw]
  have hV : @Measurable Omega (NNReal → ℝ) mΩ inferInstance V :=
    measurable_pi_iff.mpr fun u => (hMeas (t + u)).sub (hMeas t)
  have hLaw (A : Set Omega) (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A) :=
    Kyprianou.Ch03.rawRightGermRestrictedVersionLawV1 P X Y hY hMeas hEq t A hA
  have hbase : Measure.map V P = Measure.map (fun w u => Y u w) P := by
    simpa using hLaw Set.univ (@MeasurableSet.univ Omega (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s))
  apply (Indep_iff (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) (MeasurableSpace.comap U inferInstance) P).mpr
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := hB
  have hpre : (U ⁻¹' C : Set Omega) =ᵐ[P] (V ⁻¹' C : Set Omega) := by
    filter_upwards [hUV] with w hw
    change (U w ∈ C) = (V w ∈ C)
    rw [hw]
  have hinter : (A ∩ (U ⁻¹' C) : Set Omega) =ᵐ[P]
      (A ∩ (V ⁻¹' C) : Set Omega) := by
    filter_upwards [hUV] with w hw
    change (w ∈ A ∧ U w ∈ C) = (w ∈ A ∧ V w ∈ C)
    rw [hw]
  rw [measure_congr hinter, measure_congr hpre]
  have he := congrArg (fun μ : Measure (NNReal → ℝ) => μ C) (hLaw A hA)
  rw [← hbase, Measure.map_apply hV hC, Measure.smul_apply, Measure.map_apply hV hC,
    Measure.restrict_apply (hV hC), Set.inter_comm, smul_eq_mul] at he
  exact he

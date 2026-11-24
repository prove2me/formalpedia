-- Prove2me | solution 2 for Kyprianou.Ch03.rawRightGermIndepFuturePathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:57:22.02424+00:00
-- url     : https://prove2.me/submissions/cf37c645-99f7-471f-a1dd-2b1bbf8d3e2f

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
  have hV : Measurable V := measurable_pi_iff.mpr fun u => (hMeas _).sub (hMeas _)
  have hLaw (A : Set Omega) (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A) :=
    @Kyprianou.Ch03.rawRightGermRestrictedVersionLawV1 Omega mΩ P inferInstance X Y hY hMeas hEq t A hA
  have hbase : Measure.map V P = Measure.map (fun w u => Y u w) P := by
    simpa using hLaw Set.univ (@MeasurableSet.univ Omega
      (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s))
  have hUA : AEMeasurable U P := hV.aemeasurable.congr hUV.symm
  apply (Indep_iff (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s)
    (MeasurableSpace.comap U inferInstance) P).mpr
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := hB
  have hUR : AEMeasurable U (P.restrict A) :=
    hV.aemeasurable.congr (ae_restrict_of_ae hUV.symm)
  have hLU : Measure.map U (P.restrict A) = P A • Measure.map U P := by
    calc
      _ = Measure.map V (P.restrict A) := Measure.map_congr (ae_restrict_of_ae hUV)
      _ = P A • Measure.map (fun w u => Y u w) P := hLaw A hA
      _ = _ := by rw [← hbase, Measure.map_congr hUV]
  calc
    P (A ∩ U ⁻¹' C) = (P.restrict A) (U ⁻¹' C) := by
      rw [Measure.restrict_apply₀ (hUR.nullMeasurableSet_preimage hC), Set.inter_comm]
    _ = Measure.map U (P.restrict A) C := (Measure.map_apply_of_aemeasurable hUR hC).symm
    _ = P A * P (U ⁻¹' C) := by
      rw [hLU, Measure.smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable hUA hC]

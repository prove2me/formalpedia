-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RawNaturalRestrictedLawV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:34:12.321603+00:00
-- url     : https://prove2.me/submissions/424af0fc-56dc-4ecc-8dc3-7197e2f451cd

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_monotone
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_eq_natFiltr
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedFDDV1
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t))
    (s : NNReal) (B : Set Ω) (hB : MeasurableSet[Kyprianou.Ch01.naturalSigma X s] B) :
    Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
      P B • Measure.map (fun w u => X u w) P := by
  let F : Filtration NNReal (inferInstance : MeasurableSpace Ω) :=
    ⟨Kyprianou.Ch01.naturalSigma X,
      fun _ _ h => Kyprianou.Ch01.naturalSigma_monotone X h,
      fun t => by
        rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr]
        exact iSup_le fun u => iSup_le fun _ => (hm u).comap_le⟩
  have ha : ∀ t, Measurable[F t] (X t) := by
    intro t
    apply (comap_measurable (X t)).mono _ le_rfl
    change MeasurableSpace.comap (X t) inferInstance ≤ Kyprianou.Ch01.naturalSigma X t
    rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr]
    exact le_iSup₂_of_le t le_rfl le_rfl
  have hOne : ∀ (r t : NNReal), r ≤ t → ∀ A : Set Ω, MeasurableSet[F r] A →
      ∀ C : Set ℝ, MeasurableSet C →
      P (A ∩ {w | X t w - X r w ∈ C}) = P A * P {w | X t w - X r w ∈ C} := by
    intro r t hrt A hA C hC
    exact (Indep_iff _ _ P).mp
      (Kyprianou.Ch01.levyIncrement_indep_naturalSigma P X hX hm r t hrt).symm
      A ((fun w => X t w - X r w) ⁻¹' C) hA ((comap_measurable _) hC)
  apply AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
    (fun w u => X (s+u) w-X s w) (fun w u => X u w)
    (measurable_pi_iff.mpr fun u => (hm _).sub (hm _))
    (measurable_pi_iff.mpr hm) (P B) (measure_ne_top _ _)
  exact Kyprianou.Ch03.strongMarkovDeterministicRestrictedFDDV1 P F X hX ha hOne s B hB

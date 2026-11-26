-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49NaturalFiltrationV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:38:52.571458+00:00
-- url     : https://prove2.me/submissions/c132b721-50cd-4d2e-8612-b70dc143e0b2

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_monotone
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_eq_natFiltr
import Theorems.Thm_Kyprianou_Ch04_exercise49RawNaturalRestrictedLawV6
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
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t) :
    ∃ F : Filtration NNReal (inferInstance : MeasurableSpace Ω),
      (∀ t, Measurable[F t] (X t)) ∧
      ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
        Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
          P B • Measure.map (fun w u => X u w) P := by
  let F : Filtration NNReal (inferInstance : MeasurableSpace Ω) :=
    ⟨Kyprianou.Ch01.naturalSigma X,
      fun _ _ h => Kyprianou.Ch01.naturalSigma_monotone X h,
      fun t => by
        rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr]
        exact iSup_le fun u => iSup_le fun _ => (hm u).comap_le⟩
  refine ⟨F,?_,fun s B hB => Kyprianou.Ch04.exercise49RawNaturalRestrictedLawV6 P X hX hm s B hB⟩
  intro t
  apply (comap_measurable (X t)).mono _ le_rfl
  change MeasurableSpace.comap (X t) inferInstance ≤ Kyprianou.Ch01.naturalSigma X t
  rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr]
  exact le_iSup₂_of_le t le_rfl le_rfl

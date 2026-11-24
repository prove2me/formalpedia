-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:53:57.791604+00:00
-- url     : https://prove2.me/submissions/362e95a2-479d-4a3c-868e-44bf4e5f6a5d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCommonCoordinateLimitMeasV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteVectorLawLimitV1
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : ℕ → Omega → (NNReal → Real)) (Z : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hMeas : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, Measure.map (Y n) mu = nu)
    (hLimit : ∀ᵐ w ∂mu, ∀ u : NNReal,
      Tendsto (fun n => Y n w u) atTop (nhds (Z w u))) :
    AEMeasurable Z mu ∧ Measure.map Z mu = nu := by
  classical
  have hZ := strongMarkovCommonCoordinateLimitMeasV1 mu Y Z hMeas hLimit
  refine ⟨hZ, ?_⟩
  let W := hZ.mk Z
  have hW : Measurable W := hZ.measurable_mk
  have he : Z =ᵐ[mu] W := hZ.ae_eq_mk
  rw [Measure.map_congr he, ← hLaw 0]
  have hh : Measure.map W mu = (1 : ℝ≥0∞) • Measure.map (Y 0) mu := by
    apply AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
      W (Y 0) hW (hMeas 0) 1 (measure_ne_top _ _)
    intro J
    simp only [one_smul]
    let proj : (NNReal → ℝ) → (J → ℝ) := fun y j => y j
    have hp : Measurable proj := measurable_pi_iff.mpr (fun j => measurable_pi_apply (j : NNReal))
    change Measure.map (proj ∘ W) mu = Measure.map (proj ∘ Y 0) mu
    apply strongMarkovFiniteVectorLawLimitV1 mu (fun n => proj ∘ Y n) (proj ∘ W)
      (fun n => hp.comp (hMeas n)) (hp.comp hW)
    · intro n
      rw [← Measure.map_map hp (hMeas n), ← Measure.map_map hp (hMeas 0), hLaw n, hLaw 0]
    · filter_upwards [hLimit, he] with w hw hEq
      apply tendsto_pi_nhds.mpr
      intro j
      simpa [Function.comp_def, proj, ← hEq] using hw (j : NNReal)
  simpa using hh

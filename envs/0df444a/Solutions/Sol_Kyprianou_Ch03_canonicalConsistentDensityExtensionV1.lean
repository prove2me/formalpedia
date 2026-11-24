-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalConsistentDensityExtensionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:55:30.859666+00:00
-- url     : https://prove2.me/submissions/4b83994d-efee-4a22-9069-536b9bd35598

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_canonicalDensityProjectiveProductV1
import Theorems.Thm_Kyprianou_Ch03_canonicalDensityProjectiveZeroTransferV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (Z : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hNonneg : ∀ t w, 0 ≤ Z t w)
    (hInt : ∀ t, Integrable (Z t) P)
    (hUnit : ∀ t, (∫ w, Z t w ∂P) = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (Z t) w ∂P) = (∫ w, A.indicator (Z s) w ∂P))
 :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
        Q A = ENNReal.ofReal (∫ w, A.indicator (Z t) w ∂P) := by
  obtain ⟨μ, hμ, hProj⟩ :=
    Kyprianou.Ch03.canonicalDensityProjectiveProductV1 P X hCoordinate Z hNonneg hInt hUnit hCons
  letI := hμ
  exact Kyprianou.Ch03.canonicalDensityProjectiveZeroTransferV1
    P X hCoordinate Z hNonneg hInt hUnit hCons μ hProj

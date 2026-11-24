-- Prove2me | solution 2 for Kyprianou.Ch03.spectrallyNegativeLevyCadlagModification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:04:02.891051+00:00
-- url     : https://prove2.me/submissions/4934b73c-becf-429a-a067-71e3f8cb66a9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_allpath_cadlag_version
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top
import Theorems.Thm_Kyprianou_Ch03_negativeLevyNoPositiveJumpsAEV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyIndistinguishableIncrementsV1
import Theorems.Thm_Kyprianou_Ch03_negativeLevyLaplaceFromTripleV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∃ (Y : NNReal → Omega → ℝ)
      (L : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega) ∧
      L.X = Y ∧ L.ν = T.levyMeasure ∧
      L.σ ^ 2 = (T.gaussianVariance : ℝ) := by
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hj := Kyprianou.Ch03.negativeLevyNoPositiveJumpsAEV1 P X hX T hLK hNegative
  obtain ⟨Y, he, hy, hz, hc, hjy⟩ :=
    Kyprianou.Ch08.StageB.source_result81_allpath_cadlag_version
      Omega P X hm hX.start_zero hX.cadlag_ae hj
  obtain ⟨ha, hi, hs⟩ :=
    Kyprianou.Ch03.completedNaturalLevyIndistinguishableIncrementsV1 P X hX F hNatural Y he hy
  have hl := Kyprianou.Ch03.negativeLevyLaplaceFromTripleV1 P X hX T hLK hNegative Y he hy
  let L : AvramDividend.Classical.SpectrallyNegativeLevy P F :=
    { X := Y
      c := T.drift
      σ := Real.sqrt (T.gaussianVariance : ℝ)
      ν := T.levyMeasure
      isProbability := inferInstance
      σ_nonneg := Real.sqrt_nonneg _
      ν_Ici := hNegative
      ν_integrable := ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top
        T.levyMeasure_isLevyMeasure
      X_zero := fun w => congrFun hz w
      rightCont := fun w t => (hc w t).1
      leftLim := fun w t _ => (hc w t).2
      noPosJumps := hjy
      adapted := ha
      indepIncrements := hi
      stationaryIncrements := hs
      laplace := hl }
  exact ⟨Y, L, he, rfl, rfl, Real.sq_sqrt (by positivity)⟩

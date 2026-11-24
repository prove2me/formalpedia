-- Prove2me | solution 1 for Kyprianou.Ch03.spectrallyNegativeLevyCadlagModification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:01:22.330082+00:00
-- url     : https://prove2.me/submissions/aa9b8d29-522c-4cb2-aa94-21027516d218
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch03_snlCommonAllPathRegularizationV1
import Theorems.Thm_Kyprianou_Ch03_snlCommonVersionFiltrationFieldsV1
import Theorems.Thm_Kyprianou_Ch03_snlTripletRealLaplaceV1
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_lintegral_min_one_sq_lt_top
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch03

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
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
  obtain ⟨Y, hEq, hMeas, hZero, hRight, hLeft, hNeg⟩ :=
    Kyprianou.Ch03.snlCommonAllPathRegularizationV1 P X hX T hLK hNegative
  obtain ⟨hAdapt, hInd, hStat⟩ :=
    Kyprianou.Ch03.snlCommonVersionFiltrationFieldsV1 P F X hX hNatural Y hEq hMeas
  let L : AvramDividend.Classical.SpectrallyNegativeLevy P F :=
    { X := Y
      c := T.drift
      σ := Real.sqrt (T.gaussianVariance : ℝ)
      ν := T.levyMeasure
      isProbability := inferInstance
      σ_nonneg := Real.sqrt_nonneg _
      ν_Ici := hNegative
      ν_integrable := T.lintegral_min_one_sq_lt_top
      X_zero := hZero
      rightCont := hRight
      leftLim := hLeft
      noPosJumps := hNeg
      adapted := hAdapt
      indepIncrements := hInd
      stationaryIncrements := hStat
      laplace := by
        intro t θ hθ
        obtain ⟨hi, hv⟩ :=
          Kyprianou.Ch03.snlTripletRealLaplaceV1 P X hX T hLK hNegative t θ hθ
        have he : (fun w => Real.exp (θ * Y t w)) =ᵐ[P]
            (fun w => Real.exp (θ * X t w)) := by
          filter_upwards [hEq] with w hw
          rw [hw t]
        exact ⟨hi.congr he.symm, (integral_congr_ae he).trans hv⟩ }
  exact ⟨Y, L, hEq, rfl, rfl, Real.sq_sqrt (by positivity)⟩



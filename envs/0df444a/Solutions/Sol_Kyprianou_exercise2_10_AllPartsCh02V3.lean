-- Prove2me | solution 1 for Kyprianou.exercise2_10_AllPartsCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:15:43.921858+00:00
-- url     : https://prove2.me/submissions/b93a9343-a771-49d1-a6e7-03c921b9b398
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_vectorLevyKhintchineMarginalLawsV1
import Theorems.Thm_Kyprianou_Ch02_vectorLevyCadlagFromExponentialMarginalsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ X : ℝ≥0 → Ω → (Fin d → ℝ),
          (∀ᵐ ω ∂P,
            (∀ t : ℝ≥0,
              ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
            ∀ t : ℝ≥0, 0 < t →
              ∃ l : Fin d → ℝ,
                Tendsto (fun s => X s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
          (∀ᵐ ω ∂P, X 0 ω = 0) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            ProbabilityTheory.Indep
              (MeasurableSpace.comap
                (fun ω => X t ω - X s ω) inferInstance)
              (⨆ u ∈ Set.Iic s,
                MeasurableSpace.comap (X u) inferInstance) P) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            P.map (fun ω => X t ω - X s ω) =
              P.map (X (t - s))) ∧
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I *
              (((∑ i : Fin d, θ i * X t ω i : ℝ)) : ℂ)) ∂P =
            Complex.exp (-(t : ℝ) *
              (Complex.I *
                (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
               (((∑ i : Fin d, ∑ j : Fin d,
                   θ i * A i j * θ j : ℝ) / 2) : ℂ) +
               ∫ x, (1 -
                 Complex.exp (Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
                 Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
                   (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)))
      := by
  refine Kyprianou.Ch02.vectorLevyCadlagFromExponentialMarginalsV1 d
    (fun θ => Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
      (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
      ∫ x, (1 - Complex.exp (Complex.I *
        (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
        Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
        (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν) ?_
  exact Kyprianou.Ch02.vectorLevyKhintchineMarginalLawsV1 d hd a A hAsymm hApos ν hzero hLevy

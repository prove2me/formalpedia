-- Prove2me | solution 1 for Kyprianou.Ch02.vectorLevyKhintchineMarginalLawsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:20:32.981314+00:00
-- url     : https://prove2.me/submissions/f8441290-8a23-4362-afc7-e09f443122dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_vectorLevyFiniteCutoffMarginalLawV1
import Theorems.Thm_Kyprianou_Ch02_vectorLevyCutoffCharLimitV1
import Theorems.Thm_Kyprianou_Ch02_vectorCharFunctionPointwiseLimitLawV1
import Mathlib
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
    ∀ t : ℝ≥0, ∃ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ ∧
      ∀ θ : Fin d → ℝ,
        (∫ x, Complex.exp (Complex.I *
          (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂μ) =
          Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)) := by
  intro t
  choose μ hμ hchar using
    (fun n => Kyprianou.Ch02.vectorLevyFiniteCutoffMarginalLawV1
      d hd a A hAsymm hApos ν hzero hLevy t n)
  obtain ⟨hc, hlim⟩ := Kyprianou.Ch02.vectorLevyCutoffCharLimitV1
    d hd a A hAsymm hApos ν hzero hLevy t
  refine Kyprianou.Ch02.vectorCharFunctionPointwiseLimitLawV1 d μ hμ
    (fun θ => Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν))) hc ?_
  intro θ
  convert hlim θ using 1
  funext n
  exact hchar n θ

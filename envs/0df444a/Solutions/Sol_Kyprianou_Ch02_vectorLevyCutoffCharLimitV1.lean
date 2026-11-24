-- Prove2me | solution 1 for Kyprianou.Ch02.vectorLevyCutoffCharLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:32:19.696258+00:00
-- url     : https://prove2.me/submissions/4fea8c57-4ff5-48f1-9a01-13176407ab2c

import Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedIntegralContinuousV1
import Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedCutoffIntegralV1
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
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) (t : ℝ≥0) :
    ContinuousAt (fun θ : Fin d → ℝ => Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν))) 0 ∧
      ∀ θ : Fin d → ℝ,
        Tendsto (fun n : ℕ => Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂(ν.restrict {x | 1 / ((n : ℝ) + 1) ≤
           Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))}))))
          atTop (nhds (Complex.exp (-(t : ℝ) * (Complex.I * (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
       (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ) +
       ∫ x, (1 - Complex.exp (Complex.I *
         (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
         Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
         (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)))) := by
  classical
  let r (x : Fin d → ℝ) := Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))
  let dot (θ x : Fin d → ℝ) := ∑ i : Fin d, θ i * x i
  let F (θ x : Fin d → ℝ) : ℂ :=
    1 - Complex.exp (Complex.I * (dot θ x : ℂ)) +
      Complex.I * (dot θ x : ℂ) * (if r x < 1 then 1 else 0)
  let w (x : Fin d → ℝ) := min 1 (r x ^ 2)
  let D (θ : Fin d → ℝ) : ℂ := Complex.I *
    (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
    (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ)
  let S (n : ℕ) : Set (Fin d → ℝ) := {x | 1 / ((n : ℝ) + 1) ≤ r x}
  have hc : ContinuousAt (fun θ => ∫ x, F θ x ∂ν) 0 :=
    Kyprianou.Ch02.vectorLevyCompensatedIntegralContinuousV1 d ν hLevy
  have hl (θ : Fin d → ℝ) :
      Tendsto (fun n => ∫ x, F θ x ∂(ν.restrict (S n))) atTop
        (nhds (∫ x, F θ x ∂ν)) :=
    Kyprianou.Ch02.vectorLevyCompensatedCutoffIntegralV1 d ν hLevy θ
  have hD : Continuous D := by unfold D; fun_prop
  change ContinuousAt (fun θ => Complex.exp (-(t : ℝ) *
    (D θ + ∫ x, F θ x ∂ν))) 0 ∧
    ∀ θ, Tendsto (fun n => Complex.exp (-(t : ℝ) *
      (D θ + ∫ x, F θ x ∂(ν.restrict (S n))))) atTop
      (nhds (Complex.exp (-(t : ℝ) * (D θ + ∫ x, F θ x ∂ν))))
  constructor
  · exact Complex.continuous_exp.continuousAt.tendsto.comp
      (continuousAt_const.mul (hD.continuousAt.add hc)).tendsto
  · intro θ
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (tendsto_const_nhds.add (hl θ)))

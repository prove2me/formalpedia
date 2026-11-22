-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedRightBrownianConditionalExpectationLe
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:32:55.995+00:00
-- url     : https://prove2.me/submissions/0b905049-721f-439a-89b6-c6bf522995f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanRightConditionalTransitionValue
import Theorems.Thm_Kyprianou_Ch01_mckeanBrownianDiscountedSemigroupExcessive

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Conditional Brownian transition and q-excessivity yield the required inequality. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) | F s] ≤ᵐ[P]
      (fun ω => Real.exp (-q * (s : ℝ)) *
        mckeanValue K barrier phi (x + X s ω)) := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  let b : ℝ := Real.log (K * phi / (1 + phi))
  change ∀ s t : ℝ≥0, s ≤ t →
    P[(fun ω => Real.exp (-q * (t : ℝ)) *
      mckeanValue K b phi (x + X t ω)) | F s] ≤ᵐ[P]
    (fun ω => Real.exp (-q * (s : ℝ)) *
      mckeanValue K b phi (x + X s ω))
  intro s t hst
  have hTransition :
      P[(fun ω => Real.exp (-q * (t : ℝ)) *
          mckeanValue K b phi (x + X t ω)) | F s] =ᵐ[P]
        (fun ω => Real.exp (-q * (t : ℝ)) *
          ∫ ξ, mckeanValue K b phi
            ((x + X s ω) + X (t - s) ξ) ∂P) :=
    Kyprianou.Ch01.mckeanRightConditionalTransitionValue
      P X sigma gamma K q x hsigma hK hq hB
      hXmeas hAllContinuous F hF s t hst
  have hBound (ω : Ω) :
      Real.exp (-q * (t : ℝ)) *
        (∫ ξ, mckeanValue K b phi
          ((x + X s ω) + X (t - s) ξ) ∂P)
      ≤ Real.exp (-q * (s : ℝ)) *
        mckeanValue K b phi (x + X s ω) :=
    Kyprianou.Ch01.mckeanBrownianDiscountedSemigroupExcessive
      P X sigma gamma K q x hsigma hK hq hB
      hXmeas hAllContinuous s t hst (x + X s ω)
  filter_upwards [hTransition] with ω he
  exact (le_of_eq he).trans (hBound ω)

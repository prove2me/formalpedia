-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedRightNaturalSupermartingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:12:03.765812+00:00
-- url     : https://prove2.me/submissions/852e9988-91ef-45b0-b279-c7f3674eed32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightStronglyAdaptedIntegrable
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightBrownianConditionalExpectationLe

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual conditional Brownian inequality closes the right-natural supermartingale. -/
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
    Supermartingale
      (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) F P := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  let barrier : ℝ := Real.log (K * phi / (1 + phi))
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-q * (t : ℝ)) * mckeanValue K barrier phi (x + X t ω)
  change Supermartingale M F P
  have hphi : 0 < phi :=
    Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  have hAI :
      StronglyAdapted F M ∧ ∀ t : ℝ≥0, Integrable (M t) P :=
    Kyprianou.Ch01.mckeanDiscountedRightStronglyAdaptedIntegrable
      P X x K q phi hK hq hphi F hF
  have hCE :
      ∀ s t : ℝ≥0, s ≤ t →
        P[M t | F s] ≤ᵐ[P] M s :=
    Kyprianou.Ch01.mckeanDiscountedRightBrownianConditionalExpectationLe
      P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous F hF
  exact ⟨hAI.1, hCE, hAI.2⟩

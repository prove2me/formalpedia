-- Prove2me | solution 2 for Kyprianou.Ch01.mckeanBrownianPutOptimalRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:22:58.932264+00:00
-- url     : https://prove2.me/submissions/28dd61fa-bf9a-4958-9898-d4601333221f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
import Theorems.Thm_Kyprianou_Ch01_mckeanValueSmoothFit
import Theorems.Thm_Kyprianou_Ch01_mckeanPutStochasticOptimalityRightContinuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The McKean optimum combines its stochastic verification, a positive
    Brownian root and the already established deterministic smooth fit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    let tauStar : Ω → WithTop ℝ≥0 := firstLowerPassage X x barrier
    0 < phi ∧
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier := by
  dsimp only
  have hphi := Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  let phi : ℝ := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  let barrier : ℝ := Real.log (K * phi / (1 + phi))
  have hStoch := Kyprianou.Ch01.mckeanPutStochasticOptimalityRightContinuous
    P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous
  have hSmooth := Kyprianou.Ch01.mckeanValueSmoothFit K phi hK hphi
  change HasDerivAt (mckeanValue K barrier phi) (-Real.exp barrier) barrier at hSmooth
  exact ⟨hphi, hStoch.1, hStoch.2.1, hStoch.2.2.1, hStoch.2.2.2, hSmooth⟩

-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValueRightStoppedExpectedUpper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:51:57.761334+00:00
-- url     : https://prove2.me/submissions/b11f9670-7000-4d1d-84f1-16fe5e417efe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_monotone
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightNaturalSupermartingale
import Theorems.Thm_Kyprianou_Ch01_mckeanRightOptionalSamplingFromSupermartingaleZeroStart

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

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
    ∀ tau : Ω → WithTop ℝ≥0,
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
      let Z : Ω → ℝ := fun ω =>
        match tau ω with
        | none => 0
        | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)
      Integrable Z P ∧
        (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
      sigma ^ 2
  let barrier : ℝ := Real.log (K * phi / (1 + phi))
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X t ω
  have hYmeas (t : ℝ≥0) : Measurable (Y t) :=
    measurable_const.add (hXmeas t)
  let F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) := {
    seq := naturalSigmaRight Y
    mono' := by
      intro s t hst
      exact Kyprianou.Ch01.naturalSigmaRight_monotone Y hst
    le' := by
      intro t
      exact Kyprianou.Ch01.naturalSigmaRight_le_ambient Y hYmeas t
  }
  have hF (t : ℝ≥0) :
      F t = naturalSigmaRight (fun u ω => x + X u ω) t := rfl
  have hSM :=
    Kyprianou.Ch01.mckeanDiscountedRightNaturalSupermartingale
      P X sigma gamma K q x hsigma hK hq hB hXmeas
      hAllContinuous F hF
  change Supermartingale
    (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) *
      mckeanValue K barrier phi (x + X t ω)) F P at hSM
  have hphi : 0 < phi :=
    Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  have hStart : X 0 = fun _ => 0 := hB.1.start_zero
  intro tau hTau
  exact Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingaleZeroStart
    P X x K q phi hK hq hphi hXmeas hAllContinuous hStart
    F hF hSM tau hTau

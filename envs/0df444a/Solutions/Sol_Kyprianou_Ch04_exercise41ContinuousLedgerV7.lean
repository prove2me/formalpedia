-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ContinuousLedgerV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:23:10.663488+00:00
-- url     : https://prove2.me/submissions/ece6323c-9162-44ce-aa6c-1bb3b5e972f0

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41ContinuousPathLedgerV8
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramPathDataV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (Xleft : NNReal → Ω → ℝ)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => L.X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight) :
    ∀ᵐ w ∂P, ∀ t : NNReal,
      let g := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
      else if 0 < x then fRight x - fRight 0 else 0
      let D := fun x : ℝ => if x < 0 then deriv fLeft x
      else if 0 < x then deriv fRight x else 0
      let μ := (pathJumpMeasure L.X Xleft w).restrict
        (Set.prod (Ioc (0 : ℝ) (t : ℝ)) (Iio (0 : ℝ)))
      let J := fun z : ℝ × ℝ => g (Xleft z.1.toNNReal w + z.2) - g (Xleft z.1.toNNReal w)
      Integrable J μ ∧
        g (L.X t w) = g (L.X 0 w) +
          L.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), D (L.X s.toNNReal w) ∂volume) +
          ∫ z, J z ∂μ := by
  filter_upwards [exercise42AvramPathDataV1 P F L hBV hd Xleft hLeft] with w hw
  obtain ⟨hCadlag,hL,hNeg,hRep,_,_⟩ := hw
  intro t
  exact exercise41ContinuousPathLedgerV8 L.X Xleft w L.drift hd
    (L.X_zero w) hCadlag hL hNeg hRep fLeft fRight hC1Left hC1Right t

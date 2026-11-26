-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ZeroClockFamilyV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:08.629512+00:00
-- url     : https://prove2.me/submissions/8e472a1d-980d-4c2e-b3ba-0ae3551514c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroClockStopV12
import Theorems.Thm_Kyprianou_Ch04_exercise41ClockCoverV14
import Theorems.Thm_Kyprianou_Ch04_exercise41NoJumpFromZeroV6
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitsLocallyFiniteV1
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∃ τ : ℕ → ℕ → Ω → NNReal,
      (∀ j N s, MeasurableSet[F.rightCont s] {w | τ j N w ≤ s}) ∧
      (∀ᵐ w ∂P, ∀ s : NNReal, L.X s w = 0 →
        ∃ j N, τ j N w = s) := by
  classical
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  let τ (j N : ℕ) (w : Ω) : NNReal :=
    (min (⨆ n : ℕ, ⨅ k : ℕ,
      if q j ≤ q k ∧ |L.X (q k) w| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) ((N : NNReal) : WithTop NNReal)).untopD 0
  refine ⟨τ,fun j N => exercise41ZeroClockStopV12 F L.X L.adapted q (q j) N,?_⟩
  filter_upwards [exercise41NoJumpFromZeroV6 P F L hBV hd,
    exercise41ZeroVisitsLocallyFiniteV1 P F L hBV hd] with w hNoJump hVisits
  exact exercise41ClockCoverV14 (fun s => L.X s w) q hq
    (L.rightCont w) (L.leftLim w) hNoJump hVisits

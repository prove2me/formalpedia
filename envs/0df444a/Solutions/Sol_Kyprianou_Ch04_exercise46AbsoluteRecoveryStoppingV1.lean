-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46AbsoluteRecoveryStoppingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:27:34.548115+00:00
-- url     : https://prove2.me/submissions/a7d7be79-871d-4f3c-ae21-311d3622714c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_NNReal_countable_dense_clock_with_zero
import Theorems.Thm_Kyprianou_Ch04_exercise46SampledRecoveryClockV1
import Theorems.Thm_Kyprianou_Ch04_exercise46SampledRecoveryEqualsFullV1
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    IsStoppingTime G.rightCont R := by
  classical
  dsimp only
  let a : Omega → NNReal := fun w => (A w).untopD 0
  let R : Omega → WithTop NNReal := fun w =>
    ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧ (a w : Real) < L.X r w
      then (r : WithTop NNReal) else ⊤
  obtain ⟨D,hDc,hDd,_⟩ := avram_gbB32_NNReal_countable_dense_clock_with_zero
  have hR : IsStoppingTime G.rightCont R := by
    have hs := Kyprianou.Ch04.exercise46SampledRecoveryClockV1 P G L A hA D hDc
    have he : (fun w => ⨅ r ∈ D, if A w < (r : WithTop NNReal) ∧
        (a w : Real) < L.X r w then (r : WithTop NNReal) else ⊤) = R := by
      funext w
      exact Kyprianou.Ch04.exercise46SampledRecoveryEqualsFullV1 D hDd
        (fun t => L.X t w) (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).2
        (A w) (a w : Real)
    rw [he] at hs
    exact hs
  exact hR

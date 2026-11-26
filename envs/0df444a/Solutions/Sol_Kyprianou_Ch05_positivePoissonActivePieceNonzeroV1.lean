-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonActivePieceNonzeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:59:03.285039+00:00
-- url     : https://prove2.me/submissions/e08428ee-8bfa-42c0-96d8-8da172c0deb3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    ∀ᵐ w ∂Q, ∀ k n : ℕ, n < K k w →
      ((volume : Measure ℝ).prod Pi) (prmPiece ((volume : Measure ℝ).prod Pi) k) ≠ 0 := by
  let m := (volume : Measure ℝ).prod Pi
  have he (k : ℕ) : ∀ᵐ w ∂Q, m (prmPiece m k) = 0 → K k w = 0 := by
    by_cases hk : m (prmPiece m k) = 0
    · have hl := hd.law_count k
      change HasLaw (K k) (poissonMeasure (m (prmPiece m k)).toNNReal) Q at hl
      have hzero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
        apply Measure.ext_of_singleton
        intro n
        rw [poissonMeasure_singleton,Measure.dirac_apply' 0 (measurableSet_singleton n)]
        by_cases hn : n = 0
        · subst n; simp
        · simp [Set.indicator_apply,hn,Ne.symm hn,zero_pow hn]
      rw [hk,ENNReal.toNNReal_zero,hzero] at hl
      filter_upwards [hl.ae_eq_of_dirac] with w hw
      exact fun _ => hw
    · exact ae_of_all _ fun w h => (hk h).elim
  filter_upwards [ae_all_iff.2 he] with w hw
  intro k n hn hz
  rw [hw k hz] at hn
  exact Nat.not_lt_zero n hn

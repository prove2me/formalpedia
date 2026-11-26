-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteSlopeCylinderV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:38.356802+00:00
-- url     : https://prove2.me/submissions/60979ed9-0ab2-43d0-ae14-58a0b0e6b640

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (δ : NNReal) (D : Finset NNReal)
    (hD : ∀ u ∈ D, 0 < u ∧ u ≤ δ) :
    let G : Set (NNReal → ℝ) :=
      {y | ∀ u ∈ D, L.drift / 2 * (u : ℝ) ≤ y u}
    MeasurableSet G ∧
      P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
          L.drift / 2 * (u : ℝ) ≤ L.X u ω} ≤
      P {ω | (fun u => L.X u ω) ∈ G} := by
  classical
  dsimp only
  constructor
  · have heq : {y : NNReal → ℝ | ∀ u ∈ D,
        L.drift / 2 * (u : ℝ) ≤ y u} =
        ⋂ u : ↥D, {y : NNReal → ℝ | L.drift / 2 * (u : ℝ) ≤ y u} := by
      ext y
      simp
    rw [heq]
    exact MeasurableSet.iInter fun u =>
      measurableSet_le measurable_const (measurable_pi_apply (u : NNReal))
  · apply measure_mono
    intro ω hω u hu
    exact hω u (hD u hu).1 (hD u hu).2

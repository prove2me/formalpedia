-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_dyadic_no_passage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:26:47.347808+00:00
-- url     : https://prove2.me/submissions/f814f09e-3e49-4184-9980-4606506f6dd7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_iff_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The dyadic infimum reward is one on a path which never enters the negative half-line. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (w : Ω) (h : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = ⊤)
    (β : ℝ) (hβ : 0 ≤ β) :
    (⨅ q : ℕ × ℕ, ENNReal.ofReal
      (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w))) = 1 := by
  apply le_antisymm
  · have h0 := iInf_le (fun q : ℕ × ℕ =>
      ENNReal.ofReal (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w))) (0,0)
    simpa [L.X_zero] using h0
  · apply le_iInf
    intro q
    have hx : 0 ≤ L.X ((q.1 : NNReal) / 2 ^ q.2) w := by
      by_contra hn
      exact (Kyprianou.Ch04.cor412_finite_iff_negative P F L w).2
        ⟨_,lt_of_not_ge hn⟩ h
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hβ hx))

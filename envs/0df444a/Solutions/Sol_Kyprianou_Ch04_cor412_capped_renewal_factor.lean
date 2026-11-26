-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_capped_renewal_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:21:24.305173+00:00
-- url     : https://prove2.me/submissions/0b9903c9-1dc5-4e12-874a-cc12d9137f9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_clock
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_history_weight
import Theorems.Thm_Kyprianou_Ch04_cor412_rightcont_weight_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_meas
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Strong Markov factorisation of the capped passage-position weight and future infimum reward. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) =
      min (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) (n : WithTop NNReal))
    (β : ℝ) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (n : WithTop NNReal)}
    let W : Ω → ℝ≥0∞ := A.indicator (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w, W w * R (fun t => L.X (T w + t) w - L.X (T w) w) ∂P) =
      (∫⁻ w, W w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P) := by
  intro A W R
  let τ : Ω → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
  have ht := Kyprianou.Ch04.cor412_lower_stop P F L
  have hs := Kyprianou.Ch04.cor412_capped_clock F.rightCont τ ht n T hT
  have hts (s : NNReal) : MeasurableSet[F.rightCont s] {w : Ω | T w ≤ s} := by
    simpa only [WithTop.coe_le_coe] using hs s
  let hstop := isStoppingTime_withTop_of_le_events T hts
  have hWp : Measurable[hstop.measurableSpace] W :=
    Kyprianou.Ch04.cor412_capped_history_weight L τ ht n T hT hstop β
  have hW : Measurable W := hWp.mono hstop.measurableSpace_le le_rfl
  exact Kyprianou.Ch04.cor412_rightcont_weight_factor L T hts W hW hWp R
    (Kyprianou.Ch04.cor412_dyadic_reward_meas β)

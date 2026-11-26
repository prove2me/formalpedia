-- Prove2me | solution 1 for Kyprianou.Ch04.predictableLeftVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:49:00.00824+00:00
-- url     : https://prove2.me/submissions/c8bb6a72-130c-4f04-926a-3abde8981614

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Canonical strict left limits of an everywhere regular adapted process are predictable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Y : NNReal → Ω → ℝ) (hY : StronglyAdapted F Y)
    (hl : ∀ ω (t : NNReal), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 l)) :
    IsStronglyPredictable F (fun t ω => Function.leftLim (fun s => Y s ω) t) := by
  exact AvramDividend.Classical.avram_wave3_04_strongAdapted_leftContinuous_predictable
    (AvramDividend.Classical.avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits Y hY hl)
    (fun ω => AvramDividend.Classical.avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
      (fun s => Y s ω) (hl ω))

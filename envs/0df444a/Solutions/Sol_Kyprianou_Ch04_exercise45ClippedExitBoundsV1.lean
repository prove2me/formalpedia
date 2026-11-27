-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ClippedExitBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:12:20.208997+00:00
-- url     : https://prove2.me/submissions/b924d26f-752a-46dd-b22a-c5ca1a95faf7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
import Theorems.Thm_Kyprianou_Ch04_stateExitExhaustsCompactClock
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Spatial exit clocks bound the left state through the exit, including time zero. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hL0 : ∀ᵐ w ∂P, L 0 w = X 0 w) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    ∀ᵐ w ∂P, ∀ n, (∀ t < τ n w, |X t w| ≤ (n : ℝ)) ∧
      (∀ t ≤ τ n w, |L t w| ≤ (n : ℝ)) := by
  let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
    sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
  let τ (n : ℕ) (w : Ω) : NNReal :=
    (min (σ n w) (n : NNReal)).untopD (n : NNReal)
  have hc (n : ℕ) (w : Ω) : (τ n w : WithTop NNReal) = min (σ n w) (n : NNReal) :=
    Kyprianou.Ch04.clippedClockCoe (σ n w) (n : NNReal)
  filter_upwards [hL,hL0] with w hw hw0
  intro n
  obtain ⟨hpre,hleft⟩ := Kyprianou.Ch04.stateExitPreLimitBound (fun t => X t w) (fun t => L t w) (n : ℝ) hw
  have hle : (τ n w : WithTop NNReal) ≤ σ n w := by rw [hc]; exact min_le_left _ _
  constructor
  · intro t ht
    exact hpre t ((WithTop.coe_lt_coe.mpr ht).trans_le hle)
  · intro t ht
    by_cases hz : t = 0
    · rw [hz,hw0,hX.start_zero]
      simp
    · exact hleft t (pos_iff_ne_zero.mpr hz) ((WithTop.coe_le_coe.mpr ht).trans hle)

-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ClippedExitMonotoneCofinalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:12:38.905072+00:00
-- url     : https://prove2.me/submissions/fbae267b-3187-49d4-b158-7cf8fb1530e8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
import Theorems.Thm_Kyprianou_Ch04_stateExitExhaustsCompactClock
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite spatial exit clocks are bounded, monotone and exhaust compact time. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    (∀ n w, τ n w ≤ (n : NNReal)) ∧
    (∀ w, Monotone (fun n => τ n w)) ∧
    (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) := by
  let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
    sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
  let τ (n : ℕ) (w : Ω) : NNReal :=
    (min (σ n w) (n : NNReal)).untopD (n : NNReal)
  have hc (n : ℕ) (w : Ω) : (τ n w : WithTop NNReal) = min (σ n w) (n : NNReal) :=
    Kyprianou.Ch04.clippedClockCoe (σ n w) (n : NNReal)
  have hσ : ∀ w, Monotone (fun n => σ n w) := by
    intro w n m hnm
    apply sInf_le_sInf
    rintro v ⟨u, rfl, hu⟩
    exact ⟨u, rfl, (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm).trans_lt hu⟩
  have hτ : ∀ w, Monotone (fun n => τ n w) := by
    intro w n m hnm
    have hh : (n : NNReal) ≤ (m : NNReal) := by exact_mod_cast hnm
    exact WithTop.coe_le_coe.mp (by rw [hc, hc]; exact min_le_min (hσ w hnm) (WithTop.coe_le_coe.mpr hh))
  refine ⟨?_,hτ,?_⟩
  · intro n w
    apply WithTop.coe_le_coe.mp
    rw [hc]
    exact min_le_right _ _
  · filter_upwards [hX.cadlag_ae] with w hw
    rw [WithTop.tendsto_nhds_top_iff]
    intro T
    obtain ⟨k,hk⟩ := Kyprianou.Ch04.stateExitExhaustsCompactClock (fun t => X t w) hw T
    obtain ⟨l,hl⟩ := exists_nat_gt T
    filter_upwards [eventually_ge_atTop (max k l)] with n hn
    rw [hc]
    apply lt_min
    · exact hk.trans_le (hσ w ((le_max_left k l).trans hn))
    · exact WithTop.coe_lt_coe.mpr (hl.trans_le (by exact_mod_cast ((le_max_right k l).trans hn)))

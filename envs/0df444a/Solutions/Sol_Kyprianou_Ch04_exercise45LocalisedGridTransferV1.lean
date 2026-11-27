-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45LocalisedGridTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:06:29.156241+00:00
-- url     : https://prove2.me/submissions/6a71cf75-0fd4-47ac-af34-862a79bda509

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_localisationOuterEventLimitV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local bounded integral witnesses agree on increasingly likely compact path events. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X H I : NNReal → Ω → ℝ)
    (Hn In : ℕ → NNReal → Ω → ℝ)
    (B : NNReal → ℕ → Set Ω)
    (hB : ∀ T, Tendsto (fun n => (P (B T n)).toReal) atTop (nhds 0))
    (hIn : ∀ n, Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X (Hn n) (In n))
    (hEq : ∀ T n w, w ∉ B T n → ∀ t ≤ T,
      H t w = Hn n t w ∧ I t w = In n t w) :
    Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X H I := by
  intro T ε hε
  let G (W : NNReal → Ω → ℝ) (j : ℕ) (t : NNReal) (w : Ω) :=
    ∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      W u w * (X (min t v) w - X (min t u) w)
  let A (n j : ℕ) : Set Ω := {w | ∃ t ≤ T, ε ≤ |G (Hn n) j t w - In n t w|}
  let E (j : ℕ) : Set Ω := {w | ∃ t ≤ T, ε ≤ |G H j t w - I t w|}
  change Tendsto (fun j => (P (E j)).toReal) atTop (nhds 0)
  apply Kyprianou.Ch04.localisationOuterEventLimitV1 P (B T) A E (hB T)
  · intro n
    exact hIn n T ε hε
  · intro n j w hw
    by_cases hb : w ∈ B T n
    · exact Or.inl hb
    · right
      obtain ⟨t,ht,herr⟩ := hw
      refine ⟨t,ht,?_⟩
      have hgrid : G H j t w = G (Hn n) j t w := by
        unfold G
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : k < j := Finset.mem_range.mp hk
        have hj : (0 : NNReal) < (j : NNReal) := by exact_mod_cast Nat.zero_lt_of_lt hkj
        have hu : T * (k : NNReal) / (j : NNReal) ≤ T := by
          rw [div_le_iff₀ hj]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkj.le) (by positivity)
        dsimp only
        rw [(hEq T n w hb _ hu).1]
      rw [← hgrid, ← (hEq T n w hb t ht).2]
      exact herr

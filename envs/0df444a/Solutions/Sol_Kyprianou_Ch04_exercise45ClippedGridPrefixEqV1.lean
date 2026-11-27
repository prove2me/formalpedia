-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ClippedGridPrefixEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:22:41.54595+00:00
-- url     : https://prove2.me/submissions/45f57051-f7e0-443f-89f0-29e559c0a35e

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two clipped grids agree before a common clock whenever their left weights agree there. -/
theorem solution {Ω : Type}
    (X H K : NNReal → Ω → ℝ) (w : Ω) (T t : NNReal) (j : ℕ)
    (h : ∀ u ≤ t, H u w = K u w) :
    (∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      H u w * (X (min t v) w - X (min t u) w)) =
    (∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      K u w * (X (min t v) w - X (min t u) w)) := by
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  let u : NNReal := T * (k : NNReal) / (j : NNReal)
  let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
  change H u w * (X (min t v) w - X (min t u) w) =
    K u w * (X (min t v) w - X (min t u) w)
  by_cases hu : u ≤ t
  · rw [h u hu]
  · have huv : u ≤ v := by
      dsimp [u,v]
      gcongr
      exact_mod_cast Nat.le_succ k
    have htu : t ≤ u := le_of_not_ge hu
    rw [min_eq_left htu, min_eq_left (htu.trans huv), sub_self, mul_zero, mul_zero]

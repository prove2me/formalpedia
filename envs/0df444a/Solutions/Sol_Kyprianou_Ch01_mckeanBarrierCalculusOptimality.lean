-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanBarrierCalculusOptimality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:03:38.854044+00:00
-- url     : https://prove2.me/submissions/d7ed5dbc-854a-4423-8d23-ef9744ba4863

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanBarrierGlobalMax
import Theorems.Thm_Kyprianou_Ch01_mckeanBarrierIncreasingToStart
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch01

/-- The candidate exercise payoff has zero derivative at McKean's barrier. -/
noncomputable def mckean_barrier_stationary
    (K phi x : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    HasDerivAt
      (fun a => (K - Real.exp a) * Real.exp (-phi * (x - a))) 0 b := by
  dsimp
  let b : ℝ := Real.log (K * phi / (1 + phi))
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have he : Real.exp b = K * phi / (1 + phi) :=
    Real.exp_log harg
  have h1 : HasDerivAt (fun a : ℝ => K - Real.exp a)
      (-Real.exp b) b := by
    simpa using (Real.hasDerivAt_exp b).const_sub K
  have hinner : HasDerivAt (fun a : ℝ => -phi * (x - a)) phi b := by
    have hh := ((hasDerivAt_id b).const_sub x).const_mul (-phi)
    simpa only [id_eq, neg_mul, mul_neg, mul_one, neg_neg] using hh
  have h2 : HasDerivAt (fun a : ℝ => Real.exp (-phi * (x - a)))
      (Real.exp (-phi * (x - b)) * phi) b := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-phi * (x - b))).comp b hinner
  have hz :
      -(Real.exp b * Real.exp (-phi * (x - b))) +
          (K - Real.exp b) *
            (Real.exp (-phi * (x - b)) * phi) = 0 := by
    rw [he]
    field_simp
    ring
  have hf :
      ((fun a : ℝ => K - Real.exp a) *
        (fun a : ℝ => Real.exp (-phi * (x - a)))) =
        (fun a : ℝ => (K - Real.exp a) * Real.exp (-phi * (x - a))) := by
    funext a
    rfl
  have hp := h1.mul h2
  rw [hf] at hp
  have hz2 :
      (-Real.exp b) * Real.exp (-phi * (x - b)) +
        (K - Real.exp b) *
          (Real.exp (-phi * (x - b)) * phi) = 0 := by
    simpa only [neg_mul] using hz
  rw [hz2] at hp
  change HasDerivAt
    (fun a : ℝ => (K - Real.exp a) * Real.exp (-phi * (x - a))) 0 b
  exact hp


end Kyprianou.Ch01

open Kyprianou.Ch01
theorem solution
    (K phi x : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let barrierPayoff : ℝ → ℝ := fun a =>
      (K - Real.exp a) * Real.exp (-phi * (x - a))
    HasDerivAt barrierPayoff 0 b ∧
    (∀ a : ℝ, a ≤ x →
      barrierPayoff a ≤ mckeanValue K b phi x) ∧
    barrierPayoff (min x b) = mckeanValue K b phi x := by
  dsimp
  let b : ℝ := Real.log (K * phi / (1 + phi))
  have hb : b = Real.log (K * phi / (1 + phi)) := rfl
  constructor
  · simpa [b] using
      Kyprianou.Ch01.mckean_barrier_stationary K phi x hK hphi
  constructor
  · intro a ha
    by_cases hx : x < b
    · have hinc := Kyprianou.Ch01.mckeanBarrierIncreasingToStart K phi x b a
        hK hphi hb ha (le_of_lt hx)
      have hxlog : x < Real.log (K * phi / (1 + phi)) := by
        simpa [b] using hx
      simpa [mckeanValue, hxlog, b] using hinc
    · have hbg := Kyprianou.Ch01.mckeanBarrierGlobalMax K phi x b a
        hK hphi hb
      have hxlog : ¬ x < Real.log (K * phi / (1 + phi)) := by
        simpa [b] using hx
      simpa [mckeanValue, hxlog, b] using hbg
  · by_cases hx : x < b
    · have hxlog : x < Real.log (K * phi / (1 + phi)) := by
        simpa [b] using hx
      rw [min_eq_left hxlog.le]
      simp [mckeanValue, hxlog]
    · have hxlog : ¬ x < Real.log (K * phi / (1 + phi)) := by
        simpa [b] using hx
      have hbx : Real.log (K * phi / (1 + phi)) ≤ x := le_of_not_gt hxlog
      rw [min_eq_right hbx]
      simp [mckeanValue, hxlog]

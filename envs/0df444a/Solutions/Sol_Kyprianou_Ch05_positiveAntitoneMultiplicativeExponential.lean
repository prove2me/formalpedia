-- Prove2me | solution 1 for Kyprianou.Ch05.positiveAntitoneMultiplicativeExponential
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:34.840926+00:00
-- url     : https://prove2.me/submissions/50ddc74d-fdf0-415f-ae28-e0c8d2e04871
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_monotoneAdditiveNNRealLinear
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- A positive nonincreasing multiplicative function on nonnegative time, bounded by one, is an exponential with a nonnegative rate. -/
theorem solution
    (g : NNReal → ENNReal)
    (hb : ∀ t, 0 < g t ∧ g t ≤ 1)
    (hm : Antitone g) (hmul : ∀ s t, g (s+t) = g s * g t) :
    ∃ a : Real, 0 ≤ a ∧ ∀ t, g t = ENNReal.ofReal (Real.exp (-a * (t : Real))) := by
  let f : NNReal → Real := fun t => -Real.log (g t).toReal
  have hfin (t : NNReal) : g t ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hb t).2 ENNReal.one_lt_top)
  have hp (t : NNReal) : 0 < (g t).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hb t).1) (hfin t)
  have hle (t : NNReal) : (g t).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hb t).2
  have hadd (s t : NNReal) : f (s+t) = f s + f t := by
    simp only [f, hmul, ENNReal.toReal_mul, Real.log_mul (ne_of_gt (hp s)) (ne_of_gt (hp t))]
    ring
  have hmono : Monotone f := by
    intro s t hst
    dsimp [f]
    have h := ENNReal.toReal_mono (hfin s) (hm hst)
    exact neg_le_neg (Real.log_le_log (hp t) h)
  have hn : 0 ≤ f 1 := by
    exact neg_nonneg.mpr (Real.log_nonpos (hp 1).le (hle 1))
  refine ⟨f 1, hn, fun t => ?_⟩
  have hlin := monotoneAdditiveNNRealLinear f hadd hmono t
  have he : -f 1 * (t : Real) = Real.log (g t).toReal := by
    dsimp [f] at hlin ⊢
    linarith
  rw [he, Real.exp_log (hp t), ENNReal.ofReal_toReal (hfin t)]

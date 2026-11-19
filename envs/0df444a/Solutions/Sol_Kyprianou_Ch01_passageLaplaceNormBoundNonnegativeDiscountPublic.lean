-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceNormBoundNonnegativeDiscountPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:22:17.95396+00:00
-- url     : https://prove2.me/submissions/b4a09845-ac37-4201-ac0b-15a496d439b6

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted first-passage payoff is uniformly bounded, even on infinite passage. -/
theorem solution
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    ‖passageLaplace τ q ω‖ ≤ (1 : ℝ) := by
  unfold passageLaplace
  cases hτ : τ ω with
  | top => simp [hτ]
  | coe t =>
    have h : -q * (t : ℝ) ≤ 0 := by
      have ht : (0 : ℝ) ≤ (t : ℝ) := by positivity
      nlinarith
    simpa [hτ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr h)

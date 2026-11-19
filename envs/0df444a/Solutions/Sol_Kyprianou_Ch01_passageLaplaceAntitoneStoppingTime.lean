-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceAntitoneStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:21:11.288561+00:00
-- url     : https://prove2.me/submissions/ac1ba6dd-e941-41d7-8561-bf88718e6591

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted nonnegative passage payoffs decrease when extended passage time increases. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (T U : Ω → WithTop ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (hle : ∀ ω, T ω ≤ U ω) (ω : Ω) :
    passageLaplace U q ω ≤ passageLaplace T q ω := by
  classical
  cases hT : T ω with
  | top =>
      cases hU : U ω with
      | top => simp [passageLaplace, hT, hU]
      | coe u =>
          have hbad : (⊤ : WithTop ℝ≥0) ≤ (↑u : WithTop ℝ≥0) := by
            simpa only [hT, hU] using hle ω
          exact (WithTop.not_top_le_coe u hbad).elim
  | coe t =>
      cases hU : U ω with
      | top =>
          simp [passageLaplace, hT, hU, Real.exp_nonneg]
      | coe u =>
          have htu : t ≤ u := by
            apply WithTop.coe_le_coe.mp
            simpa only [hT, hU] using hle ω
          have htuReal : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast htu
          have he : -q * (u : ℝ) ≤ -q * (t : ℝ) := by
            nlinarith [hq, htuReal]
          simpa [passageLaplace, hT, hU] using
            (Real.exp_le_exp.mpr he)

-- Prove2me | solution 1 for LevyStochCalc.Probability.enorm_dyadicRunMax_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:47:17.070617+00:00
-- url     : https://prove2.me/submissions/bc52360c-d5de-48b0-86c9-38a36c89b428

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
theorem LevyStochCalc.Probability.dyadicRunMax_nonneg (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicRunMax M T n ω :=
  le_trans (norm_nonneg _)
    (Finset.le_sup' (f := fun k => ‖M (dyadicTime T n k) ω‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))))
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- The sampled running maximum, as an extended non-negative real, is the supremum over the
partition points. -/
theorem solution (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖LevyStochCalc.Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (LevyStochCalc.Probability.dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
  have hcoe : ∀ x : ℝ, 0 ≤ x → ((‖x‖₊ : ℝ≥0) : ℝ) = x := fun x hx => by
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  refine le_antisymm ?_ ?_
  · rcases Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
      (fun k => ‖M (LevyStochCalc.Probability.dyadicTime T n k) ω‖) with ⟨k, hk, hkeq⟩
    refine le_iSup_of_le ⟨k, Finset.mem_range.mp hk⟩ (le_of_eq ?_)
    rw [LevyStochCalc.Probability.dyadicRunMax, hkeq]
    congr 1
    exact NNReal.eq (by simp [Real.norm_eq_abs])
  · refine iSup_le fun k => ?_
    refine ENNReal.coe_le_coe.mpr ?_
    refine NNReal.coe_le_coe.mp ?_
    rw [hcoe _ (LevyStochCalc.Probability.dyadicRunMax_nonneg M T n ω), coe_nnnorm]
    exact Finset.le_sup' (f := fun j => ‖M (LevyStochCalc.Probability.dyadicTime T n j) ω‖)
      (Finset.mem_range.mpr k.isLt)

-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveFailureBudget_le_threshold
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:40.779234+00:00
-- url     : https://prove2.me/submissions/445e1400-3161-4199-8963-1f3bd059a8f5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean (solution of MIPRE.Introspection.adaptiveFailureBudget_le_threshold);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Theorems.Thm_MIPRE_Introspection_adaptiveFailure_step_le_threshold

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
section
theorem adaptiveFailureBudget_step (r n : ℕ) (edges z h initial : ℝ) :
    adaptiveFailureBudget r edges z h initial (n + 1) =
      adaptiveFailureBudget r edges z h initial n +
        adaptiveStepLoss (adaptiveStageBudget r
          (edges * adaptiveFailureBudget r edges z h initial n) z h) := rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveBudgetCoefficient_pos (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveBudgetCoefficient r edges := by
  unfold adaptiveBudgetCoefficient
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSmallThreshold_pos (r n : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveSmallThreshold r edges n := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  induction n with
  | zero => exact div_pos (by norm_num) hC
  | succ n ih =>
    exact lt_min (div_pos ih (by norm_num))
      (div_pos (pow_pos (div_pos ih (by norm_num)) _) hC)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveSmallThreshold_antitone (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    Antitone (adaptiveSmallThreshold r edges) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    adaptiveSmallThreshold r edges (n + 1) ≤ adaptiveSmallThreshold r edges n / 2 :=
      min_le_left _ _
    _ ≤ adaptiveSmallThreshold r edges n := by
      linarith [adaptiveSmallThreshold_pos r n hE]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N) :
    ∀ n, n ≤ N → adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSmallThreshold r edges (N - n) := by
  intro n
  induction n with
  | zero => intro _; simpa only [adaptiveFailureBudget, Nat.sub_zero] using hi
  | succ n ih =>
    intro hn
    have hn' : n ≤ N := (Nat.le_succ n).trans hn
    have hsub : N - n = (N - (n + 1)) + 1 := by omega
    have hlevel : (N - (n + 1)) + 1 ≤ N := by omega
    have ht := adaptiveSmallThreshold_antitone r hE hlevel
    have hf : adaptiveFailureBudget r edges z h initial n ≤
        adaptiveSmallThreshold r edges ((N - (n + 1)) + 1) := by
      simpa only [hsub] using ih hn'
    rw [adaptiveFailureBudget_step]
    exact adaptiveFailure_step_le_threshold r (N - (n + 1)) hE hf
      (hz.trans ht) (hh.trans ht)
end MIPRE.Introspection

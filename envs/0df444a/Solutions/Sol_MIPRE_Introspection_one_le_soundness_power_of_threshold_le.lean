-- Prove2me | solution 1 for MIPRE.Introspection.one_le_soundness_power_of_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:54.949572+00:00
-- url     : https://prove2.me/submissions/6d6dd4c5-666b-43c8-9dac-d8d2fa0cb958

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean (solution of MIPRE.Introspection.one_le_soundness_power_of_threshold_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem iteratedRoot_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < iteratedRoot n t := by
  induction n with
  | zero => exact ht
  | succ n ih => exact Real.sqrt_pos.mpr ih
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_mono (n : ℕ) : Monotone (iteratedRoot n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => Real.sqrt_le_sqrt (ih h)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution (r n : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges) (ht : adaptiveSmallThreshold r edges n ≤ t) :
    1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by
  have hroot := iteratedRoot_pos (3 * n) (adaptiveSmallThreshold_pos r n hE)
  have hrootle := iteratedRoot_mono (3 * n) ht
  have hroot0 : 0 ≤ iteratedRoot (3 * n) t := hroot.le.trans hrootle
  calc
    (1 : ℝ) = (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n)) *
        iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n) := by
      simp [ne_of_gt hroot]
    _ ≤ (1 / iteratedRoot (3 * n) (adaptiveSmallThreshold r edges n)) *
        iteratedRoot (3 * n) t :=
      mul_le_mul_of_nonneg_left hrootle (by positivity)
    _ ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hroot0
end MIPRE.Introspection

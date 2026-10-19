-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveFailure_step_le_threshold
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:48.508981+00:00
-- url     : https://prove2.me/submissions/b2a3d3f3-8cf1-4a08-bf4c-8dc064f411d6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean (solution of MIPRE.Introspection.adaptiveFailure_step_le_threshold);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Theorems.Thm_MIPRE_Introspection_adaptiveStepLoss_le_root

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
section
theorem adaptiveStepLoss_mono {δ η : ℝ} (h : δ ≤ η) :
    adaptiveStepLoss δ ≤ adaptiveStepLoss η := by
  unfold adaptiveStepLoss
  gcongr
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveStageBudget_mono_errors (r : ℕ)
    {e e' z z' h h' : ℝ} (he : e ≤ e') (hz : z ≤ z') (hh : h ≤ h') :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget r e' z' h' := by
  unfold adaptiveStageBudget
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (by norm_num))
    (mul_le_mul_of_nonneg_left he (by positivity)))
    (mul_le_mul_of_nonneg_left hh (by norm_num))
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
theorem adaptiveStageBudget_le_coefficient (r : ℕ) {edges f z h t : ℝ}
    (hE : 0 ≤ edges) (hf : f ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveStageBudget r (edges * f) z h ≤ adaptiveBudgetCoefficient r edges * t := by
  calc
    _ ≤ adaptiveStageBudget r (edges * t) t t :=
      adaptiveStageBudget_mono_errors r (mul_le_mul_of_nonneg_left hf hE) hz hh
    _ = _ := by unfold adaptiveStageBudget adaptiveBudgetCoefficient; ring
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
/-- A stack of three square roots exactly inverts the eighth power on
nonnegative inputs. -/
theorem iteratedRoot_three_pow_eight {t : ℝ} (ht : 0 ≤ t) :
    iteratedRoot 3 (t ^ 8) = t := by
  have h8 : t ^ 8 = (t ^ 4) ^ 2 := by ring
  have h4 : t ^ 4 = (t ^ 2) ^ 2 := by ring
  simp only [iteratedRoot]
  rw [h8, Real.sqrt_sq (by positivity : 0 ≤ t ^ 4), h4,
    Real.sqrt_sq (sq_nonneg t), Real.sqrt_sq ht]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution (r n : ℕ) {edges f z h : ℝ}
    (hE : 0 ≤ edges)
    (hf : f ≤ adaptiveSmallThreshold r edges (n + 1))
    (hz : z ≤ adaptiveSmallThreshold r edges (n + 1))
    (hh : h ≤ adaptiveSmallThreshold r edges (n + 1)) :
    f + adaptiveStepLoss (adaptiveStageBudget r (edges * f) z h) ≤
      adaptiveSmallThreshold r edges n := by
  have hC := adaptiveBudgetCoefficient_pos r hE
  have ht := (adaptiveSmallThreshold_pos r n hE).le
  have hs₁ : adaptiveSmallThreshold r edges (n + 1) ≤
      adaptiveSmallThreshold r edges n / 2 := min_le_left _ _
  have hs₂ : adaptiveSmallThreshold r edges (n + 1) ≤
      (adaptiveSmallThreshold r edges n / 16) ^ 8 / adaptiveBudgetCoefficient r edges :=
    min_le_right _ _
  have hb : adaptiveStageBudget r (edges * f) z h ≤
      (adaptiveSmallThreshold r edges n / 16) ^ 8 := by
    refine (adaptiveStageBudget_le_coefficient r hE hf hz hh).trans ?_
    have hs := (le_div_iff₀ hC).mp hs₂
    simpa only [mul_comm] using hs
  have hl := (adaptiveStepLoss_mono hb).trans
    (adaptiveStepLoss_le_root ((adaptiveSmallThreshold r edges n / 16) ^ 8))
  rw [iteratedRoot_three_pow_eight (div_nonneg ht (by norm_num))] at hl
  linarith
end MIPRE.Introspection

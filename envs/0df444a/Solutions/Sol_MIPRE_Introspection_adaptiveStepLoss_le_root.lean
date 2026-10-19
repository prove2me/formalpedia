-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveStepLoss_le_root
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:55.665024+00:00
-- url     : https://prove2.me/submissions/aca5eccc-7aa2-472e-b974-42866a7f8af9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveStageBudget.lean (solution of MIPRE.Introspection.adaptiveStepLoss_le_root);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution (δ : ℝ) :
    adaptiveStepLoss δ ≤ 8 * iteratedRoot 3 δ := by
  have h64 : Real.sqrt 64 = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have h₁ : Real.sqrt (56 * Real.sqrt δ) ≤ 8 * Real.sqrt (Real.sqrt δ) := by
    calc
      _ ≤ Real.sqrt (64 * Real.sqrt δ) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sqrt_nonneg δ]
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64), h64]
  unfold adaptiveStepLoss
  calc
    _ ≤ 2 * Real.sqrt (16 * Real.sqrt (Real.sqrt δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.sqrt_le_sqrt
      linarith
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), h16]
      simp only [iteratedRoot]
      ring
end MIPRE.Introspection

-- Prove2me | solution 1 for MIPRE.Introspection.self_le_errorProfile_scaled
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:39.0717+00:00
-- url     : https://prove2.me/submissions/5d4de319-35c2-4138-91d5-8a4012321c8c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean (solution of MIPRE.Introspection.self_le_errorProfile_scaled);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution {a b c x ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ errorProfile a b x (c * ε) := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hεc : ε ≤ c * ε := by nlinarith
  have hp := (Real.self_le_rpow_of_le_one hε0 hε1 hb1).trans
    (Real.rpow_le_rpow hε0 hεc hb0)
  have hxa := Real.one_le_rpow hx ha0
  have hn := Real.rpow_nonneg (mul_nonneg hc0 hε0) b
  have hterm : ε ≤ x ^ a * (c * ε) ^ b :=
    hp.trans (by nlinarith)
  have htail := Real.rpow_nonneg hx0 (-b)
  unfold errorProfile
  nlinarith
end MIPRE.Introspection

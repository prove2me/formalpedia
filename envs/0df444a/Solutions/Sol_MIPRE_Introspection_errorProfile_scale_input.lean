-- Prove2me | solution 1 for MIPRE.Introspection.errorProfile_scale_input
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:36.040876+00:00
-- url     : https://prove2.me/submissions/21616dae-d780-4488-8319-b10906ad623c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (solution of MIPRE.Introspection.errorProfile_scale_input);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution {a b c x ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    errorProfile a b x (c * ε) ≤ max 1 (c ^ b) * errorProfile a b x ε := by
  have hu : 0 ≤ x ^ a * ε ^ b := mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hε _)
  have hv : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx _
  have hfirst := mul_le_mul_of_nonneg_right (le_max_right 1 (c ^ b)) hu
  have hsecond := mul_le_mul_of_nonneg_right (le_max_left 1 (c ^ b)) hv
  unfold errorProfile
  rw [Real.mul_rpow hc hε]
  calc
    a * (x ^ a * (c ^ b * ε ^ b) + x ^ (-b)) ≤
        a * (max 1 (c ^ b) * (x ^ a * ε ^ b) + max 1 (c ^ b) * x ^ (-b)) := by
      apply mul_le_mul_of_nonneg_left _ ha
      nlinarith only [hfirst, hsecond]
    _ = max 1 (c ^ b) * (a * (x ^ a * ε ^ b + x ^ (-b))) := by ring
end MIPRE.Introspection

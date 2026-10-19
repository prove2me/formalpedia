-- Prove2me | solution 1 for MIPRE.Introspection.errorProfile_scaled_power
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:19.683956+00:00
-- url     : https://prove2.me/submissions/7ca1bc76-d6e4-423a-903c-e15e3abaadc2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (solution of MIPRE.Introspection.errorProfile_scaled_power);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Theorems.Thm_MIPRE_Introspection_errorProfile_power
import Theorems.Thm_MIPRE_Introspection_errorProfile_scale_input

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
theorem errorProfile_nonneg {a b x ε : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    0 ≤ errorProfile a b x ε := by unfold errorProfile; positivity
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution {C a b c r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x (c * ε)) ^ r ≤
      errorProfile (powerCoefficient (C * (max 1 (c ^ b)) ^ r) a r) (b * r) x ε := by
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  have hscale := Real.rpow_le_rpow (errorProfile_nonneg (b := b) ha hx0 (mul_nonneg hc hε))
    (errorProfile_scale_input (b := b) ha hc hx0 hε) hr0
  have hk : 0 ≤ max 1 (c ^ b) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  rw [Real.mul_rpow hk (errorProfile_nonneg ha hx0 hε)] at hscale
  have h := mul_le_mul_of_nonneg_left hscale hC
  rw [← mul_assoc] at h
  exact h.trans (errorProfile_power (mul_nonneg hC (Real.rpow_nonneg hk _))
    ha hr0 hr1 hx hε)
end MIPRE.Introspection

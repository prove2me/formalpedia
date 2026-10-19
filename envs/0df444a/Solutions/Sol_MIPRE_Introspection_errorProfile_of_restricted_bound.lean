-- Prove2me | solution 1 for MIPRE.Introspection.errorProfile_of_restricted_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:09.491406+00:00
-- url     : https://prove2.me/submissions/d614a603-193e-45a3-baad-72071bde2dba

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean (solution of MIPRE.Introspection.errorProfile_of_restricted_bound);
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
import Theorems.Thm_MIPRE_Introspection_errorProfile_scaled_power
import Theorems.Thm_MIPRE_Introspection_self_le_errorProfile_scaled

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
theorem errorProfile_nonneg {a b x ε : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    0 ≤ errorProfile a b x ε := by unfold errorProfile; positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem one_le_powerCoefficient (C a r : ℝ) : 1 ≤ powerCoefficient C a r := le_max_left _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem rootExponent_pos (k : ℕ) : 0 < rootExponent k := pow_pos (by norm_num) k
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem rootExponent_le_one (k : ℕ) : rootExponent k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_eq_rpow (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedRoot k t = t ^ rootExponent k := by
  induction k with
  | zero => simp [iteratedRoot, rootExponent]
  | succ k ih =>
    rw [iteratedRoot, ih, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
    simp only [rootExponent, pow_succ]
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

namespace MIPRE.Introspection
noncomputable section
/-- The normalized profile is already at least one above the unit interval. -/
theorem one_le_errorProfile {a b x ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hx : 1 ≤ x) (hε : 1 ≤ ε) : 1 ≤ errorProfile a b x ε := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxpow := Real.one_le_rpow hx ha0
  have hεpow := Real.one_le_rpow hε hb
  have htail := Real.rpow_nonneg hx0 (-b)
  have hprod : 1 ≤ x ^ a * ε ^ b := by nlinarith
  unfold errorProfile
  nlinarith
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution {C a b c x ε δ v : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc : 1 ≤ c) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hδ : δ ≤ errorProfile a b x (c * ε)) (hv : 0 ≤ v)
    (hvalue : 1 - C * iteratedRoot k (max ε δ) ≤ v) :
    1 - errorProfile
      (powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
      (b * rootExponent k) x ε ≤ v := by
  by_cases hε1 : ε ≤ 1
  · have hmax : max ε δ ≤ errorProfile a b x (c * ε) := max_le
      (self_le_errorProfile_scaled ha hb0.le hb1 hc hx hε hε1) hδ
    have hp0 := errorProfile_nonneg (a := a) (b := b) (x := x)
      (ε := c * ε) (by linarith) (by linarith) (mul_nonneg (by linarith) hε)
    have hroot := mul_le_mul_of_nonneg_left (iteratedRoot_mono k hmax) hC
    rw [iteratedRoot_eq_rpow k hp0] at hroot
    have hfinal := hroot.trans (errorProfile_scaled_power hC (by linarith)
      (by linarith) (rootExponent_pos k).le (rootExponent_le_one k) hx hε)
    linarith
  · have hlarge := one_le_errorProfile
      (one_le_powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
      (mul_pos hb0 (rootExponent_pos k)).le hx (le_of_not_ge hε1)
    linarith
end MIPRE.Introspection

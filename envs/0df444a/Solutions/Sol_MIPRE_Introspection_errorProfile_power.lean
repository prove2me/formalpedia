-- Prove2me | solution 1 for MIPRE.Introspection.errorProfile_power
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:57.070341+00:00
-- url     : https://prove2.me/submissions/350f39e8-b7ed-4211-a24d-7be55b84577d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ErrorBounds.lean (solution of MIPRE.Introspection.errorProfile_power);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
noncomputable section
theorem one_le_powerCoefficient (C a r : ℝ) : 1 ≤ powerCoefficient C a r := le_max_left _ _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem mul_rpow_le_powerCoefficient (C a r : ℝ) : C * a ^ r ≤ powerCoefficient C a r :=
  (le_max_left _ _).trans (le_max_right _ _)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem mul_le_powerCoefficient (C a r : ℝ) : a * r ≤ powerCoefficient C a r :=
  (le_max_right _ _).trans (le_max_right _ _)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution {C a b r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x ε) ^ r ≤
      errorProfile (powerCoefficient C a r) (b * r) x ε := by
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  have hu : 0 ≤ x ^ a * ε ^ b := mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hε _)
  have hv : 0 ≤ x ^ (-b) := Real.rpow_nonneg hx0 _
  have hcoeff : 0 ≤ C * a ^ r := mul_nonneg hC (Real.rpow_nonneg ha _)
  calc
    C * (errorProfile a b x ε) ^ r =
        (C * a ^ r) * (x ^ a * ε ^ b + x ^ (-b)) ^ r := by
      rw [errorProfile, Real.mul_rpow ha (add_nonneg hu hv)]
      ring
    _ ≤ (C * a ^ r) * ((x ^ a * ε ^ b) ^ r + (x ^ (-b)) ^ r) :=
      mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow hu hv hr0 hr1) hcoeff
    _ = (C * a ^ r) * (x ^ (a * r) * ε ^ (b * r) + x ^ (-(b * r))) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hε _),
        ← Real.rpow_mul hx0, ← Real.rpow_mul hε, ← Real.rpow_mul hx0, neg_mul]
    _ ≤ powerCoefficient C a r *
        (x ^ (powerCoefficient C a r) * ε ^ (b * r) + x ^ (-(b * r))) := by
      apply mul_le_mul (mul_rpow_le_powerCoefficient C a r)
      · exact add_le_add
          (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hx (mul_le_powerCoefficient C a r))
            (Real.rpow_nonneg hε _)) le_rfl
      · positivity
      · exact (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_powerCoefficient C a r)
    _ = errorProfile (powerCoefficient C a r) (b * r) x ε := rfl
end MIPRE.Introspection

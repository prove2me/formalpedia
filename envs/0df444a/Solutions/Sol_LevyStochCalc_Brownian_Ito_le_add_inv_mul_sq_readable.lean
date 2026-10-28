-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.le_add_inv_mul_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:17.604485+00:00
-- url     : https://prove2.me/submissions/6510e69e-2a81-4d53-8dd6-154c705a1b81

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
section Elementary
/-- A scaled arithmetic-geometric bound for extended non-negative reals. -/
theorem solution {ε : ℝ≥0∞} (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (a : ℝ≥0∞) :
    a ≤ ε + ε⁻¹ * a ^ 2 := by
  rcases le_or_gt a ε with h | h
  · calc a ≤ ε := h
      _ = ε + 0 := (add_zero ε).symm
      _ ≤ ε + ε⁻¹ * a ^ 2 := by gcongr; exact zero_le
  · have hmain : a ≤ ε⁻¹ * a ^ 2 := by
      calc a = ε⁻¹ * (ε * a) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
        _ ≤ ε⁻¹ * (a * a) := mul_le_mul' le_rfl (mul_le_mul' h.le le_rfl)
        _ = ε⁻¹ * a ^ 2 := by rw [sq]
    calc a ≤ ε⁻¹ * a ^ 2 := hmain
      _ = 0 + ε⁻¹ * a ^ 2 := (zero_add _).symm
      _ ≤ ε + ε⁻¹ * a ^ 2 := by gcongr; exact zero_le

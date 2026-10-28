-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_add_pow_three_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:28.608825+00:00
-- url     : https://prove2.me/submissions/7a6b94e6-3dd3-4a73-bce1-932e6683abd6

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- `(a + b)³ ≤ 4(a³ + b³)` for nonnegative reals. -/
theorem LevyStochCalc.Brownian.Ito.add_pow_three_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, sq_nonneg (a + b)]
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- `∫|u + v|³ ≤ 4(∫|u|³ + ∫|v|³)`. -/
theorem solution {P : Measure Ω} {u v : Ω → ℝ}
    (hu : MeasureTheory.Integrable (fun ω => |u ω| ^ 3) P)
    (hv : MeasureTheory.Integrable (fun ω => |v ω| ^ 3) P)
    (huv : MeasureTheory.Integrable (fun ω => |u ω + v ω| ^ 3) P) :
    ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
  have hpt : ∀ ω : Ω, |u ω + v ω| ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) := by
    intro ω
    have h3 : |u ω + v ω| ^ 3 ≤ (|u ω| + |v ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
    have h2 : (|u ω| + |v ω|) ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) :=
      LevyStochCalc.Brownian.Ito.add_pow_three_le_four (abs_nonneg _) (abs_nonneg _)
    linarith
  calc ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ ∫ ω, 4 * (|u ω| ^ 3 + |v ω| ^ 3) ∂P :=
        MeasureTheory.integral_mono huv ((hu.add hv).const_mul 4) hpt
    _ = 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hu hv]

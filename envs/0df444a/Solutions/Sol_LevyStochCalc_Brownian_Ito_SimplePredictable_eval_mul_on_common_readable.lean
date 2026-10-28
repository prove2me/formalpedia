-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:01.426452+00:00
-- url     : https://prove2.me/submissions/9bc23d92-dae3-48f2-bcdf-9f4bd661e183

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_ite_mul_sum_ite_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The product on the common refinement evaluates to the product of the evaluations. -/
theorem solution
    {T : ℝ} (H₁ H₂ : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by
  have hl := H₁.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq) (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω
  have hr := H₂.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (h_eq ▸ H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq) (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω
  rw [LevyStochCalc.Brownian.Ito.SimplePredictable.eval] at hl hr ⊢
  change (∑ j : Fin (H₁.mergedM H₂),
      if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
    = H₁.eval s ω * H₂.eval s ω
  rw [← hl, ← hr]
  exact (LevyStochCalc.Brownian.Ito.sum_ite_mul_sum_ite_readable (H₁.mergedπ_strictMono H₂) _ _ s).symm

-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support_and_prefactor_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:36:01.380932+00:00
-- url     : https://prove2.me/submissions/64569d6b-2b06-4b32-8ad2-ebeb9a4bddf3

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_tail_support
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_prefactor_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hne : PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ)) ≠ 0) :
    ((∑ i : Fin d.m,
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
        (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) ∧
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
  exact ⟨
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
      d hnu hH r t hne,
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_prefactor_bound
      d hnu hH r t⟩
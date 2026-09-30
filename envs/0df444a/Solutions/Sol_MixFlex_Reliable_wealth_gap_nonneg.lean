-- Prove2me | solution 1 for MixFlex.Reliable.wealth_gap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:38.302875+00:00
-- url     : https://prove2.me/submissions/b3001698-31a4-4f8d-ae64-3da7e5cf520e

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model
set_option autoImplicit false
open MixFlex.Reliable
theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    (X : Ω → Fin N → ℝ) (K : Fin N → ℝ) (ω : Ω) :
    wealthSF P X P.c (∑ n, K n) ω - wealthSD P X K ω =
        P.p * (min (∑ n, X ω n) (∑ n, K n) - ∑ n, min (X ω n) (K n)) ∧
      0 ≤ wealthSF P X P.c (∑ n, K n) ω - wealthSD P X K ω := by
  have he : wealthSF P X P.c (∑ n, K n) ω - wealthSD P X K ω =
      P.p * (min (∑ n, X ω n) (∑ n, K n) - ∑ n, min (X ω n) (K n)) := by
    unfold wealthSF wealthSD
    ring
  refine ⟨he, ?_⟩
  rw [he]
  apply mul_nonneg hP.p_pos.le
  apply sub_nonneg.mpr
  exact le_min (Finset.sum_le_sum fun n _ => min_le_left _ _)
    (Finset.sum_le_sum fun n _ => min_le_right _ _)


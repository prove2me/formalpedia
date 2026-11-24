-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.conj_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:57.438648+00:00
-- url     : https://prove2.me/submissions/9139a182-667d-4288-9a8b-4375ae767e70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Theorems.Thm_GlobalTheory_ReducedBasisBound_abs_sum_le_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℝ) (hk : ∀ l i, |k l i| ≤ 1) (R : ℝ)
    (hR : 0 ≤ R) (hX : ∀ i j, |X i j| ≤ R) (i j : Fin N) :
    |(kᵀ * X * k) i j| ≤ N * (N * R) := by
  rw [mul_apply]
  apply abs_sum_le_card
  intro q
  rw [abs_mul]
  have hin : |(kᵀ * X) i q| ≤ N * R := by
    rw [mul_apply]
    apply abs_sum_le_card
    intro l
    rw [abs_mul, transpose_apply]
    calc |k l i| * |X l q| ≤ 1 * R := mul_le_mul (hk l i) (hX l q) (abs_nonneg _) zero_le_one
      _ = R := one_mul R
  calc |(kᵀ * X) i q| * |k q j| ≤ (N * R) * 1 := mul_le_mul hin (hk q j) (abs_nonneg _) (by positivity)
    _ = N * R := mul_one _
end GlobalTheory.ReducedBasisBound

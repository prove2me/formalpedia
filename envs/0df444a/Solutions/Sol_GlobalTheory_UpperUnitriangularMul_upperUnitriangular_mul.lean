-- Prove2me | solution 1 for GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:11.655235+00:00
-- url     : https://prove2.me/submissions/73dda535-1653-4734-a990-5ed96c5186f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperUnitriangularMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperUnitriangularMul
open Matrix
namespace GlobalTheory.UpperUnitriangularMul
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
end GlobalTheory.UpperUnitriangularMul

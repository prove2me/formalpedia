-- Prove2me | solution 1 for GlobalTheory.LowerTriangularMul.lowerTriangular_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:52:05.690276+00:00
-- url     : https://prove2.me/submissions/e49e5121-92c9-4d56-bf41-9a8fdc79b604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriangularMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LowerTriangularMul
namespace GlobalTheory.LowerTriangularMul
theorem _root_.solution {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with hik | hki
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hki hij), mul_zero]
end GlobalTheory.LowerTriangularMul

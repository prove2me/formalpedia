-- Prove2me | solution 1 for GlobalTheory.LowerTriangularMul.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:27.684944+00:00
-- url     : https://prove2.me/submissions/66cecd5c-607f-4fce-be2a-2eefef74b244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriangularMul
import Theorems.Thm_GlobalTheory_LowerTriangularMul_lowerTriangular_mul

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
theorem _root_.solution : ∀ {S : Type} [inst : CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S), (∀ (i j : Fin n), i < j → A i j = (0 : S)) → (∀ (i j : Fin n), i < j → B i j = (0 : S)) → ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) :=
  fun A B hA hB => lowerTriangular_mul A B hA hB
end GlobalTheory.LowerTriangularMul

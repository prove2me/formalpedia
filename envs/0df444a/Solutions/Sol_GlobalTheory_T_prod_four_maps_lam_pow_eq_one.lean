-- Prove2me | solution 1 for GlobalTheory.T.prod_four_maps_lam_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:01.806054+00:00
-- url     : https://prove2.me/submissions/6dc95956-06dc-4b70-8919-12cb489927d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOneStatement
import Theorems.Thm_GlobalTheory_SymmProd_prod_four_maps_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fin r → U), (∀ k l, lam k l = lam l k) → W = (W + W.transpose) * A → ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k * (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  first | exact @GlobalTheory.SymmProd.prod_four_maps_eq_one | exact GlobalTheory.SymmProd.prod_four_maps_eq_one | (intros; apply GlobalTheory.SymmProd.prod_four_maps_eq_one <;> assumption)
end _root_.GlobalTheory.T

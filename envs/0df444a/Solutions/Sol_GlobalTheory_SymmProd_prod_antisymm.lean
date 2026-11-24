-- Prove2me | solution 1 for GlobalTheory.SymmProd.prod_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:55.293527+00:00
-- url     : https://prove2.me/submissions/42eb441b-9d2f-4a03-92e8-e77657d4551c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SymmProd
open scoped Matrix
namespace GlobalTheory.SymmProd
theorem _root_.solution {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by
  simp only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  rw [mul_inv_eq_one, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]
end GlobalTheory.SymmProd

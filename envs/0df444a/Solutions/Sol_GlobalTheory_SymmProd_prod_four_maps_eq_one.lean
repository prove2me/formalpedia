-- Prove2me | solution 1 for GlobalTheory.SymmProd.prod_four_maps_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:40.257201+00:00
-- url     : https://prove2.me/submissions/d6c03faa-eede-494a-a4bb-1b9701c1ac3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne
import Theorems.Thm_GlobalTheory_SymmProd_zpow_finsum_eq
import Theorems.Thm_GlobalTheory_SymmProd_prod_collect
import Theorems.Thm_GlobalTheory_SymmProd_prod_antisymm

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
theorem _root_.solution (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k)
    (hW : W = (W + W.transpose) * A) :
    ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^
      ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k *
        (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^
      ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  simp only [prod_collect]
  rw [← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsum_eq, ← Matrix.sum_apply]
  refine congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_
  have h2 : Wᵀ * A = W - W * A := by
    rw [eq_sub_iff_add_eq, add_comm, ← add_mul]; exact hW.symm
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_zero, h2]
  noncomm_ring
end GlobalTheory.SymmProd

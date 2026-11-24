-- Prove2me | solution 1 for GlobalTheory.SymmProd.prod_collect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:56.36385+00:00
-- url     : https://prove2.me/submissions/8ad56d4d-e8ed-4a57-97cc-a28a04c22be5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdFourMapsEqOne
import Theorems.Thm_GlobalTheory_SymmProd_zpow_finsum_eq

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
theorem _root_.solution {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by
  have h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j) := by
    intro k l
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]
  calc ∏ i, ∏ j, ∏ k, ∏ l, lam k l ^ (M i k * M j l * (e * W i j))
      = ∏ i, ∏ k, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) := Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ l, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ l, ∏ i, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_comm
end GlobalTheory.SymmProd

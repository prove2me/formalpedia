-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_monic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:45.780688+00:00
-- url     : https://prove2.me/submissions/4a38c7ec-8f4f-45f6-8796-b5aca7d36864

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_sumPoly_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
theorem _root_.solution {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (h : c n = 1) :
    (sumPoly c n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · rw [sumPoly_coeff]; simp [h]
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

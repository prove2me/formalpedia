-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:55.349466+00:00
-- url     : https://prove2.me/submissions/a8a7b6f0-cf40-484c-93e8-c81da5590522

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal

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
theorem _root_.solution {A : Type} [CommRing A] (c : ℕ → A) (n m : ℕ) :
    (sumPoly c n).coeff m = if m < n + 1 then c m else 0 := by
  simp [sumPoly, finset_sum_coeff, coeff_C_mul_X_pow]
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

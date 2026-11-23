-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.sumPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:50.277562+00:00
-- url     : https://prove2.me/submissions/243e4858-7871-4834-9a56-41274af587e3

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
theorem _root_.solution {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (x : A) :
    (sumPoly c n).eval x = ∑ k ∈ Finset.range (n + 1), c k * x ^ k := by
  simp [sumPoly, eval_finset_sum]
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

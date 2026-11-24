-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.substF_monomial_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:04.162143+00:00
-- url     : https://prove2.me/submissions/01e43fcf-e7b3-4715-b877-158f0e10a69e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.SubstCoeff
variable {σ : Type}
variable {ι : Type} {N n : ℕ}
namespace GlobalTheory.SubstCoeff
theorem _root_.solution (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by
  rw [monomial_eq, map_mul, C_1, map_one, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
end GlobalTheory.SubstCoeff

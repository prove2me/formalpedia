-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:45.217767+00:00
-- url     : https://prove2.me/submissions/4d0deaf2-7d82-47a9-8d0d-576e4bc6aab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_mul
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_one

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
namespace GlobalTheory.SubstCoeff
theorem _root_.solution (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (coeff m P)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (P ^ e)) := by
  induction e generalizing m with
  | zero => simpa only [pow_zero] using isAlgebraic_coeff_one m
  | succ e ih =>
    rw [pow_succ]
    exact isAlgebraic_coeff_mul _ _ ih hP m
end GlobalTheory.SubstCoeff

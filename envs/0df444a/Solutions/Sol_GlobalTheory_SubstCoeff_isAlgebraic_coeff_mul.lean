-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:53.074384+00:00
-- url     : https://prove2.me/submissions/3a112eb2-f460-4209-b158-2de8286063ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_sum

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (coeff m P)) (hQ : ∀ m, IsAlgebraic ℚ (coeff m Q)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (P * Q)) := by
  classical
  rw [coeff_mul]
  exact isAlgebraic_sum _ _ fun x _ => (hP _).mul (hQ _)
end GlobalTheory.SubstCoeff

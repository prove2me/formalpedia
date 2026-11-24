-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:03.999915+00:00
-- url     : https://prove2.me/submissions/e427353a-4fb7-4ed5-bc45-d41960d39991

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
namespace GlobalTheory.SubstCoeff
theorem _root_.solution (m : σ →₀ ℕ) : IsAlgebraic ℚ (coeff m (1 : MvPolynomial σ ℂ)) := by
  classical
  rw [coeff_one]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero
end GlobalTheory.SubstCoeff

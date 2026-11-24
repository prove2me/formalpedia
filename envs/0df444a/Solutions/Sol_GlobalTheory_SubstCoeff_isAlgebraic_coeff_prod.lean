-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:19.483569+00:00
-- url     : https://prove2.me/submissions/3259408c-5231-494b-9b90-fe8a3eb5546d

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
theorem _root_.solution {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (coeff m (f q))) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (∏ q ∈ s, f q)) :=
  Finset.prod_induction f (fun P => ∀ m, IsAlgebraic ℚ (coeff m P))
    (fun _ _ ha hb => isAlgebraic_coeff_mul _ _ ha hb) isAlgebraic_coeff_one hf m
end GlobalTheory.SubstCoeff

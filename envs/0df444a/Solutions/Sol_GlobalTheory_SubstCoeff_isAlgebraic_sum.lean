-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:04.696318+00:00
-- url     : https://prove2.me/submissions/5fdd7329-aa20-49b4-806c-42268794eab7

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
theorem _root_.solution {κ : Type} (s : Finset κ) (f : κ → ℂ) (hf : ∀ q ∈ s, IsAlgebraic ℚ (f q)) :
    IsAlgebraic ℚ (∑ q ∈ s, f q) :=
  Finset.sum_induction f (IsAlgebraic ℚ) (fun _ _ ha hb => ha.add hb) isAlgebraic_zero hf
end GlobalTheory.SubstCoeff

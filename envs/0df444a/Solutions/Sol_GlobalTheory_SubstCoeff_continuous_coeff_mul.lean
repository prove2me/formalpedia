-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.continuous_coeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:03.151283+00:00
-- url     : https://prove2.me/submissions/a94ccee0-701a-49a2-ac67-e2a81832f65c

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
theorem _root_.solution {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (hG : ∀ m, Continuous fun y => coeff m (G y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y * G y) := by
  classical
  simp only [coeff_mul]
  exact continuous_finset_sum _ fun x _ => (hF _).mul (hG _)
end GlobalTheory.SubstCoeff

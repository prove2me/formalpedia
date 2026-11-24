-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.continuous_coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:14.128368+00:00
-- url     : https://prove2.me/submissions/58194b41-2359-42e0-9005-13f821365bba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_mul

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
theorem _root_.solution {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y ^ e) := by
  induction e generalizing m with
  | zero =>
    classical
    simp only [pow_zero, coeff_one]
    exact continuous_const
  | succ e ih =>
    simp only [pow_succ]
    exact continuous_coeff_mul _ _ ih hF m
end GlobalTheory.SubstCoeff

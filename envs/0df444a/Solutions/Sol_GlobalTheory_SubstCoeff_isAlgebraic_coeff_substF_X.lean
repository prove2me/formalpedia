-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.isAlgebraic_coeff_substF_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:15.779802+00:00
-- url     : https://prove2.me/submissions/7696bcda-517f-43b5-b3e9-a9cbf816558e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_sum
import Theorems.Thm_GlobalTheory_CompactHowe_substF_X


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
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (GlobalTheory.CompactHowe.substF h g (X q))) := by
  classical
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine isAlgebraic_sum _ _ fun a _ => isAlgebraic_sum _ _ fun b _ => ?_
  refine ((hh _ _ _).mul (hg _ _ _)).mul ?_
  rw [coeff_X']
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero
end GlobalTheory.SubstCoeff

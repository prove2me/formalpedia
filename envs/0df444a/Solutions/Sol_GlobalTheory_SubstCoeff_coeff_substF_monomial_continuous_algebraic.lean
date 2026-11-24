-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:25:57.197255+00:00
-- url     : https://prove2.me/submissions/764cc241-d9ac-4284-ae75-46377f3bdc31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_pow
import Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_prod
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_pow
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_prod
import Theorems.Thm_GlobalTheory_SubstCoeff_substF_monomial_one
import Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_substF_X
import Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_substF_X

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
theorem _root_.solution :
    ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by
  intro ι N n k k'
  refine ⟨?_, fun h g hh hg => ?_⟩
  · simp only [substF_monomial_one]
    exact continuous_coeff_prod _ _ (fun q _ m => continuous_coeff_pow _ (continuous_coeff_substF_X q) _ m) k'
  · rw [substF_monomial_one]
    exact isAlgebraic_coeff_prod _ _
      (fun q _ m => isAlgebraic_coeff_pow _ (isAlgebraic_coeff_substF_X h g hh hg q) _ m) k'
end GlobalTheory.SubstCoeff

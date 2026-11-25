-- Prove2me | solution 1 for GlobalTheory.T.ellipticSystem_derivative_continuous_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:29.336472+00:00
-- url     : https://prove2.me/submissions/fcf4fa5b-0058-42fc-ae33-d78bc0325c5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Theorems.Thm_GlobalTheory_HCA_dw_solSet_continuous_functional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  first | exact @GlobalTheory.HCA.dw_solSet_continuous_functional | exact GlobalTheory.HCA.dw_solSet_continuous_functional | (intros; apply GlobalTheory.HCA.dw_solSet_continuous_functional <;> assumption)
end _root_.GlobalTheory.T

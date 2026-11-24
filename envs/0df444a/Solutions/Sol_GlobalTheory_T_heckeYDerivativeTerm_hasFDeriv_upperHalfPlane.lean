-- Prove2me | solution 1 for GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:27.967423+00:00
-- url     : https://prove2.me/submissions/9c77863e-086b-482e-9d0c-3316124a0c29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlane
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_termQ_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  first | exact @GlobalTheory.HeckeTwo.termQ_fderiv | exact GlobalTheory.HeckeTwo.termQ_fderiv | (intros; apply GlobalTheory.HeckeTwo.termQ_fderiv <;> assumption)
end _root_.GlobalTheory.T

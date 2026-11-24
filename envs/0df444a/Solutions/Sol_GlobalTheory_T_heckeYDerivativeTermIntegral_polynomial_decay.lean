-- Prove2me | solution 1 for GlobalTheory.T.heckeYDerivativeTermIntegral_polynomial_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:21.499214+00:00
-- url     : https://prove2.me/submissions/9528e98c-589f-49be-9089-c5c352e87455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecay
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecayStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_intT_bound


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.intT_bound | exact GlobalTheory.HeckeTwo.TermDecay.intT_bound | (intros; apply GlobalTheory.HeckeTwo.TermDecay.intT_bound <;> assumption)
end _root_.GlobalTheory.T

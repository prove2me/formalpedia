-- Prove2me | solution 1 for GlobalTheory.T.integrable_heckeTermDecayIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:14:56.48928+00:00
-- url     : https://prove2.me/submissions/e603bceb-21d8-4612-9ca7-def25044390e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrandStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_integrable_qZ


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
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | exact GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.integrable_qZ <;> assumption)
end _root_.GlobalTheory.T

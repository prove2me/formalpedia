-- Prove2me | solution 1 for GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:24.780517+00:00
-- url     : https://prove2.me/submissions/e7b05194-0521-4200-a3a7-158a1baa941a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtHeckeTermDecayIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtHeckeTermDecayIntegrandStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_hasDerivAt_qZ


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
theorem _root_.solution : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | exact GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ <;> assumption)
end _root_.GlobalTheory.T

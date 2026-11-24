-- Prove2me | solution 1 for GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:34.906243+00:00
-- url     : https://prove2.me/submissions/99d60f4b-3a75-4f75-82be-1b7155392b4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLeStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_norm_intZ_le


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
theorem _root_.solution : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le | exact GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le | (intros; apply GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le <;> assumption)
end _root_.GlobalTheory.T

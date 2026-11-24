-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.intT_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:25.882608+00:00
-- url     : https://prove2.me/submissions/bb8686b8-af2a-45e8-91df-9d585bbdfed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeTermDecayFourierIntegralLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtHeckeTermDecayIntegrandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_intZ_decay
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_intT_eq_intZ


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
noncomputable section
open GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  intro K hK hKH a b m hab N
  obtain ⟨C, hC⟩ := intZ_decay K hK hKH N (a : ℤ) b m (by exact_mod_cast hab)
  refine ⟨C, fun σ hσ ν y hν hy => ?_⟩
  rw [intT_eq_intZ]
  have := hC σ hσ ν y hν hy
  simpa using this
end GlobalTheory.HeckeTwo.TermDecay

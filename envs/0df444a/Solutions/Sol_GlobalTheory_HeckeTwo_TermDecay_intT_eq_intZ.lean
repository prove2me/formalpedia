-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.intT_eq_intZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:40:22.216902+00:00
-- url     : https://prove2.me/submissions/2a440823-939a-4a82-b144-3468cf765071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_term_eq_qZ

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution (σ : ℂ) (ν : ℝ) (a b m : ℕ) (y : ℝ) :
    GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y = intZ σ ν (a : ℤ) b m y := by
  unfold GlobalTheory.HeckeTwo.TermSmooth.intT intZ
  simp_rw [term_eq_qZ]
end GlobalTheory.HeckeTwo.TermDecay

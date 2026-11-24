-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.termQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:06.299045+00:00
-- url     : https://prove2.me/submissions/80d17c94-76c9-4787-8f86-ef30cad93c9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero

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
open GlobalTheory GlobalTheory.HeckeTwo
open MeasureTheory
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwo
theorem _root_.solution (σ : ℂ) (b ν : F) (z : Emb F → ℂ) : termQ σ b ν 0 z = fTerm σ z b ν := by
  unfold termQ fTerm
  simp only [Pi.zero_apply, iteratedDeriv_zero]
end GlobalTheory.HeckeTwo

-- Prove2me | solution 1 for GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:01.125661+00:00
-- url     : https://prove2.me/submissions/b075479e-b901-4549-8bd9-1b37d4d6ec79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOnStatement
import Theorems.Thm_GlobalTheory_eisSum_zero_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ),
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  DifferentiableOn ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 k 0) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.eisSum_zero_differentiableOn | exact GlobalTheory.eisSum_zero_differentiableOn | (intros; apply GlobalTheory.eisSum_zero_differentiableOn <;> assumption)
end _root_.GlobalTheory.T

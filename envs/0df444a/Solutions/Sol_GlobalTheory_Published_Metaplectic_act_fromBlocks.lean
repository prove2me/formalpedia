-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.act_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:39:52.610651+00:00
-- url     : https://prove2.me/submissions/db63f472-ad5f-4754-bad0-77024eadac5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Published.Metaplectic
theorem _root_.solution (A B C D : Matrix ι ι ℝ) (p q : ι → ℝ) :
    act (fromBlocks A B C D) (p, q) = (A *ᵥ p + B *ᵥ q, C *ᵥ p + D *ᵥ q) := by
  simp [act, Matrix.fromBlocks_mulVec]
end GlobalTheory.Published.Metaplectic

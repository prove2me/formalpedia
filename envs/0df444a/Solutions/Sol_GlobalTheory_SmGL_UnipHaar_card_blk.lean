-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.card_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:52.496853+00:00
-- url     : https://prove2.me/submissions/07fa4a2e-5665-4260-b50b-0aa056e1e777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (e : (Σ a, m a) ≃ n)
omit [LinearOrder α] [∀ a, DecidableEq (m a)] [DecidableEq n]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (p : α → Prop) [DecidablePred p] :
    Fintype.card {j : n // p (blk e j)} = ∑ b with p b, Fintype.card (m b) := by
  rw [Fintype.card_subtype, Finset.card_filter, ← e.sum_comp, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : p b <;> simp [h]
end GlobalTheory.SmGL.UnipHaar

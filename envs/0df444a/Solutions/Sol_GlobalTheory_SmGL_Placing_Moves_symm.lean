-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.Moves.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.119468+00:00
-- url     : https://prove2.me/submissions/2900ff6f-3f25-446c-a7b9-b61a7033d602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.Placing
namespace Moves
theorem _root_.solution {ι : Type} {e e' : ι ≃ n} {w : GL n R} (h : Moves e e' w) : Moves e' e w⁻¹ := by
  intro g x y
  rw [← h]
  congr 2
  group
end Moves
end GlobalTheory.SmGL.Placing

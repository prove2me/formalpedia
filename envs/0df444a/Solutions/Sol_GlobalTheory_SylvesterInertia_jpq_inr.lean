-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.jpq_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:34.569832+00:00
-- url     : https://prove2.me/submissions/f85d4a7d-f314-42de-b9f5-e752257f08e2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SylvesterInertia
theorem _root_.solution (a b : ℕ) (z : Fin b → ℂ) :
    star (inrMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inrMap a b z = -(star z ⬝ᵥ z) := by
  simp [inrMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, neg_mulVec, Finset.sum_neg_distrib]
end GlobalTheory.SylvesterInertia

-- Prove2me | solution 1 for GlobalTheory.UnitCase.exists_sumElim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:57.68543+00:00
-- url     : https://prove2.me/submissions/5c48e533-63b2-4960-b282-90ccef381d5e

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution (m : κ ⊕ κ →₀ ℕ) : ∃ A B : κ →₀ ℕ, m = Finsupp.sumElim A B :=
  ⟨m.comapDomain Sum.inl Sum.inl_injective.injOn, m.comapDomain Sum.inr Sum.inr_injective.injOn,
    by ext (x | x) <;> simp⟩
end GlobalTheory.UnitCase

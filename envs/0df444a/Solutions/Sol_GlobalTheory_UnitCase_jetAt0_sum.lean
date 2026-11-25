-- Prove2me | solution 1 for GlobalTheory.UnitCase.jetAt0_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:45.359937+00:00
-- url     : https://prove2.me/submissions/f6636d16-5109-4f02-94e1-132ad6636f8c

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_add

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
theorem _root_.solution {α : Type} (s : Finset α) (P : α → MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (∑ a ∈ s, P a) G = ∑ a ∈ s, jetAt0 (P a) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jetAt0_add, ih]
end GlobalTheory.UnitCase

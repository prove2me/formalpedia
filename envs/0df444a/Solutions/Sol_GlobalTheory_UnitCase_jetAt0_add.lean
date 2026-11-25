-- Prove2me | solution 1 for GlobalTheory.UnitCase.jetAt0_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:10.889957+00:00
-- url     : https://prove2.me/submissions/46e384db-dac7-4241-89de-8bd0e8b2d56a

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_eq_sum

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
theorem _root_.solution (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  rw [jetAt0_eq_sum (P + Q) G (P.support ∪ Q.support) MvPolynomial.support_add,
    jetAt0_eq_sum P G (P.support ∪ Q.support) Finset.subset_union_left,
    jetAt0_eq_sum Q G (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
end GlobalTheory.UnitCase

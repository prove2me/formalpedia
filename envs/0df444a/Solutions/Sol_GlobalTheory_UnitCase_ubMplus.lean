-- Prove2me | solution 1 for GlobalTheory.UnitCase.ubMplus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:14.725396+00:00
-- url     : https://prove2.me/submissions/52f741e5-c008-4b5d-9ddc-b157dd6816fc

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_ubUnit
import Theorems.Thm_GlobalTheory_UnitCase_constantCoeff_eq_zero
import Theorems.Thm_GlobalTheory_UnitCase_ubIntegral

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
theorem _root_.solution : UBMplus := by
  intro C _ _ v l hl h5 hvl hp n n0 y hn hy h1 H
  exact ubUnit C v l hl h5 hvl hp n n0 y hn hy h1 (constantCoeff_eq_zero H)
    (ubIntegral C v l hl h5 hvl hp n0 y (by omega) h1 H)
end GlobalTheory.UnitCase

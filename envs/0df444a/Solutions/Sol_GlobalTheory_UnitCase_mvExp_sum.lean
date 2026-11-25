-- Prove2me | solution 1 for GlobalTheory.UnitCase.mvExp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:02.655753+00:00
-- url     : https://prove2.me/submissions/0f284c5b-ddd9-4f52-9944-a3d6f2e74167

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mvExp_add
import Theorems.Thm_P2M_GlobalTheory_UnitCase_mvExp_zero__4a05052efa91

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
theorem _root_.solution [CharZero C] {ι : Type} (s : Finset ι) (a : ι → MvPowerSeries σ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mvExp (∑ i ∈ s, a i) = ∏ i ∈ s, mvExp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mvExp_add (ha i) (by simp [map_sum, ha]), ih]
end GlobalTheory.UnitCase

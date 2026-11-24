-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSubgroup.prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:54.894786+00:00
-- url     : https://prove2.me/submissions/2150b82a-cd7a-49cc-970b-fb1ada0736ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_rowE_eq
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_colE_eq
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_cenM_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSubgroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.HeisenbergSubgroup
theorem _root_.solution (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by
  rw [rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul]
  simp only [add_zero, zero_add, dotProduct_zero]
end GlobalTheory.RootEx.HeisenbergSubgroup

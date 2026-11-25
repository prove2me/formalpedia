-- Prove2me | solution 1 for GroundTheory.LocalField.ord_le_ord_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:20.766839+00:00
-- url     : https://prove2.me/submissions/22beecf1-7a8d-4c67-91e4-506ff23a3f33

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x ≤ ord y ↔ valuation K y ≤ valuation K x := by
  rw [← normalizedValuation_le_iff, normalizedValuation_eq_exp_ord hx,
    normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp, neg_le_neg_iff]
end GroundTheory.LocalField

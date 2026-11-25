-- Prove2me | solution 1 for GroundTheory.LocalField.valuation_algebraMap_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:29:33.518722+00:00
-- url     : https://prove2.me/submissions/da0e4e91-88cf-4e39-acca-246914bad0ee

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation

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
variable {F G : Type*} [Field F] [ValuativeRel F] [Field G] [ValuativeRel G] [Algebra F G]
  [ValuativeExtension F G]
namespace GroundTheory.LocalField
theorem _root_.solution (x y : F) :
    valuation G (algebraMap F G x) ≤ valuation G (algebraMap F G y) ↔
      valuation F x ≤ valuation F y := by
  rw [← (valuation G).vle_iff_le, ValuativeExtension.vle_iff_vle, (valuation F).vle_iff_le]
end GroundTheory.LocalField

-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.infiniteLocalNorm_mulSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:03.947929+00:00
-- url     : https://prove2.me/submissions/11828a26-9015-4436-9055-4106ca5e153e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_infiniteLocalNorm
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
omit [NumberField K]
open scoped Classical
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : InfinitePlace K) (w : v.placesOver L)
    (z : ((w : InfinitePlace L).Completion)ˣ) :
    infiniteLocalNorm L v (Pi.mulSingle w z) =
      LocalField.normUnits v.Completion (w : InfinitePlace L).Completion z := by
  ext
  rw [coe_infiniteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    LocalField.coe_normUnits]
end GroundTheory.Global.IdeleNorm

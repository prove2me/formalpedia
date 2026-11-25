-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.finiteLocalNorm_mulSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:57.334407+00:00
-- url     : https://prove2.me/submissions/54797a80-018e-4ded-a1cc-b5b46a446f82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_finiteLocalNorm
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
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (PlacesOver L v)]
    (w : PlacesOver L v) (z : (w.1.adicCompletion L)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w z) =
      LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L) z := by
  ext
  rw [coe_finiteLocalNorm, Fintype.prod_eq_single w fun w' hw' ↦ by
    rw [Pi.mulSingle_eq_of_ne hw', Units.val_one, map_one], Pi.mulSingle_eq_same,
    LocalField.coe_normUnits]
end GroundTheory.Global.IdeleNorm

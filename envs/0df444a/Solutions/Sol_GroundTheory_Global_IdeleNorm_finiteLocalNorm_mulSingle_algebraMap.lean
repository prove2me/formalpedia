-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.finiteLocalNorm_mulSingle_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:48.624737+00:00
-- url     : https://prove2.me/submissions/a0ea3c24-0abc-40ca-a710-b50d9459577c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mulSingle
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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    [DecidableEq (PlacesOver L v)] (w : PlacesOver L v) (a : (v.adicCompletion K)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w (Units.map (algebraMap (v.adicCompletion K)
      (w.1.adicCompletion L) : v.adicCompletion K →* w.1.adicCompletion L) a)) =
        a ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [finiteLocalNorm_mulSingle]
  apply Units.ext
  rw [LocalField.coe_normUnits, Units.coe_map, Units.val_pow_eq_pow_val]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (a : v.adicCompletion K)
end GroundTheory.Global.IdeleNorm

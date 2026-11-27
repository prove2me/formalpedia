-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.isOpen_range_finiteLocalNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:38.112804+00:00
-- url     : https://prove2.me/submissions/b48cd88e-3010-46ac-887f-6705b6947bf9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mulSingle
import Theorems.Thm_GroundTheory_Global_nonempty_placesOver
import Theorems.Thm_GroundTheory_LocalField_isOpen_range_normUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((finiteLocalNorm L v).range : Set (v.adicCompletion K)ˣ) := by
  classical
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine Subgroup.isOpen_mono ?_
    (LocalField.isOpen_range_normUnits (v.adicCompletion K) (w.1.adicCompletion L))
  rintro _ ⟨z, rfl⟩
  exact ⟨Pi.mulSingle w z, finiteLocalNorm_mulSingle v w z⟩
end GroundTheory.Global.IdeleNorm

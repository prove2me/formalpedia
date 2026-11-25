-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.infiniteModule_diagonal_unitsToUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:07.61208+00:00
-- url     : https://prove2.me/submissions/490e86b0-91c4-4230-9aab-0c75b2b63d89

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_unitsToUnits_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteModule_eq_one_of_mem


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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (u : (𝓞 K)ˣ) :
    infiniteModule (diagonal K (unitsToUnits K u)) = 1 := by
  have h := congrArg Subtype.val (ideleModule_diagonal (unitsToUnits K u))
  rwa [ideleModule_apply, finiteModule_eq_one_of_mem (diagonal_unitsToUnits_mem K u), mul_one,
    Positive.val_one] at h
end GroundTheory.Global.IdeleGroup

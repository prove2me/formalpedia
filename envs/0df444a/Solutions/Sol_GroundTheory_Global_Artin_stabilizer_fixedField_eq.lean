-- Prove2me | solution 1 for GroundTheory.Global.Artin.stabilizer_fixedField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:25:12.542444+00:00
-- url     : https://prove2.me/submissions/b77272a7-04b8-4cb9-b368-fa1da838361c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_smul_ideal
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_subfieldInfinitePlaceEquiv_mk
import Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk
attribute [local simp] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


attribute [local simp] GroundTheory.Global.Artin.fixedFieldMulEquiv_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
omit [IsGalois K L]
namespace GroundTheory.Global.Artin
theorem _root_.solution (P : Ideal (𝓞 L)) :
    MulAction.stabilizer Gal(L/fixedField H) P =
      (MulAction.stabilizer H P).map (fixedFieldMulEquiv H).toMonoidHom := by
  ext σ
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    ← fixedFieldMulEquiv_smul_ideal, MulEquiv.apply_symm_apply]
end GroundTheory.Global.Artin

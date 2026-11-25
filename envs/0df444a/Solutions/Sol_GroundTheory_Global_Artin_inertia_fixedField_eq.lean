-- Prove2me | solution 1 for GroundTheory.Global.Artin.inertia_fixedField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:32.165684+00:00
-- url     : https://prove2.me/submissions/a959a6c4-f9ea-40f5-9d0a-09329b770944

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_Artin_fixedFieldMulEquiv_smul_ringOfIntegers
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
    P.inertia Gal(L/fixedField H) = (P.inertia H).map (fixedFieldMulEquiv H).toMonoidHom := by
  ext σ
  rw [Subgroup.mem_map_equiv]
  change (∀ y, σ • y - y ∈ P) ↔ ∀ y, (fixedFieldMulEquiv H).symm σ • y - y ∈ P
  simp_rw [← fixedFieldMulEquiv_smul_ringOfIntegers, MulEquiv.apply_symm_apply]
end GroundTheory.Global.Artin

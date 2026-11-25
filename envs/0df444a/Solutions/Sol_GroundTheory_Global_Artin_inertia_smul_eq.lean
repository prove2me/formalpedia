-- Prove2me | solution 1 for GroundTheory.Global.Artin.inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:41:19.194105+00:00
-- url     : https://prove2.me/submissions/b821eccf-9871-45c3-a7a5-d4a8516bf1b7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobeniusEmbed
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
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
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


attribute [local simp] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
omit [NumberField K] [NumberField L] [IsGalois K L]
namespace GroundTheory.Global.Artin
theorem _root_.solution (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    (x • P).inertia H =
      (MulAut.conj x • P.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff, ← Ideal.coe_mem_inertia, mem_inertia_smul_iff]
end GroundTheory.Global.Artin

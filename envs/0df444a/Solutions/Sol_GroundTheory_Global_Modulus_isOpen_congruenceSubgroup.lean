-- Prove2me | solution 1 for GroundTheory.Global.Modulus.isOpen_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:56.968432+00:00
-- url     : https://prove2.me/submissions/8bbaf24f-3ea1-488c-905a-187b8469f645

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_positiveAt
import Theorems.Thm_GroundTheory_Global_Modulus_finite_support_exponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_finiteLevel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution : IsOpen (𝔪.congruenceSubgroup : Set (IdeleGroup K)) := by
  rw [congruenceSubgroup, Subgroup.coe_inf, Subgroup.coe_comap]
  refine IsOpen.inter ?_ (isOpen_positiveAt _)
  exact (isOpen_finiteLevel 𝔪.finite_support_exponent).preimage (continuous_toFinite K)
end GroundTheory.Global.Modulus

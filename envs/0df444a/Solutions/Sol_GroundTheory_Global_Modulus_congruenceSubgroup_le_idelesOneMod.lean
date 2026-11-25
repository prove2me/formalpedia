-- Prove2me | solution 1 for GroundTheory.Global.Modulus.congruenceSubgroup_le_idelesOneMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:56.95955+00:00
-- url     : https://prove2.me/submissions/6e3186f8-6d63-4d31-95c1-60582b945527

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_eq_inf

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
theorem _root_.solution : 𝔪.congruenceSubgroup ≤ 𝔪.idelesOneMod := by
  rw [congruenceSubgroup_eq_inf]
  exact inf_le_left
end GroundTheory.Global.Modulus

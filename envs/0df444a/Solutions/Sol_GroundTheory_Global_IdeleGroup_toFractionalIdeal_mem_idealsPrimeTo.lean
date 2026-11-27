-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.toFractionalIdeal_mem_idealsPrimeTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:31.334506+00:00
-- url     : https://prove2.me/submissions/48ef98f7-a74e-4b7e-b825-fbb6f48cee40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ord_eq_zero_of_mem_unitsLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K}
    (hx : x ∈ primeToLevel 𝔪) : toFractionalIdeal x ∈ idealsPrimeTo 𝔪 := by
  intro v hv
  rw [count_toFractionalIdeal]
  exact ord_eq_zero_of_mem_unitsLevel ((mem_primeToLevel.1 hx).2 v hv)
end GroundTheory.Global.IdeleGroup

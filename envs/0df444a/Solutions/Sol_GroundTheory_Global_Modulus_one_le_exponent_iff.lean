-- Prove2me | solution 1 for GroundTheory.Global.Modulus.one_le_exponent_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:23:25.411588+00:00
-- url     : https://prove2.me/submissions/9d63324f-df76-4498-89a3-3858a8dac0c9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_exponent_eq_zero_iff

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
omit [NumberField K]
namespace GroundTheory.Global.Modulus
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ 𝔪.exponent v ↔ v.asIdeal ∣ 𝔪.ideal := by
  rw [Nat.one_le_iff_ne_zero, Ne, exponent_eq_zero_iff, not_not]
end GroundTheory.Global.Modulus

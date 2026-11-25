-- Prove2me | solution 1 for GroundTheory.Global.Modulus.exponent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:22.63947+00:00
-- url     : https://prove2.me/submissions/4d5dfd4f-2d38-459a-9cea-d2476e803db1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup

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
    𝔪.exponent v = 0 ↔ ¬ v.asIdeal ∣ 𝔪.ideal :=
  multiplicity_eq_zero
end GroundTheory.Global.Modulus

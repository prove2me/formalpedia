-- Prove2me | solution 1 for GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:38.553943+00:00
-- url     : https://prove2.me/submissions/8934372f-463f-4563-95ac-4359cfeb90a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution (x : IdeleGroup K) :
    𝔪.quotientMapCongruenceEquiv (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      (QuotientGroup.mk x : 𝔪.RayClassGroup) :=
  rfl
end GroundTheory.Global.Modulus

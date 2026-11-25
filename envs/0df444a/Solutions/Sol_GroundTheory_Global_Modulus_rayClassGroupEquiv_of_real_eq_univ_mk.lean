-- Prove2me | solution 1 for GroundTheory.Global.Modulus.rayClassGroupEquiv_of_real_eq_univ_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:26.842006+00:00
-- url     : https://prove2.me/submissions/ad62ab45-380b-482a-ac23-00f70bf0e35f

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
theorem _root_.solution (h : 𝔪.real = Set.univ) (x : IdeleGroup K) :
    𝔪.rayClassGroupEquiv_of_real_eq_univ h (QuotientGroup.mk x) =
      (QuotientGroup.mk x : _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal) :=
  rfl
end GroundTheory.Global.Modulus

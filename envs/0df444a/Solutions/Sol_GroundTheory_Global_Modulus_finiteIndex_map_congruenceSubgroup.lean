-- Prove2me | solution 1 for GroundTheory.Global.Modulus.finiteIndex_map_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:31.406349+00:00
-- url     : https://prove2.me/submissions/f7a48088-9bf0-4889-8a81-62ff88033aa0

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
theorem _root_.solution :
    (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).FiniteIndex := by
  have : Finite (IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)) :=
    Finite.of_equiv _ 𝔪.quotientMapCongruenceEquiv.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient
end GroundTheory.Global.Modulus

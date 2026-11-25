-- Prove2me | solution 1 for GroundTheory.LocalField.irreducible_map_of_isEisensteinAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:34.320732+00:00
-- url     : https://prove2.me/submissions/feddbcf1-b481-4110-87f4-add30d4a87c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_isPrimitive_of_isEisensteinAt
import Theorems.Thm_GroundTheory_LocalField_irreducible_of_isEisensteinAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap 𝒪[K] K)) :=
  (isPrimitive_of_isEisensteinAt hf).irreducible_iff_irreducible_map_fraction_map.mp
    (irreducible_of_isEisensteinAt hf hn)
end GroundTheory.LocalField

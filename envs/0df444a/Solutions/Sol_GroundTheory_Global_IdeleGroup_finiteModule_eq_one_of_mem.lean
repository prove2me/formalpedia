-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteModule_eq_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:45.687569+00:00
-- url     : https://prove2.me/submissions/305f449f-e7e9-4388-a979-34e30d7a4204

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {x : IdeleGroup K} (hx : x ∈ standardOpenSubgroup K) :
    finiteModule x = 1 :=
  finprod_eq_one_of_forall_eq_one fun v ↦
    norm_eq_one_of_mul_eq_one (finite_mul_inv x v) ((mem_standardOpenSubgroup K).1 hx v).1
      ((mem_standardOpenSubgroup K).1 hx v).2
end GroundTheory.Global.IdeleGroup

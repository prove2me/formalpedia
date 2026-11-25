-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.ofFinite_mul_ofInfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:41.582858+00:00
-- url     : https://prove2.me/submissions/12bb92d6-e431-446f-b6a1-0fe452aa3353

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : IdeleGroup K) :
    ofFinite (toFinite K x) * ofInfinite (toInfinite K x) = x := by
  apply (prodEquiv K).injective
  refine Prod.ext ?_ ?_
  · change toInfinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toInfinite K x
    rw [map_mul, toInfinite_ofFinite, toInfinite_ofInfinite, one_mul]
  · change toFinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toFinite K x
    rw [map_mul, toFinite_ofFinite, toFinite_ofInfinite, mul_one]
end GroundTheory.Global.IdeleGroup

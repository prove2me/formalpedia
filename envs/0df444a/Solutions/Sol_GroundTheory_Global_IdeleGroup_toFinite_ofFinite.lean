-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.toFinite_ofFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:05.468813+00:00
-- url     : https://prove2.me/submissions/8921f96d-fb6a-4de3-861e-20d9b6ae6890

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal

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
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toFinite K (ofFinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x
  rw [ContinuousMulEquiv.apply_symm_apply]
end GroundTheory.Global.IdeleGroup

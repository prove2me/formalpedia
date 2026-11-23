-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_ofFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:06.426097+00:00
-- url     : https://prove2.me/submissions/cc0c56f9-ce6c-4cb4-b178-cfe566248220

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
theorem _root_.solution : Continuous (ofFinite (K := K)) := by
  have : Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x) :=
    (ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)
  exact this
end GroundTheory.Global.IdeleGroup

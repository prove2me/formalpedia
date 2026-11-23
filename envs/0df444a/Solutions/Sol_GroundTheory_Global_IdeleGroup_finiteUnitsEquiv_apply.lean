-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:38.013796+00:00
-- url     : https://prove2.me/submissions/7301f05e-d129-4405-a35f-af709fe9d252

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted

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
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteUnitsEquiv K x v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl
end GroundTheory.Global.IdeleGroup

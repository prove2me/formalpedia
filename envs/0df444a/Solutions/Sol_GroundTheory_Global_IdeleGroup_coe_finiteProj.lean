-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_finiteProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:28.186352+00:00
-- url     : https://prove2.me/submissions/32afc7f3-050b-4f01-9a06-31bbfa3104da

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : 𝔸[K]).2 v :=
  rfl
end GroundTheory.Global.IdeleGroup

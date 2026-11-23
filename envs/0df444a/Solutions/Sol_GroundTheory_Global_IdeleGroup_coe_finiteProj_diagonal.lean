-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:29.447805+00:00
-- url     : https://prove2.me/submissions/6c99b2a9-0bd6-4733-b3dc-cd6c66ec7a0a

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) :=
  rfl
end GroundTheory.Global.IdeleGroup

-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isOpen_integralAtFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:24.228334+00:00
-- url     : https://prove2.me/submissions/6dc3aaed-8e7b-4b74-9662-9311832d6e1e

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
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : IsOpen (integralAtFinite K : Set 𝔸[K]) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 K) ↦
    Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage continuous_snd
end GroundTheory.Global.IdeleGroup

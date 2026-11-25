-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.mem_integralAtFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:25.648331+00:00
-- url     : https://prove2.me/submissions/0be2bf10-52f7-473b-a226-6593ae243f9d

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
theorem _root_.solution {a : 𝔸[K]} :
    a ∈ integralAtFinite K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl
end GroundTheory.Global.IdeleGroup

-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.ideleModule_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:48.8097+00:00
-- url     : https://prove2.me/submissions/9325e71a-8d32-4a40-93d9-8d68444a5bd0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms

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
theorem _root_.solution (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = (∏ w : InfinitePlace K, ‖(x : 𝔸[K]).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸[K]).2 v‖ :=
  rfl
end GroundTheory.Global.IdeleGroup

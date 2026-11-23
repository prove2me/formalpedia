-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isOpen_units_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:09.44117+00:00
-- url     : https://prove2.me/submissions/e67458ef-3b83-4c21-bf13-40fb43528bfa

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion K))
end GroundTheory.Global.IdeleGroup

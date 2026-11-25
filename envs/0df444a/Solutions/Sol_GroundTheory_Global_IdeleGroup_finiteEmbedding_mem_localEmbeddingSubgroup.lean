-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteEmbedding_mem_localEmbeddingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:31.741275+00:00
-- url     : https://prove2.me/submissions/59f3f718-70f1-4087-9092-992369dada6a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique

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
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)
end GroundTheory.Global.IdeleGroup

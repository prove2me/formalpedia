-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.index_comap_sUnitsToSIdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:03.829284+00:00
-- url     : https://prove2.me/submissions/3ca741c0-cc82-4f7b-b7dc-871a97d58531

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexFormula

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
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (W : Subgroup (sIdeles S)) :
    (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by
  rw [Subgroup.index_comap, range_sUnitsToSIdeles]
end GroundTheory.Global.IdeleGroup

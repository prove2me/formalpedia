-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.index_map_mul_index_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:37.44607+00:00
-- url     : https://prove2.me/submissions/edc1137c-65de-4ba2-b41d-26d9a60cc2db

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexFormula
import Theorems.Thm_GroundTheory_Global_index_map_mul_relIndex_ker
import Theorems.Thm_GroundTheory_Global_IdeleGroup_index_comap_sUnitsToSIdeles

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
theorem _root_.solution (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (W : Subgroup (sIdeles S)) :
    (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index =
      W.index := by
  rw [index_comap_sUnitsToSIdeles]
  exact index_map_mul_relIndex_ker ((sIdelesToIdeleClassGroup_surjective_iff S).2 h) W
end GroundTheory.Global.IdeleGroup

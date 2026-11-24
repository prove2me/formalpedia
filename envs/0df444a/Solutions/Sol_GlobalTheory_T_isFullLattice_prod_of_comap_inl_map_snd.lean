-- Prove2me | solution 1 for GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:34.578122+00:00
-- url     : https://prove2.me/submissions/ac19fbf4-ff28-4aa6-b3ff-84b516458766

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSndStatement
import Theorems.Thm_GlobalTheory_UnitLemma_isLat_of_comap_inl_of_map_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by
  first | exact @GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | exact GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | (intros; apply GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.augMap_grMk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:34.540779+00:00
-- url     : https://prove2.me/submissions/eef895d8-b682-4374-96ba-be1907a566e6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_augMap_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_smul_grMk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (m : G → S.F n) :
    augMap G (S.gr n) (fun g => S.grMk n (m g)) = S.grMk n (augMap G (S.F n) m) := by
  rw [augMap_apply, augMap_apply, map_prod]
  simp only [map_div, smul_grMk]
end GroundTheory.LocalField.StableFiltration

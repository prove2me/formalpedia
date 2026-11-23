-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.coe_augMap_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.684475+00:00
-- url     : https://prove2.me/submissions/661d20d9-f695-4406-912e-672e30ef04d0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_augMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (m : G → S.F n) :
    ((augMap G (S.F n) m : S.F n) : V) = augMap G V (fun g => (m g : V)) := by
  rw [augMap_apply, augMap_apply, SubmonoidClass.coe_finsetProd]
  rfl
end GroundTheory.LocalField.StableFiltration

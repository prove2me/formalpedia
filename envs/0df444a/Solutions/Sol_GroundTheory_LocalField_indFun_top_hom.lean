-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_top_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:20.244199+00:00
-- url     : https://prove2.me/submissions/79616c26-61a2-4cad-818e-9bf10189e4af

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_indFun_comp_mulEquiv
import Theorems.Thm_GroundTheory_LocalField_indFun_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']
namespace GroundTheory.LocalField
theorem _root_.solution [Fintype (⊤ : Subgroup G)] (l : G →* ℂˣ) :
    indFun (⊤ : Subgroup G).subtype (fun k ↦ ((l.comp (⊤ : Subgroup G).subtype) k : ℂ)) =
      fun g ↦ (l g : ℂ) := by
  have h : (⊤ : Subgroup G).subtype = (MonoidHom.id G).comp Subgroup.topEquiv.toMonoidHom := by
    ext
    rfl
  rw [h, indFun_comp_mulEquiv]
  refine indFun_id fun g k ↦ ?_
  show ((l (k * g * k⁻¹) : ℂˣ) : ℂ) = l g
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
end GroundTheory.LocalField

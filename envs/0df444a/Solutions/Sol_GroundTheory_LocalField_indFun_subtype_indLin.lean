-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_subtype_indLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:18.615838+00:00
-- url     : https://prove2.me/submissions/86d18fbf-503f-430f-a5be-15dc03723798

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_indFun_comp_toMonoidHom
import Theorems.Thm_GroundTheory_LocalField_indFun_indFun


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
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]
variable {H H' : Type*} [Group H] [Fintype H] [Group H'] [Fintype H']
namespace GroundTheory.LocalField
theorem _root_.solution (K : Subgroup G) (L : Subgroup K) (μ : L →* ℂˣ) :
    indFun K.subtype (indLin L μ) = indLin (L.map K.subtype)
      (μ.comp (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom) := by
  set e := L.equivMapOfInjective K.subtype K.subtype_injective
  rw [indLin, indFun_indFun, indLin, ← indFun_comp_toMonoidHom _ e]
  congr 1
  ext l
  simp [e]
end GroundTheory.LocalField

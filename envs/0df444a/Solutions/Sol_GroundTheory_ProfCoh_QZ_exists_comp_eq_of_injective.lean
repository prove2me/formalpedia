-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.exists_comp_eq_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:44.534957+00:00
-- url     : https://prove2.me/submissions/580e156e-ecf3-46bd-80a9-b92b00569d9f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.QZDual.eval_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZ
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
namespace GroundTheory.ProfCoh.QZ
theorem _root_.solution (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    i hi (toAddCircle.toAddMonoidHom.comp f)
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp g, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hg a
  simp only [AddMonoidHom.coe_comp, comp_apply, AddEquiv.coe_toAddMonoidHom] at h1 ⊢
  rw [h1, AddEquiv.symm_apply_apply]
end GroundTheory.ProfCoh.QZ

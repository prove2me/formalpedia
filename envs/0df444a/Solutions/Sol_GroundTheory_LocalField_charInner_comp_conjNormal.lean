-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_comp_conjNormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:57.244925+00:00
-- url     : https://prove2.me/submissions/9c8f93a9-b061-435e-9e78-6312941d8212

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

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
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
namespace GroundTheory.LocalField
theorem _root_.solution [Fintype A] {χ : G → ℂ} (hχ : IsClassFun χ) (θ : A → ℂ) (g : G) :
    charInner A (χ ∘ A.subtype) (θ ∘ conjNormal A g) = charInner A (χ ∘ A.subtype) θ := by
  rw [charInner_apply, charInner_apply]
  congr 1
  refine Fintype.sum_equiv (conjNormal A g).toEquiv _ _ fun a ↦ ?_
  simp only [Function.comp_apply, Subgroup.coe_subtype, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, map_inv, coe_conjNormal]
  congr 1
  simpa using (hχ a g⁻¹).symm
end GroundTheory.LocalField

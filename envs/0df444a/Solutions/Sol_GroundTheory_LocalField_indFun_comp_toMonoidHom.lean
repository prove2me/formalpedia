-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_comp_toMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:39.985849+00:00
-- url     : https://prove2.me/submissions/1329192c-c9ac-4d26-9c27-042aab5fe1a3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan

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
theorem _root_.solution (φ : H →* G) (e : H' ≃* H) (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) (ψ ∘ e) = indFun φ ψ := by
  classical
  funext s
  simp only [indFun_apply]
  rw [Nat.card_congr e.toEquiv]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact Fintype.sum_equiv e.toEquiv _ _ fun h' ↦ by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    exact if_congr Iff.rfl rfl rfl
end GroundTheory.LocalField

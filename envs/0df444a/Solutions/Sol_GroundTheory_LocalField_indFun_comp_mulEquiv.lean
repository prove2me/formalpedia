-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_comp_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:50.137902+00:00
-- url     : https://prove2.me/submissions/3b916bca-e466-4de3-adc6-696cd89f9df3

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
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']
namespace GroundTheory.LocalField
theorem _root_.solution (φ : H' →* G) (e : H ≃* H') (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) ψ = indFun φ (ψ ∘ e.symm) := by
  funext s
  rw [indFun_apply, indFun_apply, Nat.card_congr e.toEquiv]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact Fintype.sum_equiv e.toEquiv _ _ fun h ↦ by split_ifs <;> simp_all
end GroundTheory.LocalField

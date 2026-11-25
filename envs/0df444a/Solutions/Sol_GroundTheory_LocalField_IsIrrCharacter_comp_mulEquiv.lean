-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.comp_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:32.19138+00:00
-- url     : https://prove2.me/submissions/ecec7d99-6090-4b0c-befc-98c61880c7b1

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
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {H H' : Type*} [Group H] [Group H'] {θ : H → ℂ}
    (hθ : IsIrrCharacter θ) (e : H' ≃* H) : IsIrrCharacter (θ ∘ e) := by
  obtain ⟨V, _, _, _, σ, hσ, rfl⟩ := hθ
  refine ⟨V, inferInstance, inferInstance, inferInstance, σ.comp e.toMonoidHom, ?_, rfl⟩
  let iso : Subrepresentation (σ.comp e.toMonoidHom) ≃o Subrepresentation σ :=
    { toFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ by
        have := U.apply_mem_toSubmodule (e.symm h) hv
        simpa using this⟩
      invFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ U.apply_mem_toSubmodule (e h) hv⟩
      left_inv := fun U ↦ rfl
      right_inv := fun U ↦ rfl
      map_rel_iff' := Iff.rfl }
  exact iso.isSimpleOrder_iff.mpr hσ
end IsIrrCharacter
end GroundTheory.LocalField

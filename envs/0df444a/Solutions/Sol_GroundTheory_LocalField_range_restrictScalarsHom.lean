-- Prove2me | solution 1 for GroundTheory.LocalField.range_restrictScalarsHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:43.569508+00:00
-- url     : https://prove2.me/submissions/d7499038-a66e-4939-ba22-97c22c60c0df

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex

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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
namespace GroundTheory.LocalField
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range = M.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ m hm
    exact τ.commutes ⟨m, hm⟩
  · intro h
    refine ⟨{ σ with commutes' := fun m ↦ h m m.2 }, ?_⟩
    ext x
    rfl
end GroundTheory.LocalField

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_restrictAut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:41.037493+00:00
-- url     : https://prove2.me/submissions/0fe4b9e8-1407-4a49-aeec-3f573dc3a091

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] (y : N) :
    ((restrictAut Ω τ N hN y : N) : E) = ((τ ⟨y, hN y.2⟩ : Ω) : E) := by
  have : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  set e := IntermediateField.restrictAlgEquiv hN
  have he : ∀ w : N, ((e w : IntermediateField.restrict hN) : Ω) = ⟨w, hN w.2⟩ := fun w => rfl
  set z := τ.restrictNormal (IntermediateField.restrict hN) (e y)
  have h1 : ((z : IntermediateField.restrict hN) : Ω) = τ ⟨y, hN y.2⟩ := by
    have := AlgEquiv.restrictNormal_commutes τ (IntermediateField.restrict hN) (e y)
    rw [← he y]
    exact this
  change ((e.symm z : N) : E) = _
  have h2 : ((e (e.symm z) : IntermediateField.restrict hN) : Ω) = ⟨(e.symm z : E), hN (e.symm z).2⟩ :=
    he _
  rw [AlgEquiv.apply_symm_apply, h1] at h2
  exact (congrArg Subtype.val h2).symm
end GroundTheory.PAdicHodge

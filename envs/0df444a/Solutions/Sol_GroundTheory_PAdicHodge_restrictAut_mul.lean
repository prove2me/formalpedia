-- Prove2me | solution 1 for GroundTheory.PAdicHodge.restrictAut_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:22:00.461892+00:00
-- url     : https://prove2.me/submissions/b2efc2d8-e2a7-42e0-92b1-7a5c0e1d3694

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
theorem solution (Ω : IntermediateField F E) (τ₁ τ₂ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] :
    restrictAut Ω (τ₁ * τ₂) N hN = restrictAut Ω τ₁ N hN * restrictAut Ω τ₂ N hN := by
  haveI : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  unfold restrictAut
  have h : (τ₁ * τ₂).restrictNormal (IntermediateField.restrict hN) =
      τ₁.restrictNormal (IntermediateField.restrict hN) * τ₂.restrictNormal (IntermediateField.restrict hN) :=
    (AlgEquiv.restrictNormalHom (IntermediateField.restrict hN)).map_mul τ₁ τ₂
  rw [h]
  ext x
  simp [AlgEquiv.mul_apply]

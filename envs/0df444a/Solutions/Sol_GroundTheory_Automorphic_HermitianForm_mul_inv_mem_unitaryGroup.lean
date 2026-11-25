-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mul_inv_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:50.440789+00:00
-- url     : https://prove2.me/submissions/27a5be75-ce98-42fe-9186-ec659cf2e848

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_inv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
omit [FiniteDimensional E V]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution {a b : V ≃ₗ[E] V}
    (hab : h.adjointEquiv a * a = h.adjointEquiv b * b) : b * a⁻¹ ∈ h.unitaryGroup := by
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, adjointEquiv_mul, adjointEquiv_inv]
  calc (h.adjointEquiv a)⁻¹ * h.adjointEquiv b * (b * a⁻¹)
      = (h.adjointEquiv a)⁻¹ * (h.adjointEquiv b * b) * a⁻¹ := by group
    _ = 1 := by rw [← hab]; group
end GroundTheory.Automorphic.HermitianForm

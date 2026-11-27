-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.normTorus_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:42.263206+00:00
-- url     : https://prove2.me/submissions/a3b2c3dc-5d97-4a74-aa14-b456779c1e1f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_torusStar_torusStar
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_selfAdjointTorus

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
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution : h.normTorus γ ≤ h.selfAdjointTorus γ := by
  rintro _ ⟨t, rfl⟩
  rw [mem_selfAdjointTorus, torusNorm_apply, map_mul, torusStar_torusStar, mul_comm]
end GroundTheory.Automorphic.HermitianForm

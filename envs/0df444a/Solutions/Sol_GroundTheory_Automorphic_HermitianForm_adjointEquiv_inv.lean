-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.adjointEquiv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:22.826679+00:00
-- url     : https://prove2.me/submissions/f0caf6df-1160-4689-a63c-2f6bfbc2e9c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_one

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
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (a : V ≃ₗ[E] V) : h.adjointEquiv a⁻¹ = (h.adjointEquiv a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← adjointEquiv_mul, mul_inv_cancel, adjointEquiv_one]
end GroundTheory.Automorphic.HermitianForm

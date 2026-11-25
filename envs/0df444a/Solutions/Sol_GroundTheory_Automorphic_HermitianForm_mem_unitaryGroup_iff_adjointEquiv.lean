-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup_iff_adjointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:51.933739+00:00
-- url     : https://prove2.me/submissions/627666b6-01ba-4121-b587-68c936930836

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
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
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔ h.adjointEquiv g = g⁻¹ := by
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, mul_eq_one_iff_eq_inv]
end GroundTheory.Automorphic.HermitianForm

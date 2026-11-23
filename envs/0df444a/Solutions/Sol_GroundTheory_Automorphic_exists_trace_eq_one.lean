-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_trace_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.912728+00:00
-- url     : https://prove2.me/submissions/050a93fd-0f83-4648-b82b-b99d1d89e9fd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution [Algebra.IsSeparable F E] : ∃ c : E, Algebra.trace F E c = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace F E x ≠ 0 := by
    by_contra H
    push Not at H
    exact Algebra.trace_ne_zero F E (LinearMap.ext H)
  refine ⟨(Algebra.trace F E x)⁻¹ • x, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
end GroundTheory.Automorphic

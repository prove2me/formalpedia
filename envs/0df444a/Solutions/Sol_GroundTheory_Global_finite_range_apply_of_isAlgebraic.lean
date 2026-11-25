-- Prove2me | solution 1 for GroundTheory.Global.finite_range_apply_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:43.256989+00:00
-- url     : https://prove2.me/submissions/22cc2baa-93b7-47ce-a8f3-1ec275a0af8b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
variable [CharZero Ω]
omit [IsAlgClosed Ω]
namespace GroundTheory.Global
theorem _root_.solution {x : Ω} (hx : IsAlgebraic ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite := by
  refine ((minpoly ℚ x).rootSet_finite Ω).subset ?_
  rintro _ ⟨σ, rfl⟩
  rw [mem_rootSet]
  refine ⟨minpoly.ne_zero hx.isIntegral, ?_⟩
  have := Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toRatAlgHom x (minpoly ℚ x)
  rw [minpoly.aeval, map_zero] at this
  simpa using this
end GroundTheory.Global

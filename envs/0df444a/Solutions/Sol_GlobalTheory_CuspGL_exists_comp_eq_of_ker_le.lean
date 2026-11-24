-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_comp_eq_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:57.756855+00:00
-- url     : https://prove2.me/submissions/dc058914-b2a8-4711-8fd0-fd15f4661682

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {U X Y : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] (p : U →ₗ[F] X) (f : U →ₗ[F] Y)
    (h : LinearMap.ker p ≤ LinearMap.ker f) : ∃ k : X →ₗ[F] Y, ∀ u, k (p u) = f u := by
  obtain ⟨k, hk⟩ := LinearMap.exists_extend
    (((LinearMap.ker p).liftQ f h) ∘ₗ p.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun u => ?_⟩
  have := LinearMap.congr_fun hk ⟨p u, LinearMap.mem_range_self p u⟩
  simpa using this
end GlobalTheory.CuspGL

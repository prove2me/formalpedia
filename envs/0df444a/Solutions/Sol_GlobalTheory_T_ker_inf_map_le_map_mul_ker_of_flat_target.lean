-- Prove2me | solution 1 for GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:57.342173+00:00
-- url     : https://prove2.me/submissions/81c0ddd8-e4ee-40a9-9b0d-6e5a0efaeca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTarget
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTargetStatement
import Theorems.Thm_GlobalTheory_ker_inf_map_le_map_mul_ker_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  first | exact @GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | exact GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | (intros; apply GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat <;> assumption)
end _root_.GlobalTheory.T

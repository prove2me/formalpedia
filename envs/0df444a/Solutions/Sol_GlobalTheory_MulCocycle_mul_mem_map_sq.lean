-- Prove2me | solution 1 for GlobalTheory.MulCocycle.mul_mem_map_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:27.119693+00:00
-- url     : https://prove2.me/submissions/9b8c6881-da74-460d-b31b-678c333340e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle
variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.MulCocycle
theorem _root_.solution {C : Type*} [CommRing C] [Algebra B C] {J : Ideal B} {a b : C}
    (ha : a ∈ J.map (algebraMap B C)) (hb : b ∈ J.map (algebraMap B C)) :
    a * b ∈ (J ^ 2).map (algebraMap B C) := by
  rw [Ideal.map_pow, pow_two]
  exact Ideal.mul_mem_mul ha hb
end GlobalTheory.MulCocycle

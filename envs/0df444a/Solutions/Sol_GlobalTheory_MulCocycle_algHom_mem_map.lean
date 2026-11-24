-- Prove2me | solution 1 for GlobalTheory.MulCocycle.algHom_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:24.950345+00:00
-- url     : https://prove2.me/submissions/15aa0d3a-5fd4-41e2-a43b-1c4351c4b331

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
theorem _root_.solution {C C' : Type*} [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    {J : Ideal B} (φ : C →ₐ[B] C') {a : C} (ha : a ∈ J.map (algebraMap B C)) :
    φ a ∈ J.map (algebraMap B C') := by
  have := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
end GlobalTheory.MulCocycle

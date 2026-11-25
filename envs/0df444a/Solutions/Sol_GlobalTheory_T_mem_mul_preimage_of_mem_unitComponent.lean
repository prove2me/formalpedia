-- Prove2me | solution 1 for GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:29.963348+00:00
-- url     : https://prove2.me/submissions/0aee1ff7-c038-4263-8066-c1e2d7d4096f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
import Theorems.Thm_GlobalTheory_mem_unitComponent_mul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (η[G]).left (G.hom y) ∈ U → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.mem_unitComponent_mul_mem | exact GlobalTheory.mem_unitComponent_mul_mem | (intros; apply GlobalTheory.mem_unitComponent_mul_mem <;> assumption)
end _root_.GlobalTheory.T

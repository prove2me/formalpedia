-- Prove2me | solution 1 for GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:19.122068+00:00
-- url     : https://prove2.me/submissions/5c7d118b-48b9-49b4-8f14-eea80706f009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMemStatement
import Theorems.Thm_GlobalTheory_IdCompMul_mul_mem


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompMul.mul_mem | exact GlobalTheory.IdCompMul.mul_mem | (intros; apply GlobalTheory.IdCompMul.mul_mem <;> assumption)
end _root_.GlobalTheory.T

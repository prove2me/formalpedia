-- Prove2me | solution 1 for GlobalTheory.T.inv_mem_identity_component_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:09:23.911085+00:00
-- url     : https://prove2.me/submissions/f1ca524a-f7cf-43c3-a328-0bab29bd4c6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibreStatement
import Theorems.Thm_GlobalTheory_inv_mem_connectedComponentIn_fibre


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left), y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.inv_mem_connectedComponentIn_fibre | exact GlobalTheory.inv_mem_connectedComponentIn_fibre | (intros; apply GlobalTheory.inv_mem_connectedComponentIn_fibre <;> assumption)
end _root_.GlobalTheory.T

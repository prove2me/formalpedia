-- Prove2me | solution 1 for GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:18.383071+00:00
-- url     : https://prove2.me/submissions/b1cb91b3-40ef-4989-97b6-7259f3e3d468

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupSchemeStatement
import Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_identityComponent


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_identityComponent | exact GlobalTheory.IdCompOpen.isOpen_identityComponent | (intros; apply GlobalTheory.IdCompOpen.isOpen_identityComponent <;> assumption)
end _root_.GlobalTheory.T

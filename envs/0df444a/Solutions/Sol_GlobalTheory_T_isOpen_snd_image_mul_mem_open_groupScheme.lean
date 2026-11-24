-- Prove2me | solution 1 for GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:04.776274+00:00
-- url     : https://prove2.me/submissions/49c86b00-3bb1-49ef-b1d4-b67f9a213943

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
import Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_snd_image


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens, IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_snd_image | exact GlobalTheory.IdCompOpen.isOpen_snd_image | (intros; apply GlobalTheory.IdCompOpen.isOpen_snd_image <;> assumption)
end _root_.GlobalTheory.T

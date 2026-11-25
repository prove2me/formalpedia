-- Prove2me | solution 1 for GlobalTheory.IdCompOpen.isOpen_identityComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:30.957801+00:00
-- url     : https://prove2.me/submissions/def81f9d-9c22-4e1d-a796-74caa8c5cd87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponentsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
import Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_sectionComponents_of_family
import Theorems.Thm_GlobalTheory_T_isOpen_snd_image_mul_mem_open_groupScheme
import Theorems.Thm_GlobalTheory_T_mem_mul_preimage_of_mem_unitComponent
import Theorems.Thm_GlobalTheory_T_mem_unitComponent_of_mul_mem


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
open GlobalTheory GlobalTheory.IdCompOpen
namespace GlobalTheory.IdCompOpen
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hG
  exact isOpen_sectionComponents_of_family G.left S G.hom (η[G]).left hG (Over.w (η[G]))
    (fun U => {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y})
    (GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme S G hG) (GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent S G hG) (GlobalTheory.T.mem_unitComponent_of_mul_mem S G hG)
end GlobalTheory.IdCompOpen

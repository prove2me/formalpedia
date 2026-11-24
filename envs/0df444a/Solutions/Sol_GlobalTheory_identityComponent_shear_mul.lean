-- Prove2me | solution 1 for GlobalTheory.identityComponent_shear_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:15.248908+00:00
-- url     : https://prove2.me/submissions/eea2cb21-2cfb-4839-8940-03cec39cd2ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInv

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = snd G G := by
  have h1 : lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = (fst G G)⁻¹ * (fst G G * snd G G) := by
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.inv_def]
  rw [h1, inv_mul_cancel_left]
end GlobalTheory

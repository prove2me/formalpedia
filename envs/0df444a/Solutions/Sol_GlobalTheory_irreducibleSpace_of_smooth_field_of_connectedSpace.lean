-- Prove2me | solution 1 for GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:35.688803+00:00
-- url     : https://prove2.me/submissions/e86e928a-b2f5-4cb1-a206-b28528700133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_field_of_connectedSpace


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f →
      ConnectedSpace X → IrreducibleSpace X := by
  intro k _ X f hf hc
  haveI := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace f
  infer_instance
end _root_.GlobalTheory
end GlobalTheory

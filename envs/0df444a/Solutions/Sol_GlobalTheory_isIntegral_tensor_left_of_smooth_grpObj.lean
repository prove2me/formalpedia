-- Prove2me | solution 1 for GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:30:48.599928+00:00
-- url     : https://prove2.me/submissions/7970057f-8c7d-4fd9-b1d6-35378639a3a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Theorems.Thm_GlobalTheory_isIntegral_of_isPullback_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (B T : Over S) [GrpObj B]
    [Smooth B.hom] [GeometricallyConnected B.hom] [IsIntegral T.left] :
    IsIntegral (T ⊗ B).left :=
  isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback T.hom B.hom).flip
end GlobalTheory

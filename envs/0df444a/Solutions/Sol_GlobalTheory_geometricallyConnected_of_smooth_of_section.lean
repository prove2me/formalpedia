-- Prove2me | solution 1 for GlobalTheory.geometricallyConnected_of_smooth_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:47.483274+00:00
-- url     : https://prove2.me/submissions/912f3b4a-6e4c-4efe-a4d1-00dc360bf46f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSection
import Theorems.Thm_GlobalTheory_RatPointConn_of_section


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
theorem _root_.solution :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  intro k _ X f e _ he _
  exact GlobalTheory.RatPointConn.of_section f e he
end GlobalTheory

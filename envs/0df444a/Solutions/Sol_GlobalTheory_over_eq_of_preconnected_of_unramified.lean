-- Prove2me | solution 1 for GlobalTheory.over_eq_of_preconnected_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:58.684302+00:00
-- url     : https://prove2.me/submissions/69d462fa-0c87-4d7d-8a5f-4c200e405b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_eq_of_preconnected_of_unramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S Z : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    [PreconnectedSpace T.left] {a b : T ⟶ X}
    (j : Z ⟶ T.left) [Nonempty Z] (hj : j ≫ a.left = j ≫ b.left) : a = b :=
  Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified X.hom ((Over.w a).trans (Over.w b).symm) j hj)
end GlobalTheory

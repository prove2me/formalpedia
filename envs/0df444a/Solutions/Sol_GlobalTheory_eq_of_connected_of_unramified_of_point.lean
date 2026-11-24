-- Prove2me | solution 1 for GlobalTheory.eq_of_connected_of_unramified_of_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:06.901139+00:00
-- url     : https://prove2.me/submissions/64f1cc26-6e16-4dc4-b555-c3357bce0232

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
theorem _root_.solution {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [ConnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    {k : Type u} [Field k] (j : Spec (.of k) ⟶ T) (hj : j ≫ a = j ≫ b) : a = b :=
  eq_of_preconnected_of_unramified f hab j hj
end GlobalTheory

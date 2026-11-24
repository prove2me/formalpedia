-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.bijective_of_isIso_appTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:45.949543+00:00
-- url     : https://prove2.me/submissions/83dbd4b3-3220-4c8f-ae41-193b1e16d568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R : CommRingCat.{u}} (p : X ⟶ Spec R) [IsIso p.appTop] :
    Function.Bijective ((Scheme.ΓSpecIso R).inv ≫ p.appTop) :=
  ConcreteCategory.bijective_of_isIso _
end GlobalTheory.ProperFunctions

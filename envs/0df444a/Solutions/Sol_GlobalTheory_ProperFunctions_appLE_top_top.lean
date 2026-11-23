-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.appLE_top_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:28.949795+00:00
-- url     : https://prove2.me/submissions/01d960a1-ddcb-4bb8-85ba-4a43a7806ffb

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
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) (h : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤) : p.appLE ⊤ ⊤ h = p.appTop :=
  (Scheme.Hom.app_eq_appLE p (U := ⊤)).symm
end GlobalTheory.ProperFunctions

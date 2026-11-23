-- Prove2me | solution 1 for GlobalTheory.Retract.surjective_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:08.085799+00:00
-- url     : https://prove2.me/submissions/d4a66988-667a-4566-96ac-bf66f68d487a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_apply_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y : Scheme.{u}} {i : X ⟶ Y} {r : Y ⟶ X} (hir : i ≫ r = 𝟙 X)
include hir
namespace GlobalTheory.Retract
theorem _root_.solution : Surjective r :=
  ⟨fun x ↦ ⟨i x, apply_apply hir x⟩⟩
end GlobalTheory.Retract

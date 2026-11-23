-- Prove2me | solution 1 for GlobalTheory.Retract.irreducibleSpace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:07.229745+00:00
-- url     : https://prove2.me/submissions/36b946ef-005d-4850-afee-e503e338c4fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_surjective_retraction

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
theorem _root_.solution [IrreducibleSpace Y] : IrreducibleSpace X :=
  (surjective_retraction hir).surj.irreducibleSpace r.continuous
end GlobalTheory.Retract

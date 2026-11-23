-- Prove2me | solution 1 for GlobalTheory.Retract.isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:59.299709+00:00
-- url     : https://prove2.me/submissions/de09ce7f-551b-426a-b899-3e2ca85a05e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_irreducibleSpace
import Theorems.Thm_GlobalTheory_Retract_isReduced

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
theorem _root_.solution [IsIntegral Y] : IsIntegral X :=
  (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨irreducibleSpace hir, isReduced hir⟩
end GlobalTheory.Retract

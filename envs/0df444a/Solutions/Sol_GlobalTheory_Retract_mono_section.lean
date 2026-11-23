-- Prove2me | solution 1 for GlobalTheory.Retract.mono_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:12.266202+00:00
-- url     : https://prove2.me/submissions/606e2e15-a19c-4fec-b909-10318fcee361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation

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
theorem _root_.solution : Mono i :=
  (SplitMono.mk r hir).mono
end GlobalTheory.Retract

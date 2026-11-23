-- Prove2me | solution 1 for GlobalTheory.ThickeningClosed.isOpen_zeroLocusOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:33.400845+00:00
-- url     : https://prove2.me/submissions/332a594b-7edd-4e7e-9deb-473a232209b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickeningClosed
namespace _root_.GlobalTheory.ThickeningClosed
theorem _root_.solution {X : Scheme.{0}} (K : X.IdealSheafData) :
    IsOpen (_root_.GlobalTheory.ThickeningClosed.zeroLocusOpen K) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨V, hxV, hV⟩
  exact ⟨V.1, fun y hy ↦ ⟨V, hy, hV⟩, V.1.2, hxV⟩
end _root_.GlobalTheory.ThickeningClosed
end GlobalTheory.ThickeningClosed

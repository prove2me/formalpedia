-- Prove2me | solution 1 for GlobalTheory.SecGlue.mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:48.843086+00:00
-- url     : https://prove2.me/submissions/30810456-1403-477d-b485-01b62f7c0cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.SecGlue
theorem _root_.solution {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q') (j : K → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : K => q') j ↔ h y ∈ LB.wchart L (fun _ : K => q) j := by
  subst e
  exact ⟨fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k,
    fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
end GlobalTheory.SecGlue

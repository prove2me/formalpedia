-- Prove2me | solution 1 for GlobalTheory.Cartier.mem_nonzeroLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:11.455151+00:00
-- url     : https://prove2.me/submissions/76905bc4-7a36-45f1-95ce-4d4ca72fbdd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution {L : LB X} (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    x ∈ Out.nonzeroLocus s ↔ x ∈ X.basicOpen (s.f i) := by
  refine ⟨fun h => ?_, fun h => Opens.mem_iSup.2 ⟨i, h⟩⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hxj : x ∈ L.U j := X.basicOpen_le _ hj
  have hm : x ∈ L.U i ⊓ L.U j := ⟨hx, hxj⟩
  have e := congrArg (X.presheaf.germ (L.U i ⊓ L.U j) x hm).hom (s.compat i j)
  rw [map_mul, germ_resG, germ_resG] at e
  rw [X.mem_basicOpen _ x hx]
  rw [X.mem_basicOpen _ x hxj] at hj
  exact (congrArg IsUnit e).mpr (((L.g i j).isUnit.map _).mul hj)
end GlobalTheory.Cartier

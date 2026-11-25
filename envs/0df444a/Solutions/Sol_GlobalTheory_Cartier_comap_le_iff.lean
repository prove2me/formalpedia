-- Prove2me | solution 1 for GlobalTheory.Cartier.comap_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:28.363972+00:00
-- url     : https://prove2.me/submissions/50dff429-23b8-4adf-803d-2409da058a4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5

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
theorem _root_.solution (I : X.IdealSheafData) (φ : Y ⟶ X) (J : Y.IdealSheafData) :
    I.comap φ ≤ J ↔ ∀ (U : X.affineOpens), ∀ a ∈ I.ideal U, ∀ (W : Y.affineOpens)
      (h : W.1 ≤ φ ⁻¹ᵁ U.1), resG Y h ((φ.app U.1).hom a) ∈ J.ideal W := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map, Scheme.Hom.ker,
    Scheme.IdealSheafData.le_ofIdeals_iff]
  refine forall_congr' fun U => forall₂_congr fun a _ => ?_
  exact app_subschemeι_eq_zero_iff J ((φ.app U.1).hom a)
end GlobalTheory.Cartier

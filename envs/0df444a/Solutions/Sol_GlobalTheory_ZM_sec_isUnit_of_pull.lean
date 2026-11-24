-- Prove2me | solution 1 for GlobalTheory.ZM.sec_isUnit_of_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:15.258292+00:00
-- url     : https://prove2.me/submissions/69b0115d-44e8-4d26-a92e-0d58856e6f73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
import Theorems.Thm_GlobalTheory_ZM_stalkMap_germ_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) (s : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ IsUnit ((f.appLE W W' h).hom s)) : IsUnit s := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ W s
  intro p hp
  obtain ⟨Z, f, z, W', h, hz, rfl, u⟩ := H p hp
  apply isUnit_of_map_unit (f.stalkMap z).hom
  rw [stalkMap_germ_appLE f W W' h z hz]
  exact u.map _
end GlobalTheory.ZM

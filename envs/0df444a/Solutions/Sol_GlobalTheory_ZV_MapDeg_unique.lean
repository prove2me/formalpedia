-- Prove2me | solution 1 for GlobalTheory.ZV.MapDeg.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:45.818875+00:00
-- url     : https://prove2.me/submissions/1e56cdc6-1d86-443a-9d4e-304d7fc3a518

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Theorems.Thm_GlobalTheory_ZV_MapDeg_finrank_eq

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
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
namespace MapDeg
theorem _root_.solution [Nonempty Y] {ψ : X ⟶ Y} {D D' : ℕ} (h : MapDeg ψ D) (h' : MapDeg ψ D') : D = D' := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact (h.finrank_eq U hU ⟨y, hy⟩).symm.trans (h'.finrank_eq U hU ⟨y, hy⟩)
end MapDeg
end GlobalTheory.ZV

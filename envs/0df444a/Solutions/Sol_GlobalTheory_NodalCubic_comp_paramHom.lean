-- Prove2me | solution 1 for GlobalTheory.NodalCubic.comp_paramHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:45:04.196727+00:00
-- url     : https://prove2.me/submissions/85483fb3-222d-4b9b-a85f-2469923cf59f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Theorems.Thm_P2M_GlobalTheory_NodalCubic_comp_toSpec__bbfc5e339852
import Theorems.Thm_GlobalTheory_NodalCubic_valOf_comp
import Theorems.Thm_GlobalTheory_NodalCubic_comp_param
import Theorems.Thm_P2M_GlobalTheory_NodalCubic_toSpec__constHom_50b6664562d9
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
variable (K : Type) [Field K]
variable {K}
namespace GlobalTheory.NodalCubic
theorem _root_.solution {k : Type} [CommRing k] {ρ : K →+* k}
    (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ) :
    x.left ≫ paramHom K = ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := by
  have e := comp_toSpecΓ (k := k) x.left
  have e2 : (evalAt (k := k) x.left).comp (constHom K _) = ρ := by
    have : Spec.map (CommRingCat.ofHom ((evalAt (k := k) x.left).comp (constHom K _))) =
        Spec.map (CommRingCat.ofHom ρ) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← e]
      exact (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) (toSpecΓ_constHom K _)).trans (Over.w x))
    exact congrArg (·.hom) (Spec.map_injective this)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
  rw [SpecMap_ptHom]
  refine ptHom_congr _ _ _ _ e2 ?_ _
  rw [comp_param, ← valOf_comp, Category.comp_id]
end GlobalTheory.NodalCubic

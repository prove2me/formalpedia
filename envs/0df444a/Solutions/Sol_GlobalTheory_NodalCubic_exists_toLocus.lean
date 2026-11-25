-- Prove2me | solution 1 for GlobalTheory.NodalCubic.exists_toLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:05.570868+00:00
-- url     : https://prove2.me/submissions/89004540-67dd-46c6-8641-f4f24f8cc352

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
import Theorems.Thm_GlobalTheory_NodalCubic_paramHom_toSpec
import Theorems.Thm_GlobalTheory_NodalCubic_comp_paramHom
import Theorems.Thm_GlobalTheory_NodalCubic_exists_over_point
import Theorems.Thm_GlobalTheory_NodalCubic_range_subset_of_forall_field
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_points


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
variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)
include hU
namespace GlobalTheory.NodalCubic
theorem _root_.solution : ∃ f : splitTorus (Spec (.of K)) ℤ ⟶ Over.mk (U.ι ≫ toSpec (node K)),
    f.left ≫ U.ι = paramHom K := by
  have h : Set.range (paramHom K) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point x
    rw [comp_paramHom, hU, node_map]
    exact (nonsingular_points k).1 _
  have e := IsOpenImmersion.lift_fac U.ι (paramHom K) h
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (paramHom K) h) ?_, e⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (paramHom_toSpec K))
end GlobalTheory.NodalCubic

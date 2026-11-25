-- Prove2me | solution 1 for GlobalTheory.NodalCubic.exists_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:36.693012+00:00
-- url     : https://prove2.me/submissions/a260ca08-aa12-484b-84b1-8897c3614cf5

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
theorem _root_.solution {k : Type} [Field k] {ρ : K →+* k}
    (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K))) :
    ∃ (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h ∧ (node k).toProjective.Nonsingular P := by
  obtain ⟨P, h, e⟩ := exists_eq_ptHom (node K) ρ (y.left ≫ U.ι)
    ((Category.assoc _ _ _).trans (Over.w y))
  refine ⟨P, h, e, ?_⟩
  rw [← node_map ρ, ← hU k ρ P h, ← e]
  intro z _
  exact (y.left z).2
end GlobalTheory.NodalCubic

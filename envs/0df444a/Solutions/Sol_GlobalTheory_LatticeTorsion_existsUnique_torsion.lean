-- Prove2me | solution 1 for GlobalTheory.LatticeTorsion.existsUnique_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.469802+00:00
-- url     : https://prove2.me/submissions/c43543c9-fa4a-4ef7-8e4c-b545aa7b8515

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom

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
open GlobalTheory GlobalTheory.LatticeTorsion
variable {S : Scheme.{0}}
namespace GlobalTheory.LatticeTorsion
theorem _root_.solution (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (x : T ⟶ G)
    (hx : x ^ n = 1) : ∃! y : T ⟶ torsion G n, y ≫ torsion.ι G n = x := by
  refine ⟨pullback.lift x (toUnit T) ((GrpTangent.comp_mulN x n).trans hx),
    pullback.lift_fst _ _ _, fun y hy => ?_⟩
  exact pullback.hom_ext (hy.trans (pullback.lift_fst _ _ _).symm) (toUnit_unique _ _)
end GlobalTheory.LatticeTorsion

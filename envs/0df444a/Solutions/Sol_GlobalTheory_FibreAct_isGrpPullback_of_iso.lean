-- Prove2me | solution 1 for GlobalTheory.FibreAct.isGrpPullback_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:57.298853+00:00
-- url     : https://prove2.me/submissions/ca57d9d4-e7fa-40d5-9279-1ba6d5af4b91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreAct

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
open GlobalTheory GlobalTheory.FibreAct
namespace GlobalTheory.FibreAct
theorem _root_.solution {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G) [IsIso ψ]
    [IsMonHom ψ] : IsGrpPullback G' G (𝟙 S) ψ.left := by
  haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = U ≫ x ≫ ψ := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have ey : y₀ = U ≫ y ≫ ψ := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _
end GlobalTheory.FibreAct

-- Prove2me | solution 1 for GlobalTheory.LevCover.finiteEtale_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:25.287571+00:00
-- url     : https://prove2.me/submissions/2d9ff217-79ba-408b-9f35-fc756e79c14f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution (X Y : Over S) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsFinite (X ⊗ Y).hom ∧ Etale (X ⊗ Y).hom :=
  ⟨inferInstanceAs (IsFinite (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (Etale (pullback.fst X.hom Y.hom ≫ X.hom))⟩
end GlobalTheory.LevCover

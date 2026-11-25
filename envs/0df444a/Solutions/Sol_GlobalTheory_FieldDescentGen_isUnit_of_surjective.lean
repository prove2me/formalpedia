-- Prove2me | solution 1 for GlobalTheory.FieldDescentGen.isUnit_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:34.61992+00:00
-- url     : https://prove2.me/submissions/0817ae69-de0f-49f1-9381-e6567b51d5b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField

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
open GlobalTheory
open GlobalTheory.FieldDescentGen
variable {X₀ X : Scheme.{0}}
namespace GlobalTheory.FieldDescentGen
theorem _root_.solution (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X₀.toLocallyRingedSpace.toRingedSpace U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hy : y ∈ X.basicOpen ((φ.appLE U V h).hom a) := by
    rw [X.basicOpen_of_isUnit ha]; exact h' hx
  rw [Scheme.basicOpen_appLE] at hy
  exact (X₀.mem_basicOpen a _ hx).1 hy.2
end GlobalTheory.FieldDescentGen

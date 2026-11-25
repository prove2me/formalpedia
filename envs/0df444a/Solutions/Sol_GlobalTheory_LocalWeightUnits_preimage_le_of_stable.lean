-- Prove2me | solution 1 for GlobalTheory.LocalWeightUnits.preimage_le_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:07:11.593556+00:00
-- url     : https://prove2.me/submissions/6eb0a63f-1a55-45fe-95e4-441288b24105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}
namespace GlobalTheory.LocalWeightUnits
theorem _root_.solution {V : H.left.Opens} (hV : Stable i V) :
    (snd (splitTorus S X) H).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) H ≫ i) * snd (splitTorus S X) H).left ⁻¹ᵁ V := by
  let U := (snd (splitTorus S X) H).left ⁻¹ᵁ V
  let Y : Over S := Over.mk (U.ι ≫ (splitTorus S X ⊗ H).hom)
  let j : Y ⟶ splitTorus S X ⊗ H := Over.homMk U.ι rfl
  have h := hV Y (j ≫ fst _ _) (j ≫ snd _ _) (fun y _ => y.2)
  rw [Category.assoc, ← MonObj.comp_mul] at h
  exact fun y hy => h (x := ⟨y, hy⟩) trivial
end GlobalTheory.LocalWeightUnits

-- Prove2me | solution 1 for GlobalTheory.ZM.SegreCoord.appLE_ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:23.055156+00:00
-- url     : https://prove2.me/submissions/8dc82034-a632-464b-8dd5-20aacfb31608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SegreCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepBC_appLE_appLE


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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.ZM.SegreCoord
theorem _root_.solution {Z : Scheme.{0}} (x : Z ⟶ P) {U : X.Opens} {V : Y.Opens} {W : P.Opens} {W' : Z.Opens}
    (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V) (e : W' ≤ x ⁻¹ᵁ W) (e₁ : W' ≤ (x ≫ p) ⁻¹ᵁ U) (e₂ : W' ≤ (x ≫ q) ⁻¹ᵁ V)
    (a : Γ(X, U)) (b : Γ(Y, V)) :
    (x.appLE W W' e).hom (ap p h₁ a * ap q h₂ b) =
      ((x ≫ p).appLE U W' e₁).hom a * ((x ≫ q).appLE V W' e₂).hom b := by
  rw [map_mul]
  exact congrArg₂ (· * ·) (appLE_appLE x p h₁ e e₁ a) (appLE_appLE x q h₂ e e₂ b)
end GlobalTheory.ZM.SegreCoord

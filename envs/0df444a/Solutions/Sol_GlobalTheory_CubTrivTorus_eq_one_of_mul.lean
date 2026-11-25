-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.eq_one_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:49.979077+00:00
-- url     : https://prove2.me/submissions/bc732ee2-1410-4d70-9a96-31c18b12b963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Theorems.Thm_GlobalTheory_CubTrivTorus_existsUnique_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution {Y : Over S} [GrpObj Y] [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ)
    (h₁ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left), gm (lift t (1 : Z ⟶ Y)).left z ⊤ ρ = 1)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left) : gm (lift t y).left z ⊤ ρ = 1 := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_char ρ hρ
  rw [hχ Z t y z, ← hχ Z t 1 z]
  exact h₁ Z t z
end GlobalTheory.CubTrivTorus

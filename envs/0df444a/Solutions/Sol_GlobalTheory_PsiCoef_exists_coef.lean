-- Prove2me | solution 1 for GlobalTheory.PsiCoef.exists_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:09.362816+00:00
-- url     : https://prove2.me/submissions/bbc5dcc3-7ac5-491e-814c-bab79a8d9b7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTwistedSectionThetaTranslateCoef
import Theorems.Thm_GlobalTheory_PsiCoef_exists_untwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
open GlobalTheory GlobalTheory.PsiCoef
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiCoef
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  intro R _ _ D th hth χ u hu g
  obtain ⟨g₀, hg₀⟩ := exists_untwist D χ u hu g
  obtain ⟨b, hb⟩ := hth g₀
  refine ⟨b, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) (y * cT D T χ)).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := hb _ (lift (toUnit T) (y * cT D T χ)).left z J hJ
  rw [e₁, hg₀ T y z J hJ, Units.mul_inv_eq_iff_eq_mul] at h
  rw [h]
  ring
end GlobalTheory.PsiCoef

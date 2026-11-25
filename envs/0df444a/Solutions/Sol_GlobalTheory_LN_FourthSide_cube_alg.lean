-- Prove2me | solution 1 for GlobalTheory.LN.FourthSide.cube_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:58:03.454228+00:00
-- url     : https://prove2.me/submissions/adfb38b8-a0e8-483e-86fa-eb2ec8983035

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourthSideRespectsRigSymmetryCube

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
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.FourthSide
namespace GlobalTheory.LN.FourthSide
theorem _root_.solution {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x y u : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E)
    (h₁ : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E')
    (h₂ : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C') :
    C' * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_mul, map_one]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂
end GlobalTheory.LN.FourthSide

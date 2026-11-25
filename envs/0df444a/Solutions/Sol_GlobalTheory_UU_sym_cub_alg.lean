-- Prove2me | solution 1 for GlobalTheory.UU.sym_cub_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:41.679528+00:00
-- url     : https://prove2.me/submissions/893a3377-d66e-44b1-b269-d2972c7833ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
theorem _root_.solution {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U} {σ : A → U} {σ' : A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) = W (a * b * d) * (W (a * b))⁻¹ * (W (a * d))⁻¹ * (W (b * d))⁻¹ * W a * W b *
      W d * (W 1)⁻¹ * θ' a b d) (hσ : ∀ a, σ (β a) = W a⁻¹ * (W a)⁻¹ * σ' a) {x y u : A'}
    (e : θ (β x)⁻¹ (β y)⁻¹ (β u)⁻¹ * σ (β x * β y) * σ (β x * β u) * σ (β y * β u) =
      θ (β x) (β y) (β u) * σ (β x * β y * β u) * σ (β x) * σ (β y) * σ (β u)) :
    θ' x⁻¹ y⁻¹ u⁻¹ * σ' (x * y) * σ' (x * u) * σ' (y * u) =
      θ' x y u * σ' (x * y * u) * σ' x * σ' y * σ' u := by
  have h1 := congrArg Additive.ofMul (hθ x⁻¹ y⁻¹ u⁻¹)
  have h2 := congrArg Additive.ofMul (hθ x y u)
  have s1 := congrArg Additive.ofMul (hσ (x * y))
  have s2 := congrArg Additive.ofMul (hσ (x * u))
  have s3 := congrArg Additive.ofMul (hσ (y * u))
  have s4 := congrArg Additive.ofMul (hσ (x * y * u))
  have s5 := congrArg Additive.ofMul (hσ x)
  have s6 := congrArg Additive.ofMul (hσ y)
  have s7 := congrArg Additive.ofMul (hσ u)
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [map_mul, map_inv, mul_inv, ofMul_mul, ofMul_inv] at h1 h2 s1 s2 s3 s4 s5 s6 s7 e' ⊢
  linear_combination (norm := abel) e' - h1 + h2 - s1 - s2 - s3 + s4 + s5 + s6 + s7
end GlobalTheory.UU

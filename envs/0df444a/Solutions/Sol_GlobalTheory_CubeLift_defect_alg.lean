-- Prove2me | solution 1 for GlobalTheory.CubeLift.defect_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:41:27.975594+00:00
-- url     : https://prove2.me/submissions/60813821-602b-4a6e-a1b3-c9f6d31722fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {B C U : Type} [CommGroup B] [CommGroup C] [CommGroup U]
namespace GlobalTheory.CubeLift
theorem _root_.solution {θ : C → C → C → U} (hθ : IsCub θ) (ι' : B →* C) (σ : B → U) (D : B → B → B → U)
    (h : ∀ x y u, σ (x * y * u) * σ x * σ y * σ u =
      D x y u * (θ (ι' x) (ι' y) (ι' u) * σ (x * y) * σ (x * u) * σ (y * u))) :
    (∀ x y u, D x y u = D y x u) ∧ (∀ x y u, D x y u = D x u y) ∧
      ∀ x y u v, D (x * y) u v * D x y v = D x (y * u) v * D y u v := by
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  refine ⟨fun x y u => ?_, fun x y u => ?_, fun x y u v => ?_⟩
  · have a := E (h x y u)
    have b := E (h y x u)
    rw [mul_comm y x, hθ.s01] at b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a := E (h x y u)
    have b := E (h x u y)
    rw [mul_comm u y, mul_right_comm x u y, hθ.s12] at b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a₁ := E (h (x * y) u v)
    have a₂ := E (h x y v)
    have a₃ := E (h x (y * u) v)
    have a₄ := E (h y u v)
    have c := E (hθ.coc (ι' x) (ι' y) (ι' u) (ι' v))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, map_mul, ← _root_.mul_assoc] at a₁ a₂ a₃ a₄ c ⊢
    linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂ - c
end GlobalTheory.CubeLift

-- Prove2me | solution 1 for GlobalTheory.AdditionTensor.sum_sval_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:44.326828+00:00
-- url     : https://prove2.me/submissions/9f934fb1-89b7-4744-8d46-ab6ef8e146fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionFormulaTensorNeZero
import Theorems.Thm_GlobalTheory_AdditionTensor_svalHom_smul
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.AdditionTensor
namespace GlobalTheory.AdditionTensor
theorem _root_.solution {F : Type} [CommRing F] {Z Y₁ Y₂ T : Scheme.{0}} {L : LB Z}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂))
    (h : ∑ i, TensorProduct.tmul F (a i) (b i) = 0) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂) (e : r₁ ≫ p₁ = r₂ ≫ p₂) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  let f : SecMod p₁ (LB.LinComb L φ₁ ε₁) →+ SecMod p₂ (LB.LinComb L φ₂ ε₂) →+ T.presheaf.stalk z :=
    (((AddMonoidHom.mul (R := T.presheaf.stalk z)).comp (svalHom p₁ φ₁ ε₁ r₁ z hJ)).flip.comp
      (svalHom p₂ φ₂ ε₂ r₂ z hJ)).flip
  have hf : ∀ s t, f s t = svalHom p₁ φ₁ ε₁ r₁ z hJ s * svalHom p₂ φ₂ ε₂ r₂ z hJ t := fun _ _ => rfl
  have hb : ∀ (c : F) s t, f (c • s) t = f s (c • t) := fun c s t => by
    rw [hf, hf, svalHom_smul, svalHom_smul, e]; ring
  have := congrArg (TensorProduct.liftAddHom f hb) h
  rw [map_sum, map_zero] at this
  simp only [TensorProduct.liftAddHom_tmul] at this
  exact this
end GlobalTheory.AdditionTensor

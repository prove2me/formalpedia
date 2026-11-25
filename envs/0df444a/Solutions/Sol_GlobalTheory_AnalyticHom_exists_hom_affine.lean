-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.exists_hom_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:42.099801+00:00
-- url     : https://prove2.me/submissions/8d634a56-967f-4b25-8425-398735a472c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_val_mul
import Theorems.Thm_GlobalTheory_AnalyticHom_val_add
import Theorems.Thm_GlobalTheory_AnalyticHom_val_one
import Theorems.Thm_GlobalTheory_AnalyticHom_val_zero
import Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec
import Theorems.Thm_P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] {Z : Type}
  (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
  (hon : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
include hon
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {W : X.Opens} {D : Y.Opens} (hW : IsAffineOpen W) (hD : IsAffineOpen D)
    (hin : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hfn : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (y : Sp ℂ ⟶ W.toScheme), y ≫ W.ι = ex w → y ≫ g = ey w := by
  choose ρ hρ using hfn
  have ext : ∀ a b : Γ(X, W), (∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → valAt' (ex w) W a = valAt' (ex w) W b) →
      a = b := fun a b h => eq_of_valAt'_eq p W a b fun x hx hxW => by
    obtain ⟨w, rfl⟩ := hon x hx
    exact h w hxW
  let ρ' : Γ(Y, D) →+* Γ(X, W) :=
    { toFun := ρ
      map_one' := ext _ _ fun w hw => by rw [hρ _ w hw, val_one _ hw, val_one _ (hin w hw)]
      map_mul' := fun a b => ext _ _ fun w hw => by
        rw [hρ _ w hw, val_mul _ hw, val_mul _ (hin w hw), hρ _ w hw, hρ _ w hw]
      map_zero' := ext _ _ fun w hw => by rw [hρ _ w hw, val_zero _ hw, val_zero _ (hin w hw)]
      map_add' := fun a b => ext _ _ fun w hw => by
        rw [hρ _ w hw, val_add _ hw, val_add _ (hin w hw), hρ _ w hw, hρ _ w hw] }
  refine ⟨hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ') ≫ hD.fromSpec, fun w y hy => ?_⟩
  have hw : ⊤ ≤ ex w ⁻¹ᵁ W := by
    rw [← hy]
    intro a _
    exact (y a).2
  have h1 := specMap_appLE_fromSpec hW (R := CommRingCat.of ℂ) (ex w) hw
  have h2 := specMap_appLE_fromSpec hD (R := CommRingCat.of ℂ) (ey w) (hin w hw)
  have h3 : y ≫ hW.isoSpec.hom =
      Spec.map ((ex w).appLE W ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) := by
    rw [← cancel_mono hW.fromSpec, h1, ← hy, Category.assoc, ← hW.isoSpec_inv_ι,
      Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h3, ← h2, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext f
  have := hρ f w hw
  rw [valAt', valAt', dif_pos hw, dif_pos (hin w hw)] at this
  exact this
end GlobalTheory.AnalyticHom

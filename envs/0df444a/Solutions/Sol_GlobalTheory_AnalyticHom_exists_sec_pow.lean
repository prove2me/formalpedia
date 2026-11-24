-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.exists_sec_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:49.342329+00:00
-- url     : https://prove2.me/submissions/c071a42b-0c22-4c5e-8b1f-1eaa048faad9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_val_mul
import Theorems.Thm_GlobalTheory_AnalyticHom_val_resG
import Theorems.Thm_GlobalTheory_AnalyticHom_val_appLE
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_mono
import Theorems.Thm_GlobalTheory_AnalyticHom_val_sec
import Theorems.Thm_GlobalTheory_AnalyticHom_chart_le
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
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
variable {X Y : Scheme.{0}} (L : LB X) (κ : Y ⟶ X) (σ : X ⟶ Y) (e : σ ≫ κ = 𝟙 X) (N : ℕ)
include e
namespace GlobalTheory.AnalyticHom
theorem _root_.solution (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (s : (L.LinComb (K := Fin N) (fun _ => κ) (fun _ => 1)).Sec) :
    ∃ s' : (lbPow L N).Sec, ∀ (x : Sp ℂ ⟶ X) (j : PUnit → L.ι), ⊤ ≤ x ⁻¹ᵁ (lbPow L N).U j →
      valAt' x ((lbPow L N).U j) (s'.f j) =
        valAt' (x ≫ σ) (L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit))
          (s.f fun _ => j PUnit.unit) := by
  let f : ∀ j : PUnit → L.ι, Γ(X, L.wchart (fun _ : PUnit => 𝟙 X) j) := fun j =>
    (σ.appLE _ _ (chart_le L κ σ e N j)).hom (s.f fun _ => j PUnit.unit)
  have hf : ∀ (x : Sp ℂ ⟶ X) (j : PUnit → L.ι), ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => 𝟙 X) j →
      valAt' x _ (f j) = valAt' (x ≫ σ) (L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit))
        (s.f fun _ => j PUnit.unit) := fun x j hj => val_appLE x σ _ _ _ _ hj
  refine ⟨⟨f, fun i j => eq_of_valAt'_eq p _ _ _ fun x _ hx => ?_⟩, hf⟩
  obtain ⟨hi, hj⟩ := (le_preimage_inf x _ _).1 hx
  have hi' : ⊤ ≤ (x ≫ σ) ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => i PUnit.unit) :=
    le_preimage_mono x (chart_le L κ σ e N i) hi
  have hj' : ⊤ ≤ (x ≫ σ) ⁻¹ᵁ L.wchart (fun _ : Fin N => κ) (fun _ => j PUnit.unit) :=
    le_preimage_mono x (chart_le L κ σ e N j) hj
  refine (val_resG x inf_le_left hx _).trans (Eq.trans ?_ (val_mul x hx _ _).symm)
  refine (hf x i hi).trans ((val_sec (x ≫ σ) s _ _ hi' hj').trans (congrArg₂ (· * ·) ?_ ?_))
  · refine (val_linComb (x ≫ σ) valueRules L _ _ _ _ hi' hj').trans
      (Eq.trans ?_ (val_linComb x valueRules L _ _ _ _ hi hj).symm)
    simp [e]
  · exact ((val_resG x inf_le_right hx _).trans (hf x j hj)).symm
end GlobalTheory.AnalyticHom

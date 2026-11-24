-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.exists_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:10.651942+00:00
-- url     : https://prove2.me/submissions/d56544dd-4970-46c3-96d8-3567a69f4be5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_val_mul
import Theorems.Thm_GlobalTheory_AnalyticHom_val_one
import Theorems.Thm_GlobalTheory_AnalyticHom_val_resG
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_mono
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820


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
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')
namespace GlobalTheory.AnalyticHom
theorem _root_.solution [LocallyOfFiniteType A.hom] {k : ℕ} {s t : (lbPow L k).Sec}
    {θ ϑ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow k s θ) (ht : u.IsFnPow k t ϑ) (j : (lbPow L k).ι) :
    ∃ h : Γ(A.left, A.left.basicOpen (t.f j)), ∀ w,
      ⊤ ≤ (u.ex w).left ⁻¹ᵁ A.left.basicOpen (t.f j) →
        valAt' (u.ex w).left _ h * ϑ w = θ w := by
  have hle := A.left.basicOpen_le (t.f j)
  obtain ⟨v, hv⟩ := isUnit_of_valAt'_ne_zero A.hom _ (resG _ hle (t.f j)) fun x _ hx => by
    rw [val_resG x hle hx]
    exact ((valueRules _ x).2.2.2.2.1 _ _).1 hx
  refine ⟨resG _ hle (s.f j) * (v⁻¹).val, fun w hw => ?_⟩
  have hj := le_preimage_mono _ hle hw
  have h1 : valAt' (u.ex w).left _ (v⁻¹).val * valAt' (u.ex w).left _ v.val = 1 := by
    rw [← val_mul _ hw, Units.inv_mul, val_one _ hw]
  rw [hv, val_resG _ hle hw, ht j w hj] at h1
  rw [val_mul _ hw, val_resG _ hle hw, hs j w hj]
  linear_combination θ w * h1
end GlobalTheory.AnalyticHom

-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.val_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:06.076282+00:00
-- url     : https://prove2.me/submissions/d649b504-28c2-4d01-a064-51f697ed395e

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
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf


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
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {L : LB X} (s : L.Sec) (i j : L.ι) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (s.f i) =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  rw [← val_resG x inf_le_left hij (s.f i), ← val_resG x inf_le_right hij (s.f j), ← val_mul x hij]
  exact congrArg _ (s.compat i j)
end GlobalTheory.AnalyticHom

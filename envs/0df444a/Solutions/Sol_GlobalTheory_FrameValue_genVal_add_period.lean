-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_add_period
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.767193+00:00
-- url     : https://prove2.me/submissions/55bf1c71-8c94-4d51-af57-2d385cecb8a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_le_wchart_chartAt
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_frameProd_add_period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (t : LB.Gen (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y}
    {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (l : K → u.Λ) :
    genVal u hL t y (fun k => z k + l k) = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * genVal u hL t y z := by
  have n : (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (ahFactor_ne_zero h _ _)
  rw [genVal, genVal, genValIn, genValIn, frameProd_add_period h hz ε l (le_wchart_chartAt hL φ y),
    ← mul_div_assoc, mul_div_mul_left _ _ n]
end GlobalTheory.FrameValue

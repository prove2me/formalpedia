-- Prove2me | solution 1 for GlobalTheory.FrameValue.genVal_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.162045+00:00
-- url     : https://prove2.me/submissions/877633d0-d765-497c-849e-70e4d1d29215

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
import Theorems.Thm_GlobalTheory_CubeValues_val_pullU
import Theorems.Thm_GlobalTheory_CubeValues_val_res
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


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
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (y : Sp ℂ ⟶ Y') (z : K → Fin g → ℂ) :
    genVal u hL (LB.pullGen L φ ε t h) y z = genVal u hL t (y ≫ h) z := by
  have e : (fun k => chartAt hL ((y ≫ h) ≫ φ k)) = fun k => chartAt hL (y ≫ h ≫ φ k) :=
    funext fun k => by rw [Category.assoc]
  rw [genVal, genVal, e]
  refine congrArg₂ (· / ·) ?_ rfl
  exact (val_res y valueRules _ (le_wchart_chartAt hL (fun k => h ≫ φ k) y) _).trans (val_pullU y valueRules h _ _)
end GlobalTheory.FrameValue

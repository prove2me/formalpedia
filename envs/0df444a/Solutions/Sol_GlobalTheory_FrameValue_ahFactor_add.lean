-- Prove2me | solution 1 for GlobalTheory.FrameValue.ahFactor_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:29:42.286801+00:00
-- url     : https://prove2.me/submissions/d8cf6cdc-2b09-435d-b360-12452de1e285

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_le_chartAt
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period


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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) (z : Fin g → ℂ) :
    ahFactor Hm χ (l + m) z = ahFactor Hm χ l z * ahFactor Hm χ m (z + l) := by
  have hi := le_chartAt hL (u.ex z).left
  set i := chartAt hL (u.ex z).left
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rw [ex_add_period u _ _ l.2]; exact hi
  have hi'' : ⊤ ≤ (u.ex (z + (l + m : u.Λ))).left ⁻¹ᵁ L.U i := by rw [ex_add_period u _ _ (l + m).2]; exact hi
  have e := (h.2.2.2 (l + m) i z hi).symm.trans (h.2.2.2 l i z hi)
  rw [h.2.2.2 m i _ hi', add_assoc z, ← Submodule.coe_add, ← _root_.mul_assoc] at e
  exact mul_right_cancel₀ (u.fr_ne i _ hi'') e
end GlobalTheory.FrameValue

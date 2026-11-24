-- Prove2me | solution 1 for GlobalTheory.FrameValue.val_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:06.693268+00:00
-- url     : https://prove2.me/submissions/c5d66ad7-3d55-49ac-a26c-a431188b33c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
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
namespace GlobalTheory.FrameValue
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB X} (s : L.Sec) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (s.f i) = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (s.f j) := by
  have hij := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  obtain ⟨e, he⟩ := (valueRules X x).2.1 _ hij
  rw [← (valueRules X x).2.2.1 _ _ inf_le_left (s.f i) hij, ← (valueRules X x).2.2.1 _ _ inf_le_right (s.f j) hij,
    he, he, he, ← map_mul]
  exact congrArg e (s.compat i j)
end GlobalTheory.FrameValue

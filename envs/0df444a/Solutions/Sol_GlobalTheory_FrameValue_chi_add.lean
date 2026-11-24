-- Prove2me | solution 1 for GlobalTheory.FrameValue.chi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:34.009808+00:00
-- url     : https://prove2.me/submissions/215aa637-bd57-4f21-8f60-e910fc51be26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_zero_left
import Theorems.Thm_GlobalTheory_FrameValue_ahFactor_add
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_left
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_add_right
import Theorems.Thm_GlobalTheory_EigenNorm_hermForm_conj


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
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) := by
  have e := ahFactor_add hL h l m 0
  have e' := Complex.sub_conj (hermForm Hm l m)
  rw [← hermForm_conj Hm h.1] at e'
  push_cast at e'
  simp only [ahFactor, hermForm_zero_left, zero_add, mul_zero, Submodule.coe_add, hermForm_add_left,
    hermForm_add_right] at e
  refine mul_right_cancel₀ (Complex.exp_ne_zero _) (e.trans ?_)
  rw [_root_.mul_mul_mul_comm, ← Complex.exp_add, _root_.mul_assoc (χ l * χ m), ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2 : ℂ) * e'
end GlobalTheory.FrameValue

-- Prove2me | solution 1 for GlobalTheory.FrameValue.chi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:07:15.384301+00:00
-- url     : https://prove2.me/submissions/106a9f79-9f30-4a31-a537-4ed0776b54b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_chi_ne_zero
import Theorems.Thm_GlobalTheory_FrameValue_hermForm_zero_left
import Theorems.Thm_GlobalTheory_FrameValue_chi_add

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
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) : χ 0 = 1 := by
  have e := chi_add hL h 0 0
  simp only [add_zero, Submodule.coe_zero, hermForm_zero_left, Complex.zero_im, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, _root_.mul_one] at e
  exact mul_left_cancel₀ (chi_ne_zero h 0) (e.symm.trans (_root_.mul_one _).symm)
end GlobalTheory.FrameValue

-- Prove2me | solution 1 for GlobalTheory.FrameValue.exists_int_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:43.950836+00:00
-- url     : https://prove2.me/submissions/31fc2b26-7892-41e5-963e-597cfc3c49d6

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
import Theorems.Thm_GlobalTheory_FrameValue_chi_add
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
theorem _root_.solution (hL : L.IsLB) (h : u.IsAH Hm χ) (l m : u.Λ) : ∃ n : ℤ, (n : ℝ) = (hermForm Hm l m).im := by
  have e := (chi_add hL h l m).symm.trans ((congrArg χ (add_comm l m)).trans (chi_add hL h m l))
  rw [mul_comm (χ m), hermForm_conj Hm h.1 l m, Complex.conj_im] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1
    (mul_left_cancel₀ (mul_ne_zero (chi_ne_zero h l) (chi_ne_zero h m)) e)
  refine ⟨n, ?_⟩
  have : ((n : ℝ) : ℂ) = ((hermForm Hm l m).im : ℂ) := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    push_cast at hn ⊢
    linear_combination -hn
  exact_mod_cast this
end GlobalTheory.FrameValue

-- Prove2me | solution 1 for GlobalTheory.HeckeTwoConst.gammaR_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:46.602111+00:00
-- url     : https://prove2.me/submissions/799a471d-6592-40d0-9d79-04893876d4f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoConst
theorem _root_.solution : Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Gammaℝ_add_two (s := -1) (by norm_num)
  rw [show (-1 : ℂ) + 2 = 1 by norm_num, Gammaℝ_one] at h
  field_simp at h
  linear_combination h
end GlobalTheory.HeckeTwoConst

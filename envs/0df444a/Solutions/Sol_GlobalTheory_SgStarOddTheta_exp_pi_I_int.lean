-- Prove2me | solution 1 for GlobalTheory.SgStarOddTheta.exp_pi_I_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:51.155098+00:00
-- url     : https://prove2.me/submissions/2a83cf31-9bf8-4b15-a03f-0df87652e012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open GlobalTheory GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F
namespace GlobalTheory.SgStarOddTheta
theorem _root_.solution (j : ℤ) : cexp ((Real.pi : ℂ) * I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow
end GlobalTheory.SgStarOddTheta

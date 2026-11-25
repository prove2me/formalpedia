-- Prove2me | solution 1 for GlobalTheory.OfPeriod.exp_pi_I_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:22.591655+00:00
-- url     : https://prove2.me/submissions/a3102556-7533-41d9-9273-e80435d23ecc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.OfPeriod.reForm_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex
namespace GlobalTheory.OfPeriod
theorem _root_.solution (n : ℤ) : Complex.exp (Real.pi * I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, mul_comm]; simp
end GlobalTheory.OfPeriod

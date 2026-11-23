-- Prove2me | solution 1 for GlobalTheory.PrincipalLogDeriv.half_le_norm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:55.823554+00:00
-- url     : https://prove2.me/submissions/03c35a16-6935-4e05-a0ff-c9bb55b34074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_norm_cpow_neg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PrincipalLogDeriv
namespace GlobalTheory.PrincipalLogDeriv
theorem _root_.solution {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith
end GlobalTheory.PrincipalLogDeriv

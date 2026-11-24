-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:29.503845+00:00
-- url     : https://prove2.me/submissions/91965f68-445f-4129-9111-bfc6dd5b376c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {S : ℝ} (hS : 0 ≤ S) :
    S * Real.exp (-(2 * Real.pi * S)) ≤ Real.exp (-S) := by
  have h1 : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
  calc S * Real.exp (-(2 * Real.pi * S))
      ≤ Real.exp S * Real.exp (-(2 * Real.pi * S)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (S + -(2 * Real.pi * S)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-S) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_gt_three]
end GlobalTheory.CompanionTheory.EisTube

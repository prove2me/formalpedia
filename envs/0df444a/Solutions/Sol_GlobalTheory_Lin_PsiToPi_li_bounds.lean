-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.li_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:56.755168+00:00
-- url     : https://prove2.me/submissions/09a51668-d0bb-4ed0-8a88-9fa9dd0646f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_intInt_inv_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : 0 ≤ Li x ∧ Li x ≤ 3 / 2 * x := by
  have h2 := Real.log_two_gt_d9
  constructor
  · exact intervalIntegral.integral_nonneg hx fun t ht =>
      div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))
  · have h := intervalIntegral.integral_mono_on hx (intInt_inv_log (by linarith))
      (intervalIntegrable_const (c := (3 / 2 : ℝ))) (fun t ht => by
        have := Real.log_le_log (by norm_num) ht.1
        rw [div_le_iff₀ (by linarith)]; linarith)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    unfold Li; linarith
end GlobalTheory.Lin.PsiToPi

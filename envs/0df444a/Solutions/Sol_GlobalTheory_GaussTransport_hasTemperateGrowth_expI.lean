-- Prove2me | solution 1 for GlobalTheory.GaussTransport.hasTemperateGrowth_expI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:56.203988+00:00
-- url     : https://prove2.me/submissions/c25aa65b-1f28-4103-971f-640250efa615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp
import Theorems.Thm_GlobalTheory_GaussTransport_iteratedDeriv_cexp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport
namespace GlobalTheory.GaussTransport
theorem _root_.solution : Function.HasTemperateGrowth (fun t : ℝ => Complex.exp (Complex.I * t)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, ‖Complex.I‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_mul, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]
end GlobalTheory.GaussTransport

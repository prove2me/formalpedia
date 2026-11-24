-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PolyGaussSchwartz.norm_toEuclid_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:18.913077+00:00
-- url     : https://prove2.me/submissions/c4c3a8d0-d707-4e53-bb43-2596747562dc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz
theorem _root_.solution (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
end GlobalTheory.CompanionTheory.PolyGaussSchwartz

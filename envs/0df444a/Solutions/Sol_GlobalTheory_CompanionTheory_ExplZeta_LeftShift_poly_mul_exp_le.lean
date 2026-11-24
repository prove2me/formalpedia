-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.poly_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:30:00.841664+00:00
-- url     : https://prove2.me/submissions/6bab81cf-bed2-46a3-9a70-94070a17f59a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift
namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift
theorem _root_.solution {σ : ℝ} (hσ : σ ≤ 0) :
    (2 + |σ|) * Real.exp (σ / 2) ≤ 4 * Real.exp (σ / 4) := by
  rw [abs_of_nonpos hσ]
  have h1 : -σ / 4 + 1 ≤ Real.exp (-σ / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (σ / 2) = Real.exp (σ / 4) * Real.exp (σ / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-σ / 4) * Real.exp (σ / 4) = 1 := by
    rw [← Real.exp_add]; simp [show -σ / 4 + σ / 4 = 0 by ring]
  have hp := Real.exp_pos (σ / 4)
  have h4 : (2 + -σ) * Real.exp (σ / 4) ≤ 4 := by
    have : (2 + -σ) * Real.exp (σ / 4) ≤ 4 * Real.exp (-σ / 4) * Real.exp (σ / 4) := by
      apply mul_le_mul_of_nonneg_right _ hp.le
      linarith
    calc _ ≤ _ := this
      _ = 4 * (Real.exp (-σ / 4) * Real.exp (σ / 4)) := by ring
      _ = 4 := by rw [h3]; ring
  rw [h2]
  calc (2 + -σ) * (Real.exp (σ / 4) * Real.exp (σ / 4))
      = ((2 + -σ) * Real.exp (σ / 4)) * Real.exp (σ / 4) := by ring
    _ ≤ 4 * Real.exp (σ / 4) := mul_le_mul_of_nonneg_right h4 hp.le
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.left_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:59.900311+00:00
-- url     : https://prove2.me/submissions/bc7c2d0c-f3fe-4974-8b91-0706501da408

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_rpow_le_exp_half
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_norm_quot

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
theorem _root_.solution {g s : ℂ} {A x B : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ -1)
    (hB : |s.im| ≤ B) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ A * (1 + |s.re| + B) * Real.exp (s.re / 2) := by
  rw [norm_quot hx]
  have hn : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hre : 1 ≤ |s.re| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hn1 : 1 ≤ ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (1 + |s.re| + B) := by
    refine hg.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have h2 := rpow_le_exp_half hx (show s.re ≤ 0 by linarith)
  calc ‖g‖ * x ^ s.re / ‖s‖ ≤ ‖g‖ * x ^ s.re :=
        div_le_self (mul_nonneg (norm_nonneg _) hxp) hn1
    _ ≤ _ := mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift

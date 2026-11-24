-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:08.615635+00:00
-- url     : https://prove2.me/submissions/7b13be26-1440-4c7e-87a5-4250dacda368

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_rpow_le_exp_half
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_poly_mul_exp_le
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
theorem _root_.solution {g s : ℂ} {A x : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ 0)
    (him : 1 ≤ |s.im|) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ 4 * A * Real.exp (s.re / 4) := by
  rw [norm_quot hx]
  have hn : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnpos : 0 < ‖s‖ := by linarith
  have hxp : 0 ≤ x ^ s.re := Real.rpow_nonneg (by linarith) _
  have h1 : ‖g‖ ≤ A * (2 + |s.re|) * ‖s‖ := by
    refine hg.trans ?_
    have h0 := abs_nonneg s.re
    have : 1 + |s.re| + |s.im| ≤ (2 + |s.re|) * ‖s‖ := by nlinarith
    calc A * (1 + |s.re| + |s.im|) ≤ A * ((2 + |s.re|) * ‖s‖) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  rw [div_le_iff₀ hnpos]
  have h2 := rpow_le_exp_half hx hs
  have h3 := poly_mul_exp_le hs
  calc ‖g‖ * x ^ s.re ≤ (A * (2 + |s.re|) * ‖s‖) * Real.exp (s.re / 2) :=
        mul_le_mul h1 h2 hxp (le_trans (norm_nonneg _) h1)
    _ = A * ((2 + |s.re|) * Real.exp (s.re / 2)) * ‖s‖ := by ring
    _ ≤ A * (4 * Real.exp (s.re / 4)) * ‖s‖ := by
        apply mul_le_mul_of_nonneg_right _ hnpos.le
        exact mul_le_mul_of_nonneg_left h3 hA
    _ = _ := by ring
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift

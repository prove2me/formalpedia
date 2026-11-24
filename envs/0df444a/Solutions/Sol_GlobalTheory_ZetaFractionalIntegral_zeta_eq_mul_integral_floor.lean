-- Prove2me | solution 1 for GlobalTheory.ZetaFractionalIntegral.zeta_eq_mul_integral_floor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:15.232389+00:00
-- url     : https://prove2.me/submissions/542f8704-26cd-4f35-9df9-a2aecb004ce7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZetaFractionalIntegral
open MeasureTheory Set Filter Asymptotics
namespace GlobalTheory.ZetaFractionalIntegral
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n ↦ ?_
    simp
  have key := LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)
  have e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [← e1, key]
  congr 2
  funext t
  simp
end GlobalTheory.ZetaFractionalIntegral

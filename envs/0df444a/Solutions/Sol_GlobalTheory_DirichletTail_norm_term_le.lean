-- Prove2me | solution 1 for GlobalTheory.DirichletTail.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:43:01.691981+00:00
-- url     : https://prove2.me/submissions/9c299ba7-9cb6-4552-9711-46347b48f201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_norm_sum_range_le
import Theorems.Thm_GlobalTheory_DirichletTail_norm_cpow_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ)
    {δ R : ℝ} {s : ℂ} (hδ : 0 < δ) (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖term χ n s‖ ≤ q * (R / δ) *
      (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) := by
  have h1 := norm_sum_range_le χ hχ (n + 1)
  have h2 := norm_cpow_sub_le (a := ((n + 1 : ℕ) : ℝ)) (b := ((n + 1 + 1 : ℕ) : ℝ))
    (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast Nat.le_succ (n + 1)) hδ hs
  simp only [Complex.ofReal_natCast] at h2
  have hd : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ) := by
    refine sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
    exact_mod_cast Nat.le_succ (n + 1)
  rw [term, norm_mul]
  calc _ ≤ (q : ℝ) * (‖s‖ / δ * (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (q : ℝ) * (R / δ * (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ))) := by
        gcongr
    _ = _ := by ring
end GlobalTheory.DirichletTail

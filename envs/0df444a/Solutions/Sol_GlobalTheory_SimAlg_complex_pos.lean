-- Prove2me | solution 1 for GlobalTheory.SimAlg.complex_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:43.493204+00:00
-- url     : https://prove2.me/submissions/f6c11671-7fbc-412a-8923-e343e1f84069

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_real_nonneg
import Theorems.Thm_GlobalTheory_SimAlg_real_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ) (hs : ∀ i j, G i j = G j i)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℂ)
    (hx : ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (G i j : ℂ) = 0) : x = 0 := by
  have h := congrArg Complex.re hx
  have h1 := real_nonneg G hG fun i => (x i).re
  have h2 := real_nonneg G hG fun i => (x i).im
  have h3 : (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (G i j : ℂ)).re =
      ∑ i, ∑ j, (x i).re * (x j).re * (G i j : ℝ) + ∑ i, ∑ j, (x i).im * (x j).im * (G i j : ℝ) := by
    simp only [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp; ring
  rw [h3, Complex.zero_re] at h
  have e1 := real_pos G hs hG (fun i => (x i).re) (by linarith)
  have e2 := real_pos G hs hG (fun i => (x i).im) (by linarith)
  ext i
  exact Complex.ext (congrFun e1 i) (congrFun e2 i)
end GlobalTheory.SimAlg

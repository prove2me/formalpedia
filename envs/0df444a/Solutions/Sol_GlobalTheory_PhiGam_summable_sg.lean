-- Prove2me | solution 1 for GlobalTheory.PhiGam.summable_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:30.941399+00:00
-- url     : https://prove2.me/submissions/ac414491-2a1e-4ed1-9059-aa85800f0941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam
theorem _root_.solution {l n : ℕ} [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    Summable fun j : ℕ => (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hg : Summable fun j : ℕ => ((∑ t, h t : ℕ) : ℝ) * ((l : ℝ)⁻¹) ^ (j + 1) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith)))).mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hg
  rw [div_eq_mul_inv, inv_pow]
  gcongr
  exact Finset.single_le_sum (f := h) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
end GlobalTheory.PhiGam

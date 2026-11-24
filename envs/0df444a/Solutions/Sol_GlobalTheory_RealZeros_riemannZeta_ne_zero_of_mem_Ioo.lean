-- Prove2me | solution 1 for GlobalTheory.RealZeros.riemannZeta_ne_zero_of_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:13.696265+00:00
-- url     : https://prove2.me/submissions/21ab503d-c870-4893-9d72-70532d5c0cbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_summable_br
import Theorems.Thm_GlobalTheory_RealZeros_br_ofReal
import Theorems.Thm_GlobalTheory_RealZeros_eta_eq_of_strip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  intro h
  have key := eta_eq_of_strip (s := σ) (by simpa using h0) (by simpa using h1)
  have hsum := summable_br (N := 2) (c := 1) (d := 2) (by norm_num) le_rfl (by norm_num)
    (s := σ) (by simpa using h0)
  simp only [br_ofReal] at key hsum
  rw [h, mul_zero, ← ofReal_tsum] at key
  rw [summable_ofReal] at hsum
  have hpos : ∀ k : ℕ, 0 < ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) :=
    fun k => sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by positivity)
      (by exact_mod_cast Nat.lt_succ_self _) (by linarith))
  have := hsum.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  exact this.ne (by exact_mod_cast key)
end GlobalTheory.RealZeros

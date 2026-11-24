-- Prove2me | solution 1 for GlobalTheory.RealZeros.norm_br_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:55.555582+00:00
-- url     : https://prove2.me/submissions/4816c017-4a7d-42bd-bc34-f5ccb3593d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_norm_cpow_sub_le

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
theorem _root_.solution {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) (k : ℕ) {s : ℂ} {ε R : ℝ}
    (hε : 0 < ε) (hs : ε < s.re) (hR : ‖s‖ < R) :
    ‖br N c d k s‖ ≤ R * d * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) := by
  have h1 : k + 1 ≤ N * k + c := by nlinarith
  have h1' : ((k + 1 : ℕ) : ℝ) ≤ ((N * k + c : ℕ) : ℝ) := by exact_mod_cast h1
  have h0 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have key := norm_cpow_sub_le (s := s) (by linarith) (a := ((N * k + c : ℕ) : ℝ))
    (b := ((N * k + d : ℕ) : ℝ)) (by linarith) (by exact_mod_cast Nat.add_le_add_left hcd _)
  simp only [ofReal_natCast] at key
  refine key.trans ?_
  have h2 : ((N * k + c : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
    (Real.rpow_le_rpow_of_nonpos (by linarith) h1' (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le h0 (by linarith))
  have h3 : ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ) ≤ d := by
    push_cast
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  have h4 : (0 : ℝ) ≤ ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ) := by
    have : ((N * k + c : ℕ) : ℝ) ≤ ((N * k + d : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hcd _
    linarith
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR.le
  calc _ ≤ R * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) * d := by gcongr
    _ = _ := by ring
end GlobalTheory.RealZeros

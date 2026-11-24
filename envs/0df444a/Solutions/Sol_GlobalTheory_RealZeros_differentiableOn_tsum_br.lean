-- Prove2me | solution 1 for GlobalTheory.RealZeros.differentiableOn_tsum_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:27:22.579795+00:00
-- url     : https://prove2.me/submissions/165f7e33-ed44-4943-b6e7-2710d945e28c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_norm_br_le
import Theorems.Thm_GlobalTheory_RealZeros_summable_bound

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
theorem _root_.solution {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) :
    DifferentiableOn ℂ (fun s => ∑' k, br N c d k s) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hU : IsOpen {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hd : DifferentiableOn ℂ (fun z => ∑' k, br N c d k z)
      {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1} := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_bound (half_pos hs') ((‖s‖ + 1) * d)) (fun k => ?_) hU
      (fun k z hz => norm_br_le hN hc hcd k (half_pos hs') hz.1 hz.2)
    intro z _
    have h1 : ((N * k + c : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((N * k + d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl h2))).differentiableWithinAt
  exact (hd.differentiableAt (hU.mem_nhds ⟨half_lt_self hs', lt_add_one _⟩)).differentiableWithinAt
end GlobalTheory.RealZeros

-- Prove2me | solution 1 for GlobalTheory.RealZeros.eta_eq_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:05.71239+00:00
-- url     : https://prove2.me/submissions/3d2d5687-20a4-4650-85e5-d7f59f5cec4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_hasSum_group

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
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s = ∑' k, br 2 1 2 k s := by
  have h0 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
    have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr
        (Complex.summable_one_div_nat_cpow.mpr hs)
      simpa using this
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    simpa [cpow_neg] using hsum.hasSum
  have h1 := hasSum_group 2 h0
  have h2 := h0.mul_left (2 * (2 : ℂ) ^ (-s))
  have h3 := h1.sub h2
  rw [sub_mul, one_mul, ← h3.tsum_eq]
  refine tsum_congr fun k => ?_
  have : ((2 * k + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((k + 1 : ℕ) : ℂ) ^ (-s) := by
    have := natCast_mul_natCast_cpow 2 (k + 1) (-s)
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, Nat.cast_mul, this]
    simp
  simp only [Fin.sum_univ_two, br, Fin.val_zero, Fin.val_one, add_zero, add_assoc]
  rw [this]
  ring
end GlobalTheory.RealZeros

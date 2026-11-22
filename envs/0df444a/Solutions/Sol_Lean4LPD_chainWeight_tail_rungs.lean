-- Prove2me | solution 1 for Lean4LPD.chainWeight_tail_rungs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:47.809804+00:00
-- url     : https://prove2.me/submissions/d3dbb4f6-025f-4007-bed2-901f46375d3f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (kh1 c : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = kh1 ^ j * ∏ i ∈ range j, ((m : ℝ) + c - j + 1 + i) := by
  have hterm : ∀ i : ℕ, rungW kh1 c (m - j + i + 2)
      = kh1 * ((m : ℝ) + c - j + 1 + i) := by
    intro i
    unfold rungW
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hjm]
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
end Lean4LPD

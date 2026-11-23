-- Prove2me | solution 1 for GlobalTheory.NormPowSubOne.norm_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.303941+00:00
-- url     : https://prove2.me/submissions/eeea2c18-2fed-4a11-8f7e-27e1b5b68ddb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormPowSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NormPowSubOne
namespace GlobalTheory.NormPowSubOne
theorem _root_.solution {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by
  induction a with
  | zero => simp
  | succ n ih =>
    have h : ζ ^ (n + 1) - 1 = ζ * (ζ ^ n - 1) + (ζ - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hζ, one_mul]
    exact ih
end GlobalTheory.NormPowSubOne

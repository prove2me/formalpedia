-- Prove2me | solution 1 for GlobalTheory.GaussCoset.summable_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:46.577216+00:00
-- url     : https://prove2.me/submissions/6e0f3500-078d-498e-a17c-e5ec6f99ff7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Theorems.Thm_GlobalTheory_GaussCoset_exp_le_inv_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset
namespace GlobalTheory.GaussCoset
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by
  have hmaj := (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1)
    (Nat.lt_succ_self _) x).mul_left
      (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin : {z : L | (z : V) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with z hz
  have hne : (z : V) ≠ x := hz
  have hpos : 0 < ‖(z : V) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos
end GlobalTheory.GaussCoset

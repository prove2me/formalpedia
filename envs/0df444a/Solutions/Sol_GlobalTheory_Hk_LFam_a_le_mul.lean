-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.a_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.755803+00:00
-- url     : https://prove2.me/submissions/75c186d4-f66d-4e93-bfd5-a65efd529914

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n hn1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (f := 𝓕.a g) (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h4 : 𝓕.κ * n ≤ 4 * n := by gcongr; exact 𝓕.κ_le
  linarith
end LFam
end GlobalTheory.Hk

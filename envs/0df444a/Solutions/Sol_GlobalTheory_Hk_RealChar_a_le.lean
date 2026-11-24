-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.a_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:05.403957+00:00
-- url     : https://prove2.me/submissions/87ab9e36-3ccd-44de-bd48-c6f3378d906a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n h1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h4 : 𝓕.κ * n ≤ 4 * n := mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)
  linarith
end GlobalTheory.Hk.RealChar

-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.besW_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:00.875797+00:00
-- url     : https://prove2.me/submissions/7253ed5e-b75b-404a-8f50-1ed5647b8355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
import Theorems.Thm_GlobalTheory_Hk_RealChar_besW_nonneg
import Theorems.Thm_GlobalTheory_Hk_RealChar_hasSum_pairs

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
theorem _root_.solution {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    (a1 : a 1 = 1) (b1 : b 1 = 1)
    (hr : ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) {v : ℝ} (hv : 0 < v) :
    besW v ≤ ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have H := (hasSum_pairs ha hb hv).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have e : ∀ n : ℕ, ∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n},
      a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2)
      = (∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) * besW (v * n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
          a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2) = 0 := by
        rintro ⟨⟨m, n⟩, hp⟩
        have hp' : m * n = 0 := hp
        rcases Nat.mul_eq_zero.1 hp' with rfl | rfl <;> simp [a0, b0]
      simp [this]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
        Finset.tsum_subtype' n.divisorsAntidiagonal
          fun p => a p.1 * b p.2 * besW (v * p.1 * p.2), Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.1 hp).1, Nat.cast_mul, mul_assoc v]
  simp only [e] at H
  have := le_hasSum H 1 fun n _ => mul_nonneg (hr n) (besW_nonneg _)
  simpa [a1, b1] using this
end GlobalTheory.Hk.RealChar

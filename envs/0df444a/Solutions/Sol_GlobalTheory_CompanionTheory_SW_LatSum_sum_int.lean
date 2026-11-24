-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.sum_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:30.847376+00:00
-- url     : https://prove2.me/submissions/8604fc37-20e9-4b1f-8eed-c01a0eae0069

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_hasSum_tele
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_pt_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution {t y : ℝ} (ht : 0 < t) (hy : t ≤ y) (m : ℕ) :
    Summable (fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) ∧
      ∑' k : ℤ, ((|(k : ℝ)| + y) ^ (m + 2))⁻¹ ≤ 2 * (1 + 1 / t) * (y * (y ^ (m + 2))⁻¹) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨B, hB⟩ : ∃ B, B = (1 + 1 / t) * (y ^ m)⁻¹ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hs : HasSum (fun n : ℕ => B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1))) (B * (1 / y)) :=
    (hasSum_tele hy0).mul_left B
  have nn : ∀ k : ℤ, 0 ≤ ((|(k : ℝ)| + y) ^ (m + 2))⁻¹ := fun k => by positivity
  have hp : ∀ n : ℕ, ((|(((n : ℤ)) : ℝ)| + y) ^ (m + 2))⁻¹
      ≤ B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) := by
    intro n
    have e : |(((n : ℤ)) : ℝ)| = (n : ℝ) := by simp
    rw [e, hB]
    exact pt_bound ht hy (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) m
  have hn : ∀ n : ℕ, ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| + y) ^ (m + 2))⁻¹
      ≤ B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) := by
    intro n
    refine le_trans ?_ (hp n)
    have e : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have e' : |(((n : ℤ)) : ℝ)| = (n : ℝ) := by simp
    rw [e, e']
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have s1 : Summable (fun n : ℕ => ((|(((n : ℤ)) : ℝ)| + y) ^ (m + 2))⁻¹) :=
    Summable.of_nonneg_of_le (fun n => nn n) hp hs.summable
  have s2 : Summable (fun n : ℕ => ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| + y) ^ (m + 2))⁻¹) :=
    Summable.of_nonneg_of_le (fun n => nn _) hn hs.summable
  refine ⟨Summable.of_nat_of_neg_add_one (f := fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) s1 s2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) s1 s2]
  have e1 := s1.tsum_le_tsum hp hs.summable
  have e2 := s2.tsum_le_tsum hn hs.summable
  rw [hs.tsum_eq] at e1 e2
  have e3 : B * (1 / y) = (1 + 1 / t) * (y * (y ^ (m + 2))⁻¹) := by
    rw [hB]
    field_simp
    ring
  rw [e3] at e1 e2
  linarith
end GlobalTheory.CompanionTheory.SW.LatSum

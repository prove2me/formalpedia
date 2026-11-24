-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleStableRange.local_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:19.551189+00:00
-- url     : https://prove2.me/submissions/4ee6a99d-d256-402e-ab96-ee16c41b973d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleStableRange
namespace GlobalTheory.CompanionTheory.AdeleStableRange
theorem _root_.solution {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, (t = 0 ∨ t = 1) ∧ a + t * b ≠ 0 ∧
      (w a ≤ 1 → w b ≤ 1 → w x ≤ 1 → w y ≤ 1 → w (a + t * b) = 1) := by
  have hb0 : a = 0 → b ≠ 0 := by
    rintro rfl rfl
    simp at h
  by_cases hint : w a ≤ 1 ∧ w b ≤ 1 ∧ w x ≤ 1 ∧ w y ≤ 1
  · obtain ⟨ha, hb, hx, hy⟩ := hint
    by_cases ha1 : w a = 1
    · refine ⟨0, Or.inl rfl, ?_, ?_⟩
      · intro h0
        have : a = 0 := by simpa using h0
        rw [this, map_zero] at ha1
        exact zero_ne_one ha1
      · intro _ _ _ _
        simpa using ha1
    · have hlt : w a < 1 := lt_of_le_of_ne ha ha1
      have hxa : w (x * a) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hlt
      have hyb : w (y * b) = 1 := by
        have h1 : y * b = 1 + (-(x * a)) := by linear_combination h
        rw [h1, Valuation.map_add_eq_of_lt_left w (by rw [Valuation.map_neg, map_one]; exact hxa),
          map_one]
      have hb1 : w b = 1 := by
        refine le_antisymm hb ?_
        rw [map_mul] at hyb
        rw [← hyb]
        exact mul_le_of_le_one_left' hy
      have hab : w (a + 1 * b) = 1 := by
        rw [one_mul, Valuation.map_add_eq_of_lt_right w (by rw [hb1]; exact hlt), hb1]
      refine ⟨1, Or.inr rfl, ?_, fun _ _ _ _ => hab⟩
      intro h0
      rw [h0, map_zero] at hab
      exact zero_ne_one hab
  · by_cases ha0 : a = 0
    · refine ⟨1, Or.inr rfl, ?_, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩
      simpa [ha0] using hb0 ha0
    · refine ⟨0, Or.inl rfl, by simpa using ha0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hint⟩
end GlobalTheory.CompanionTheory.AdeleStableRange

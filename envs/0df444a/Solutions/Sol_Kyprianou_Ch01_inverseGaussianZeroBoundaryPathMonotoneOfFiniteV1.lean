-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianZeroBoundaryPathMonotoneOfFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:31:24.530817+00:00
-- url     : https://prove2.me/submissions/1a68a63b-0dcb-4334-977f-7d24f26d0e5d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageBarrierMonotone
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s → firstUpperPassage X (s : ℝ) ω ≠ ⊤) :
    Monotone (fun s : ℝ≥0 =>
      if s = 0 then (0 : ℝ)
      else match firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ)) := by
  intro s t hst
  by_cases hs : s = 0
  · subst s
    by_cases ht : t = 0
    · subst t
      simp
    · cases hpass : firstUpperPassage X (t : ℝ) ω with
      | top =>
          simp [ht, hpass]
      | coe x =>
          have hx : (0 : ℝ) ≤ (x : ℝ) := by
            have hx0 : (0 : ℝ≥0) ≤ x := zero_le
            exact_mod_cast hx0
          simpa [ht, hpass] using hx
  · have h0s : (0 : ℝ≥0) ≤ s := zero_le
    have hspos : 0 < s := lt_of_le_of_ne h0s (Ne.symm hs)
    have htpos : 0 < t := lt_of_lt_of_le hspos hst
    have hf_s := hFinite s hspos
    have hf_t := hFinite t htpos
    cases hpass_s : firstUpperPassage X (s : ℝ) ω with
    | top =>
        exact False.elim (hf_s (by simp [hpass_s]))
    | coe x =>
        cases hpass_t : firstUpperPassage X (t : ℝ) ω with
        | top =>
            exact False.elim (hf_t (by simp [hpass_t]))
        | coe y =>
            have hbarrier : firstUpperPassage X (s : ℝ) ω ≤
                firstUpperPassage X (t : ℝ) ω :=
              firstUpperPassageBarrierMonotone X (s : ℝ) (t : ℝ)
                (by exact_mod_cast hst) ω
            rw [hpass_s, hpass_t] at hbarrier
            have hxy : x ≤ y := WithTop.coe_le_coe.mp hbarrier
            have hreal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
            simpa [hs, ne_of_gt htpos, hpass_s, hpass_t] using hreal

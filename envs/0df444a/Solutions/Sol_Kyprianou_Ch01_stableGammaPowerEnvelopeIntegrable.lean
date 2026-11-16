-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:19:10.148817+00:00
-- url     : https://prove2.me/submissions/5e3dc2b4-5609-472f-b4e0-b6be3e1edd23

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
open MeasureTheory Real Set
set_option autoImplicit false

theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) := by
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, _⟩ | h2) <;> linarith
  rw [hsplit]
  apply IntegrableOn.union
  · have h1 : IntegrableOn (fun x : ℝ => u * x ^ (-alpha)) (Set.Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := -alpha) (by linarith)).const_mul u
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
      exact this
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [hx.2]
  · have h2 : IntegrableOn (fun x : ℝ => x ^ (-alpha - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have : ¬ x ≤ 1 := not_le.mpr hx
    simp [this]

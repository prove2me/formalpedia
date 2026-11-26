-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSupportedWindowIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:31:23.522388+00:00
-- url     : https://prove2.me/submissions/cbddee47-3a98-4c73-8a24-b412365ca42a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedFiniteSupportMemLpV1
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- A bounded measurable kernel supported on a finite mark band is integrable
and has integrable square on the physical time window. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : R (Icc 0 T ×ˢ B) < ⊤)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0) :
    IntegrableOn g (Icc 0 T ×ˢ univ) R ∧
      IntegrableOn (fun p => (g p)^2) (Icc 0 T ×ˢ univ) R := by
  let U := Icc 0 T ×ˢ (univ : Set ℝ)
  let S := (univ : Set ℝ) ×ˢ B
  have hS : MeasurableSet S := MeasurableSet.univ.prod hB
  have hmass : (R.restrict U) S < ⊤ := by
    rw [Measure.restrict_apply hS]
    simpa [U,S,prod_inter_prod,inter_comm] using hfin
  have h := Kyprianou.Ch04.boundedFiniteSupportMemLpV1 (R.restrict U) S hS hmass
    g hg C hb (fun p hp => hsupp p (fun hz => hp ⟨mem_univ _,hz⟩))
  exact ⟨h.1,h.2.integrable_sq⟩

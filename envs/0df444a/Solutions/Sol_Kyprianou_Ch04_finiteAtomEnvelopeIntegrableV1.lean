-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAtomEnvelopeIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:18:32.133886+00:00
-- url     : https://prove2.me/submissions/f0f2f53d-bda9-4399-88a3-ddefbff6fafb

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- Integrability of any real-valued weight supported on a finite physical atom window. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (g : ℝ → ℝ) (hg : Measurable g) :
    IntegrableOn (fun z : ℝ × ℝ => if 1 ≤ |z.2| then g z.2 else 0)
      (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R := by
  let A := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  let B := {z : ℝ × ℝ | 1 ≤ |z.2|}
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|}
  have hB : MeasurableSet B := measurableSet_le measurable_const measurable_snd.abs
  have hSub : B ∩ A ⊆ D := fun z hz => ⟨hz.2.1,lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hz.1⟩
  have hI : Integrable (fun z : ℝ × ℝ => g z.2) (R.restrict D) := by
    change Integrable _ (R.restrict _) 
    rw [hR]
    exact integrable_finsetSum_measure.mpr fun r _ => integrable_dirac (by simp)
  change Integrable (B.indicator (fun z => g z.2)) (R.restrict A)
  rw [integrable_indicator_iff hB,IntegrableOn,Measure.restrict_restrict hB]
  exact hI.mono_measure (Measure.restrict_mono hSub le_rfl)

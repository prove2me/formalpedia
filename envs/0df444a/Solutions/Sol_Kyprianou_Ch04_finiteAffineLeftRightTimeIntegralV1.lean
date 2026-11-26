-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineLeftRightTimeIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:47:36.169579+00:00
-- url     : https://prove2.me/submissions/4f273049-fcbf-49a2-a0c8-f6e41d4af355

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- The right and strict-left finite affine paths agree at Lebesgue-almost every time. -/
theorem solution (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (f : ℝ → ℝ → ℝ) (T : ℝ) :
    (∫ u in Icc (0 : ℝ) T,
      f u (d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0)) =
    ∫ u in Icc (0 : ℝ) T,
      f u (d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0) := by
  classical
  have hf : ((fun r : NNReal => (r : ℝ)) '' (S : Set NNReal)).Finite :=
    S.finite_toSet.image _
  have hnull : volume ((fun r : NNReal => (r : ℝ)) '' (S : Set NNReal)) = 0 :=
    hf.countable.measure_zero _
  apply integral_congr_ae
  have hAE : ∀ᵐ u ∂volume, u ∉ (fun r : NNReal => (r : ℝ)) '' (S : Set NNReal) :=
    ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using hnull)
  filter_upwards [ae_restrict_of_ae hAE] with u hu
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  have hn : (r : ℝ) ≠ u := fun h => hu ⟨r,hr,h⟩
  simp [le_iff_lt_or_eq,hn]

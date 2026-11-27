-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridWindowIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:46:12.889129+00:00
-- url     : https://prove2.me/submissions/f73647ff-b9a4-4d05-91ef-2dbc740c9bbd

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clippedGridWindowCellIntegralV1
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- Integrating the finite step coefficient against any integrable marked
window kernel gives the corresponding clipped weighted increment sum. -/
theorem solution (R : Measure (ℝ × ℝ)) (Q : ℝ × ℝ → ℝ)
    (T t : NNReal) (ht : t ≤ T) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (H : ℕ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)) R) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k) z.1.toNNReal) * Q z ∂ R) =
    ∑ k ∈ Finset.range n, H k *
      ((∫ z in Icc (0 : ℝ) ((min t (u (k+1)) : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) -
       ∫ z in Icc (0 : ℝ) ((min t (u k) : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) := by
  let D := Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ)
  have hDt : Integrable Q (R.restrict D) := hQ.mono_set
    (fun z hz => ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast ht)⟩,hz.2⟩)
  have he (k : ℕ) : Integrable (fun z : ℝ × ℝ =>
      (Ioc (u k) (u (k+1))).indicator (fun _ => H k) z.1.toNNReal * Q z)
      (R.restrict D) := by
    let A := (fun z : ℝ × ℝ => z.1.toNNReal) ⁻¹' Ioc (u k) (u (k+1))
    have hA : MeasurableSet A := measurableSet_Ioc.preimage
      (measurable_real_toNNReal.comp measurable_fst)
    have hi := (hDt.const_mul (H k)).indicator hA
    have heq : (fun z : ℝ × ℝ => (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k) z.1.toNNReal * Q z) = A.indicator (fun z => H k * Q z) := by
      funext z
      by_cases hz : z.1.toNNReal ∈ Ioc (u k) (u (k+1)) <;> simp [A,Set.indicator_apply,hz]
    rw [heq]
    exact hi
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun k _ => he k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact Kyprianou.Ch04.clippedGridWindowCellIntegralV1 R Q T t (u k) (u (k+1))
    ht (hu (Nat.le_succ k)) hQ (H k)

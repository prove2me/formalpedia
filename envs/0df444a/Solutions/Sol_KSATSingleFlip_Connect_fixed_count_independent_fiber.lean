-- Prove2me | solution 1 for KSATSingleFlip.Connect.fixed_count_independent_fiber
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:56:29.323695+00:00
-- url     : https://prove2.me/submissions/1dae99b9-fe30-41c9-ad1c-cb959f35ae84

import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_fixed_clause_count
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
    (N : Ω → ℕ) (j : ℕ) (hj : 1 ≤ j) (Q : Ω → Fin j → A)
    (hQ : Measurable Q) (hlaw : Measure.map Q P = Measure.pi (fun _ : Fin j => D))
    (hind : IndepFun N Q P) (F : List A → ℝ)
    (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
    (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
    (hins : ∀ (xs : List A) (i : ℕ) (a : A), |F (xs.insertIdx i a)-F xs| ≤ L) :
    P ({ω | N ω = j} ∩ {ω | F (List.ofFn (Q ω)) ≤
      (∫ x, F (List.ofFn x) ∂(Measure.pi (fun _ : Fin j => D)))-u}) ≤
      P {ω | N ω = j} * ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2))) := by
  let T : Set (Fin j → A) := {x | F (List.ofFn x) ≤
      (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => D)))-u}
  have hT : MeasurableSet T := measurableSet_le hF measurable_const
  have hind' := hind.measure_inter_preimage_eq_mul {j} T (measurableSet_singleton j) hT
  change P ({ω | N ω = j} ∩ {ω | F (List.ofFn (Q ω)) ≤
      (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => D)))-u}) =
      P {ω | N ω = j} * P (Q ⁻¹' T) at hind'
  rw [hind']
  have htail := KSATSingleFlip.Connect.lemma_2_6_fixed_clause_count j hj D F hF L u hL hu hins
  have hmap : P (Q ⁻¹' T) = (Measure.pi (fun _ : Fin j => D)) T := by
    rw [← Measure.map_apply hQ hT, hlaw]
  rw [hmap]
  exact mul_le_mul_right htail _

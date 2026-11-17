-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_pair_vectors_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:49.448764+00:00
-- url     : https://prove2.me/submissions/00927b9a-6bd0-429f-b405-b9829882caa0

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_pair_vectors_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : ∀ (i : Fin 3) (s : ℝ≥0),
      AEMeasurable (fun ω => F i ω s) P)
    (I J : Finset ℝ≥0) :
    ∀ i : Fin 3,
      AEMeasurable
        (fun ω => ((fun s : I => F i ω s),
          (fun s : J => F i ω s))) P := by
  intro i
  exact (aemeasurable_pi_lambda (fun ω (s : I) => F i ω s) fun s => hF i s).prodMk
    (aemeasurable_pi_lambda (fun ω (s : J) => F i ω s) fun s => hF i s)

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : ∀ (i : Fin 3) (s : ℝ≥0),
      AEMeasurable (fun ω => F i ω s) P)
    (I J : Finset ℝ≥0) :
    ∀ i : Fin 3,
      AEMeasurable
        (fun ω => ((fun s : I => F i ω s),
          (fun s : J => F i ω s))) P := by
  first
  | exact Kyprianou.ProofPreparation.finite_pair_vectors_aemeasurable
  | exact Kyprianou.ProofPreparation.finite_pair_vectors_aemeasurable ..
  | (apply Kyprianou.ProofPreparation.finite_pair_vectors_aemeasurable <;> assumption)

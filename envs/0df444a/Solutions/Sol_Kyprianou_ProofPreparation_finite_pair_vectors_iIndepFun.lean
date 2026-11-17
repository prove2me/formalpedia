-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_pair_vectors_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:50.186957+00:00
-- url     : https://prove2.me/submissions/8c03693c-0c15-4aa4-8182-6a154e2902aa

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_pair_vectors_iIndepFun
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : iIndepFun F P)
    (I J : Finset ℝ≥0) :
    iIndepFun
      (fun i ω =>
        ((fun s : I => F i ω s), (fun s : J => F i ω s))) P := by
  have hg : ∀ i : Fin 3, Measurable (fun x : ℝ≥0 → ℝ =>
      ((fun s : I => x s), (fun s : J => x s))) := fun i =>
    (measurable_pi_lambda _ fun s => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun s => measurable_pi_apply _)
  exact hF.comp (fun i (x : ℝ≥0 → ℝ) => ((fun s : I => x s), (fun s : J => x s))) hg

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : iIndepFun F P)
    (I J : Finset ℝ≥0) :
    iIndepFun
      (fun i ω =>
        ((fun s : I => F i ω s), (fun s : J => F i ω s))) P := by
  first
  | exact Kyprianou.ProofPreparation.finite_pair_vectors_iIndepFun
  | exact Kyprianou.ProofPreparation.finite_pair_vectors_iIndepFun ..
  | (apply Kyprianou.ProofPreparation.finite_pair_vectors_iIndepFun <;> assumption)

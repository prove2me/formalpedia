-- Prove2me | solution 1 for Kyprianou.Ch04.physicalRestrictedGeneratorSumIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:22:48.623148+00:00
-- url     : https://prove2.me/submissions/ce1e1c00-ce5d-415c-983f-c6b9f193fdb6

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteGeneratorSumTailRepresentation
import Theorems.Thm_Kyprianou_Ch04_physicalTailSumIsometry
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Physical finite-band isometry for finite sums of predictable generator indicators. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : nu B < ⊤)
    (k : ℕ) (D : Fin k → Set ((NNReal × Omega) × ℝ)) (c : Fin k → ℝ)
    (hD : ∀ i, D i ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) :
    let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    let K := fun w (z : ℝ × ℝ) => ∑ i, c i *
      (D i).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)
    let X := fun w => (∫ z in U, K w z ∂(N.N w)) -
      ∫ z in U, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in U, (K w z)^2 ∂referenceIntensity nu ∂P := by
  classical
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  let K := fun w (z : ℝ × ℝ) => ∑ i, c i *
    (D i).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)
  have hU : MeasurableSet U := measurableSet_Icc.prod hB
  obtain ⟨a,C,H,ha,hC,hCB,hH,hH2,he⟩ :=
    Kyprianou.Ch04.finiteGeneratorSumTailRepresentation P F t B hB k D c hD
  have hCfin (i : Fin k) : nu (C i) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono (hCB i))
  have hsec := Kyprianou.Ch04.physicalTailSumIsometry P nu F N hFuture hPast
    Finset.univ t a C H (fun i _ => ha i) (fun i _ => hC i) (fun i _ => hCfin i)
    (fun i _ => hH i) (fun i _ => hH2 i) (fun w => U.indicator (K w)) he
  have hsq (w : Omega) : (fun z => (U.indicator (K w) z)^2) =
      U.indicator (fun z => (K w z)^2) := by
    funext z
    by_cases hz : z ∈ U <;> simp [Set.indicator_apply, hz]
  dsimp only at hsec
  simpa only [integral_indicator hU, hsq] using hsec

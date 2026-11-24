-- Prove2me | solution 3 for Kyprianou.independentSubordinationCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:04:03.268807+00:00
-- url     : https://prove2.me/submissions/e43631bc-e4b6-4fd0-872f-cf080665490b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3
import Theorems.Thm_Kyprianou_independentSubordinationCh02
import Theorems.Thm_Kyprianou_Ch02_subordinatorComplexLaplaceFromTripletV1

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

set_option linter.unusedVariables false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ)
    (aτ : ℝ) (στ : ℝ≥0) (ντ : Measure ℝ)
    (hντ : ProbabilityTheory.IsLevyMeasure ντ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ))
    (hτchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => (τ t ω : ℝ))) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-aτ, στ ^ 2, ντ, hντ⟩ ξ)) :
    let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ)) := by
  -- Subordinator path criterion (Lemma 2.14, already Proved): recovers
  -- ντ(Iio 0)=0, στ=0, ∫ min(1,|x|) dντ < ∞ on (0,∞), and d ≥ 0.
  have hcrit :
      ντ (Set.Iio (0 : ℝ)) = 0 ∧
      στ = 0 ∧
      Integrable (fun x : ℝ => min (1 : ℝ) |x|)
        (ντ.restrict (Set.Ioi (0 : ℝ))) ∧
      0 ≤ -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ :=
    (Kyprianou.subordinatorCriterionCh02V3 aτ στ ντ hντ P
      (fun t ω => (τ t ω : ℝ)) hτ hτchar).mp hmon
  rcases hcrit with ⟨hneg, hsigma, hint, hdis⟩
  -- Complex Laplace transform of τ from its Lévy triplet.
  have hlaplace :
      let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
      let Ξ : ℂ → ℂ := fun z =>
        (d : ℂ) * z +
        ∫ x in Set.Ioi (0 : ℝ),
          (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
      ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
        ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
          Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z) :=
    Kyprianou.Ch02.subordinatorComplexLaplaceFromTripletV1
      P τ aτ στ ντ hντ hτ hτchar hneg hsigma hint hdis
  -- Independent subordination (Lemma 2.15): IsLevyProcess of X∘τ together
  -- with the composed characteristic exponent Ξ ∘ Ψ.
  exact
    Kyprianou.independentSubordinationCh02 P X τ Ψ
      (fun z =>
        (((-aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ : ℝ) : ℂ) * z +
          ∫ x in Set.Ioi (0 : ℝ),
            (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ))
      hX hτ hmon hind hψ hlaplace

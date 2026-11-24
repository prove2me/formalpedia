-- Prove2me | solution 2 for Kyprianou.independentSubordinationCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:26:24.849043+00:00
-- url     : https://prove2.me/submissions/a880514a-ad9b-4fe4-9972-2007687d20b7

import Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3
import Theorems.Thm_Kyprianou_independentSubordinationCh02
import Theorems.Thm_Kyprianou_Ch02_subordinatorComplexLaplaceFromTripletV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false


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
  have hm : ∀ᵐ ω ∂P, Monotone (fun t => (τ t ω : ℝ)) := by
    filter_upwards [hmon] with ω hw
    intro s t hst
    exact_mod_cast hw hst
  obtain ⟨hn, hs, hi, hd⟩ :=
    (Kyprianou.subordinatorCriterionCh02V3 aτ στ ντ hντ P
      (fun t ω => (τ t ω : ℝ)) hτ hτchar).mp hm
  dsimp
  exact Kyprianou.independentSubordinationCh02 P X τ Ψ
    (fun z => (((-aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ) : ℝ) : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ)
    hX hτ hmon hind hψ
    (Kyprianou.Ch02.subordinatorComplexLaplaceFromTripletV1
      P τ aτ στ ντ hντ hτ hτchar hn hs hi hd)



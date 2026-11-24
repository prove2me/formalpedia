-- Prove2me | solution 1 for Kyprianou.Ch02.levySmallJumpMassLIntegralEqOfPathLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:54:44.230237+00:00
-- url     : https://prove2.me/submissions/e82d436b-3890-43ba-99be-e682f8d8f347

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_cadlagSmallJumpMassBorelFunctionalV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem actualMass_ae_eq
    {A : Type} [MeasurableSpace A] (M : Measure A)
    (Z : ℝ≥0 → A → ℝ) (hZ : IsLevyProcess Z M) (T : ℝ≥0)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hRep : ∀ (Y : ℝ≥0 → ℝ),
      (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
      (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
      F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal (if |Y (s : ℝ≥0) -
          Function.leftLim Y (s : ℝ≥0)| ≤ (1 : ℝ)
          then |Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)| else 0)) :
    (fun ω : A => F (fun t : ℝ≥0 => Z t ω)) =ᵐ[M]
      (fun ω : A => ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal (if |Z (s : ℝ≥0) ω -
          Function.leftLim (fun u : ℝ≥0 => Z u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
          then |Z (s : ℝ≥0) ω -
            Function.leftLim (fun u : ℝ≥0 => Z u ω) (s : ℝ≥0)| else 0)) := by
  filter_upwards [hZ.cadlag_ae] with ω hω
  exact hRep (fun t => Z t ω) (fun t => (hω t).1) (fun t _ => (hω t).2)

/-- Source-faithful Chapter 2 proof. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hpath :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q)
    (T : ℝ≥0) :
    (∫⁻ ω : Ω, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) =
      (∫⁻ ω : Λ, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |Y (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |Y (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|
           else 0) ∂Q) := by
  obtain ⟨F, hF, hRep⟩ :=
    Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1 T
  have hA := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  have hB := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 Q Y hY
  have hEqX := actualMass_ae_eq P X hX T F hRep
  have hEqY := actualMass_ae_eq Q Y hY T F hRep
  rw [← lintegral_congr_ae hEqX, ← lintegral_congr_ae hEqY]
  rw [← lintegral_map' hF.aemeasurable hA,
    ← lintegral_map' hF.aemeasurable hB, hpath]

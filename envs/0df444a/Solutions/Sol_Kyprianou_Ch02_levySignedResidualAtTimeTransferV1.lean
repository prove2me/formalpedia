-- Prove2me | solution 1 for Kyprianou.Ch02.levySignedResidualAtTimeTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:18.369253+00:00
-- url     : https://prove2.me/submissions/3ab43cb8-e654-49e1-9b31-615e7d5497a4

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagSignedJumpSeriesBorelFunctionalV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer the measurable signed residual equality through the path law. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hpath : Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q)
    (T : ℝ≥0) (d : ℝ)
    (hXs : ∀ᵐ ω ∂P, Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|))
    (hYs : ∀ᵐ ω ∂Q, Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|))
    (hYeq : ∀ᵐ ω ∂Q, Y T ω = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T,
        (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) :
    ∀ᵐ ω ∂P, X T ω = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T,
        (X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)) := by
  obtain ⟨F, hF, hrep⟩ := Kyprianou.Ch02.cadlagSignedJumpSeriesBorelFunctionalV1 T
  let A : Ω → (ℝ≥0 → ℝ) := fun ω t => X t ω
  let B : Λ → (ℝ≥0 → ℝ) := fun ω t => Y t ω
  have hA : AEMeasurable A P :=
    Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  have hB : AEMeasurable B Q :=
    Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 Q Y hY
  let E : Set (ℝ≥0 → ℝ) := {f | f T ≠ d * (T : ℝ) + F f}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (measurable_pi_apply T)
      (measurable_const.add hF)).compl
  have hYgood : ∀ᵐ ω ∂Q, B ω ∉ E := by
    filter_upwards [hY.cadlag_ae, hYs, hYeq] with ω hc hs he
    have h := hrep (B ω) (fun t => (hc t).1) (fun t _ => (hc t).2) hs
    simpa only [E, Set.mem_setOf_eq, not_not, h] using he
  have hzero : Q (B ⁻¹' E) = 0 := by
    have h := (ae_iff (p := fun ω : Λ => B ω ∉ E)).mp hYgood
    have heq : {ω : Λ | ¬ B ω ∉ E} = B ⁻¹' E := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, not_not]
    rw [heq] at h
    exact h
  have hzeroP : P (A ⁻¹' E) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hA hE, hpath,
      Measure.map_apply_of_aemeasurable hB hE, hzero]
  have hXgood : ∀ᵐ ω ∂P, A ω ∉ E := by
    apply ae_iff.mpr
    have heq : {ω : Ω | ¬ A ω ∉ E} = A ⁻¹' E := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, not_not]
    rw [heq]
    exact hzeroP
  filter_upwards [hX.cadlag_ae, hXs, hXgood] with ω hc hs he
  have h := hrep (A ω) (fun t => (hc t).1) (fun t _ => (hc t).2) hs
  simpa only [E, Set.mem_setOf_eq, not_not, h] using he

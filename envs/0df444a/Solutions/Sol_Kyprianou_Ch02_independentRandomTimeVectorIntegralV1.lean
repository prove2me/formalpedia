-- Prove2me | solution 1 for Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:55:53.431387+00:00
-- url     : https://prove2.me/submissions/cb45a479-f53c-43a8-a323-d3e41dfad8ed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_measurableUniversalRightTimeEvaluationV1
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_independentAEMeasurablePairIntegralV1
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : IsLevyProcess X P)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hind : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (m : ℕ) (t : Fin m → ℝ≥0)
    (G : (Fin m → ℝ) → ℂ) (hG : Measurable G) :
    AEMeasurable (fun ω => fun i : Fin m => X (τ (t i) ω) ω) P ∧
    (∀ C : ℝ, (∀ x, ‖G x‖ ≤ C) →
      (∫ ω, G (fun i => X (τ (t i) ω) ω) ∂P) =
        ∫ ω, (∫ ω', G (fun i => X (τ (t i) ω) ω') ∂P) ∂P) := by
  obtain ⟨E, hE, hEval⟩ := Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
  let A (ω : Ω) : ℝ≥0 → ℝ := fun s => X s ω
  let B (ω : Ω) : ℝ≥0 → ℝ := fun s => (τ s ω : ℝ)
  have hA : AEMeasurable A P := Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
    P X hX.cadlag_ae (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX)
  have hB : AEMeasurable B P := Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
    P _ hτ.cadlag_ae (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P _ hτ)
  have hInd : IndepFun B A P := by
    simpa [A, B] using hind.indepFun (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
  let V (b : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (i : Fin m) :=
    E (b.2, (b.1 (t i)).toNNReal)
  have hV : Measurable V := measurable_pi_iff.2 (fun i =>
    hE.comp (measurable_snd.prodMk
      (measurable_real_toNNReal.comp ((measurable_pi_apply (t i)).comp measurable_fst))))
  have hgood : ∀ᵐ ω ∂P, IsCadlag (A ω) := hX.cadlag_ae
  have hv_eq : (fun ω => fun i => X (τ (t i) ω) ω) =ᵐ[P]
      (fun ω => V (B ω, A ω)) := by
    filter_upwards [hgood] with ω hw
    funext i
    simp only [V, B, Real.toNNReal_coe]
    exact (hEval (A ω) (fun s => (hw s).1) _).symm
  refine ⟨(hV.comp_aemeasurable (hB.prodMk hA)).congr hv_eq.symm, ?_⟩
  intro C hC
  let F := G ∘ V
  have hFm : Measurable F := hG.comp hV
  calc
    (∫ ω, G (fun i => X (τ (t i) ω) ω) ∂P) =
        ∫ ω, F (B ω, A ω) ∂P := integral_congr_ae (hv_eq.fun_comp G)
    _ = ∫ ω, (∫ ω', F (B ω, A ω') ∂P) ∂P :=
      Kyprianou.Ch02.independentAEMeasurablePairIntegralV1 P B A hB hA hInd
        F hFm C (fun x => hC (V x))
    _ = ∫ ω, (∫ ω', G (fun i => X (τ (t i) ω) ω') ∂P) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      apply integral_congr_ae
      filter_upwards [hX.cadlag_ae] with ω' hc
      change G (V (B ω, A ω')) = _
      congr 1
      funext i
      simp only [V, B, Real.toNNReal_coe]
      exact hEval (A ω') (fun s => (hc s).1) _

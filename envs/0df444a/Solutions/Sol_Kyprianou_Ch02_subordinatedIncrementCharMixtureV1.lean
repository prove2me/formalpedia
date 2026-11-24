-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:32.807184+00:00
-- url     : https://prove2.me/submissions/813c7c1a-50ef-4ab9-b101-e747cb7a23a7

import Theorems.Thm_Kyprianou_Ch02_independentRandomTimeVectorIntegralV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyIncrementCharFunEqualsLagV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (s t : ℝ≥0) (hst : s ≤ t) (ξ : ℝ) :
    AEMeasurable (increment (fun t ω => X (τ t ω) ω) s t) P ∧
    charFun (P.map (increment (fun t ω => X (τ t ω) ω) s t)) ξ =
      ∫ ω, charFun (P.map (X (τ t ω - τ s ω))) ξ ∂P := by
  let times : Fin 2 → ℝ≥0 := fun i => if i = 0 then s else t
  let G : (Fin 2 → ℝ) → ℂ := fun v =>
    Complex.exp ((ξ : ℂ) * ((v 1 - v 0 : ℝ) : ℂ) * Complex.I)
  have hG : Measurable G := by unfold G; fun_prop
  have hb : ∀ v, ‖G v‖ ≤ 1 := by
    intro v
    simp [G, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  obtain ⟨hm, he⟩ :=
    Kyprianou.Ch02.independentRandomTimeVectorIntegralV1 P X τ hX hτ hind 2 times G hG
  have h1 := (measurable_pi_apply (1 : Fin 2)).comp_aemeasurable hm
  have h0 := (measurable_pi_apply (0 : Fin 2)).comp_aemeasurable hm
  have hd : AEMeasurable (increment (fun t ω => X (τ t ω) ω) s t) P := by
    have h1' : AEMeasurable (fun ω => X (τ t ω) ω) P := by
      simpa [times, Function.comp_def] using h1
    have h0' : AEMeasurable (fun ω => X (τ s ω) ω) P := by
      simpa [times, Function.comp_def] using h0
    exact h1'.sub h0'
  refine ⟨hd, ?_⟩
  rw [charFun_apply_real, integral_map hd (by fun_prop)]
  calc
    _ = ∫ ω, (∫ ω', G (fun i => X (τ (times i) ω) ω') ∂P) ∂P := by
      simpa [G, times, increment] using he 1 hb
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hmon] with ω hω
      rw [← Kyprianou.Ch02.levyIncrementCharFunEqualsLagV1 P X hX
        (τ s ω) (τ t ω) (hω hst) ξ, charFun_apply_real]
      have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
      have hm' : AEMeasurable (increment X (τ s ω) (τ t ω)) P :=
        (hcoord (τ t ω)).sub (hcoord (τ s ω))
      rw [integral_map hm' (by fun_prop)]
      simp [G, times, increment]

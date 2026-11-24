-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationMarginalMixtureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:56:21.69816+00:00
-- url     : https://prove2.me/submissions/d3e53619-c317-45f3-80bf-80e8888d0497

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_independentRandomTimeVectorIntegralV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
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
    (Ψ : ℝ → ℂ)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
        ∫ ω, Complex.exp (-(((τ t ω : ℝ) : ℂ)) * Ψ ξ) ∂P := by
  intro t ξ
  let G : (Fin 1 → ℝ) → ℂ := fun v => Complex.exp ((ξ : ℂ) * (v 0 : ℂ) * I)
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  obtain ⟨hm, hmix⟩ := Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
    P X τ hX hτ hind 1 (fun _ => t) G hG
  have hm' : AEMeasurable (fun ω => X (τ t ω) ω) P :=
    (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable hm
  have hbound (v : Fin 1 → ℝ) : ‖G v‖ ≤ 1 := by
    simp [G, Complex.norm_exp, mul_re, mul_im]
  rw [charFun_apply_real, integral_map hm']
  · change (∫ ω, G (fun _ => X (τ t ω) ω) ∂P) = _
    rw [hmix 1 hbound]
    apply integral_congr_ae
    filter_upwards with ω
    rw [← hψ (τ t ω) ξ, charFun_apply_real,
      integral_map (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX (τ t ω))]
    · exact (by fun_prop : Measurable
        (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * I))).aestronglyMeasurable
  · exact (by fun_prop : Measurable
      (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * I))).aestronglyMeasurable

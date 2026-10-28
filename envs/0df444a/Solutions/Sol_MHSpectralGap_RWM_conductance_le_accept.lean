-- Prove2me | solution 1 for MHSpectralGap.RWM.conductance_le_accept
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:33:46.618219+00:00
-- url     : https://prove2.me/submissions/fe177cfa-93aa-40c1-8a09-9132ebf39a8f

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Aux_MHSG_cond

open MHSpectralGap.RWM

lemma kernel_le {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel Q] (α : X → X → ℝ≥0∞)
    (hα : Measurable (Function.uncurry α)) (A : Set X) (hA : MeasurableSet A) (x : X)
    (hx : x ∈ A) : mhKernel Q α x Aᶜ ≤ accBar Q α x := by
  unfold mhKernel
  rw [Kernel.add_apply, Measure.add_apply]
  have h1 : Q.withDensity (fun x y => α x y) x Aᶜ ≤ accBar Q α x := by
    rw [Kernel.withDensity_apply Q (f := fun x y => α x y) hα, withDensity_apply _ hA.compl]
    exact setLIntegral_le_lintegral _ _
  have h2 : (ProbabilityTheory.Kernel.withDensity ProbabilityTheory.Kernel.id
      (fun x (_ : X) => ∫⁻ u, (1 - α x u) ∂(Q x))) x Aᶜ = 0 := by
    by_cases hm : Measurable (Function.uncurry
        (fun x (_ : X) => ∫⁻ u, (1 - α x u) ∂(Q x)))
    · rw [Kernel.withDensity_apply _ hm, withDensity_apply _ hA.compl, Kernel.id_apply]
      have : (Measure.dirac x).restrict Aᶜ = 0 := by
        rw [Measure.restrict_eq_zero, Measure.dirac_apply' _ hA.compl]
        simp [hx]
      rw [this, lintegral_zero_measure]
    · rw [Kernel.withDensity_of_not_measurable _ hm]
      simp
  rw [h2, add_zero]
  exact h1

end Aux_MHSG_cond

open MHSpectralGap.RWM Aux_MHSG_cond in
theorem solution {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel Q] (α : X → X → ℝ≥0∞)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ x y, α x y ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    conductance (mhKernel Q α) μ ≤
        ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
          (∫⁻ x in A, accBar Q α x ∂μ) / μ A ∧
      ∀ B : Set X, MeasurableSet B → 0 < μ B → μ B ≤ 1 / 2 →
        conductance (mhKernel Q α) μ ≤ ⨆ x ∈ B, accBar Q α x := by
  have hstep : ∀ A : Set X, MeasurableSet A →
      (∫⁻ x in A, mhKernel Q α x Aᶜ ∂μ) / μ A ≤ (∫⁻ x in A, accBar Q α x ∂μ) / μ A := by
    intro A hA
    apply ENNReal.div_le_div_right
    exact setLIntegral_mono' hA (fun x hx => kernel_le Q α hα A hA x hx)
  have part1 : conductance (mhKernel Q α) μ ≤
      ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
        (∫⁻ x in A, accBar Q α x ∂μ) / μ A := by
    unfold conductance
    exact iInf_mono fun A => iInf_mono fun hA => iInf_mono fun _ => iInf_mono fun _ =>
      hstep A hA
  refine ⟨part1, fun B hB h0 h1 => ?_⟩
  refine le_trans part1 ?_
  refine le_trans (iInf_le_of_le B (iInf_le_of_le hB (iInf_le_of_le h0 (iInf_le _ h1)))) ?_
  have hint : ∫⁻ x in B, accBar Q α x ∂μ ≤ ∫⁻ _ in B, (⨆ x ∈ B, accBar Q α x) ∂μ :=
    setLIntegral_mono' hB (fun x hx =>
      le_iSup₂ (f := fun x (_ : x ∈ B) => accBar Q α x) x hx)
  rw [setLIntegral_const] at hint
  calc (∫⁻ x in B, accBar Q α x ∂μ) / μ B
      ≤ ((⨆ x ∈ B, accBar Q α x) * μ B) / μ B := ENNReal.div_le_div_right hint _
    _ = ⨆ x ∈ B, accBar Q α x := ENNReal.mul_div_cancel_right h0.ne' (measure_ne_top μ B)

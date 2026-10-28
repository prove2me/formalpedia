-- Prove2me | solution 1 for MarkovProcess.condExp_comp_ae_eq_integral_kernel_of_restrict_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:58:37.507295+00:00
-- url     : https://prove2.me/submissions/b4728c89-ce2c-4b6e-9d1a-5f2e08edcb9f

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
open MeasureTheory ProbabilityTheory
variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

theorem solution
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F)
    (hFm : StronglyMeasurable[m] (fun omega ↦ ∫ y, F y ∂kappa omega))
    (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    mu[fun omega ↦ F (Y omega)|m] =ᵐ[mu]
      fun omega ↦ ∫ y, F y ∂kappa omega := by
  haveI : IsFiniteMeasure (mu.trim hm) := isFiniteMeasure_trim hm
  have hgb : ∀ ω, ‖∫ y, F y ∂kappa ω‖ ≤ C := fun ω => by
    have := norm_integral_le_of_norm_le_const (μ := kappa ω) (C := C)
      (Filter.Eventually.of_forall hFC)
    simpa using this
  have hgm : StronglyMeasurable[mOmega] (fun omega ↦ ∫ y, F y ∂kappa omega) := hFm.mono hm
  have hf : Integrable (fun omega ↦ F (Y omega)) mu :=
    Integrable.of_bound (hF.comp_measurable hY).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hFC _)
  have hg : Integrable (fun omega ↦ ∫ y, F y ∂kappa omega) mu :=
    Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hgb)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hg.integrableOn)
    (fun s hs _ => ?_) hFm.aestronglyMeasurable).symm
  have h1 : ∫ x in s, F (Y x) ∂mu = ∫ y, F y ∂((mu.restrict s).map Y) :=
    (integral_map hY.aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, hJoint s hs, Measure.comp_eq_comp_const_apply]
  have hint : Integrable F ((kappa ∘ₖ Kernel.const Unit (mu.restrict s)) ()) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hFC)
  rw [Kernel.integral_comp hint]
  simp [Kernel.const_apply]

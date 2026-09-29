-- Prove2me | solution 1 for InformationTheory.compProd_categorical_kl_le_marginal_entropy_general
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:26:07.303566+00:00
-- url     : https://prove2.me/submissions/53bb5cd3-db81-43bb-aa17-4ec5a1a59631

import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_kernel_average_categorical_kl_le_marginal_entropy_general
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Mathlib.Probability.Kernel.Posterior

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators ProbabilityTheory

namespace InformationTheory

theorem _root_.solution
    {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    (klDiv (mu ⊗ₘ kappa)
      (mu ⊗ₘ Kernel.const Alpha (kappa ∘ₘ mu))).toReal ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  let p : Measure (Fin k) := kappa ∘ₘ mu
  letI : IsProbabilityMeasure p := by
    dsimp [p]
    infer_instance
  have hac : ∀ᵐ x ∂mu, kappa x ≪ p := by
    have hsingle (a : Fin k) (ha : p {a} = 0) :
        ∀ᵐ x ∂mu, kappa x {a} = 0 := by
      dsimp [p] at ha
      rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable] at ha
      rw [lintegral_eq_zero_iff
        (Kernel.measurable_coe kappa (MeasurableSet.singleton a))] at ha
      exact ha
    have hall : ∀ᵐ x ∂mu, ∀ a : Fin k, p {a} = 0 → kappa x {a} = 0 := by
      rw [ae_all_iff]
      intro a
      by_cases ha : p {a} = 0
      · filter_upwards [hsingle a ha] with x hx
        exact fun _ ↦ hx
      · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
    filter_upwards [hall] with x hx
    apply Measure.AbsolutelyContinuous.mk
    intro s _ hs
    have hs' : p (↑s.toFinite.toFinset : Set (Fin k)) = 0 := by simpa using hs
    have hzero : ∀ a ∈ s.toFinite.toFinset, kappa x {a} = 0 := by
      intro a ha
      apply hx a
      exact measure_mono_null (Set.singleton_subset_iff.mpr ha) hs'
    rw [← Set.Finite.coe_toFinset s.toFinite, ← sum_measure_singleton]
    exact Finset.sum_eq_zero hzero
  have hlt : ∀ᵐ x ∂mu, klDiv (kappa x) p < ∞ := by
    filter_upwards [hac] with x hx
    exact (lt_top_iff_ne_top.mpr (klDiv_ne_top hx Integrable.of_finite))
  have hmeas : AEMeasurable (fun x ↦ klDiv (kappa x) p) mu := by
    have htoReal_meas : AEMeasurable (fun x ↦ (klDiv (kappa x) p).toReal) mu := by
      let F : Alpha → ℝ := fun x ↦ ∑ a,
        (kappa x).real {a} *
          Real.log ((kappa x).real {a} / p.real {a})
      have hF_meas : Measurable F := by
        apply Finset.measurable_sum
        intro a _
        have hqa : Measurable (fun x ↦ (kappa x).real {a}) :=
          (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).ennreal_toReal
        exact hqa.mul (Real.measurable_log.comp (hqa.div_const _))
      have heq : (fun x ↦ (klDiv (kappa x) p).toReal) =ᵐ[mu] F := by
        filter_upwards [hac] with x hx
        exact categorical_toReal_klDiv_eq_sum (kappa x) p hx
      exact hF_meas.aemeasurable.congr heq.symm
    apply AEMeasurable.congr (htoReal_meas.ennreal_ofReal) ?_
    filter_upwards [hlt] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  rw [klDiv_compProd_self_eq_lintegral_of_ae mu kappa (Kernel.const Alpha p) (by simpa using hac)]
  simp only [Kernel.const_apply]
  rw [← integral_toReal hmeas hlt]
  exact kernel_average_categorical_kl_le_marginal_entropy_general mu kappa

end InformationTheory

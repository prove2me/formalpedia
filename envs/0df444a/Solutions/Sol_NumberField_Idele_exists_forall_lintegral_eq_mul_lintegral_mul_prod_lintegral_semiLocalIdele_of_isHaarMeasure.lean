-- Prove2me | solution 1 for NumberField.Idele.exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bd15cd67-a510-5a41-8171-ed057759bfd2

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_MeasureTheory_Measure_exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Theorems.Thm_NumberField_Idele_continuous_semiLocalIdele_and_continuous_archSemiLocalIdele
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel

attribute [local instance] AutomorphicForm.TransversalMeasure.archUnitsBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (ν : Measure (AdeleRing (𝓞 L) L)ˣ)
    [ν.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    ∃ (νa : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ))
      (νf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ),
      @Measure.IsHaarMeasure (InfiniteAdeleRing L)ˣ _ _ (borel (InfiniteAdeleRing L)ˣ) νa ∧
      (∀ v, (νf v).IsHaarMeasure ∧
        νf v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
        @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g →
        (∀ v ∈ S, Measurable (f v)) →
        ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂ν =
          c * (∫⁻ x, g x ∂νa) * ∏ v ∈ S, ∫⁻ x, f v x ∂(νf v) := by
  classical
  obtain ⟨hsc, hfin, hinf, hP, hsurj, hbox, -, -⟩ := NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K L
  obtain ⟨hcf, hca⟩ := NumberField.Idele.continuous_semiLocalIdele_and_continuous_archSemiLocalIdele K L
  obtain ⟨E, hE⟩ := NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre K L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := hsc
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ := fun v => (hfin v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), LocallyCompactSpace (L ⊗[K] v.adicCompletion K)ˣ := fun v => (hfin v).2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), T2Space (L ⊗[K] v.adicCompletion K)ˣ := fun v => (hfin v).2.2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), SecondCountableTopology (L ⊗[K] v.adicCompletion K)ˣ :=
    fun v => (hfin v).2.2.2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := fun v => ⟨rfl⟩
  haveI : ∀ v : InfinitePlace K, IsTopologicalGroup (∀ w : v.Extension L, w.1.Completion)ˣ := fun v => (hinf v).1
  haveI : ∀ v : InfinitePlace K, LocallyCompactSpace (∀ w : v.Extension L, w.1.Completion)ˣ := fun v => (hinf v).2.1
  haveI : ∀ v : InfinitePlace K, T2Space (∀ w : v.Extension L, w.1.Completion)ˣ := fun v => (hinf v).2.2.1
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology (∀ w : v.Extension L, w.1.Completion)ˣ := fun v => (hinf v).2.2.2
  haveI : ∀ v : InfinitePlace K, BorelSpace (∀ w : v.Extension L, w.1.Completion)ˣ := fun v => ⟨rfl⟩
  obtain ⟨νA, νG, hνA, hνG, hfac⟩ :=
    MeasureTheory.Measure.exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
      (B := (AdeleRing (𝓞 L) L)ˣ) (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L) hca
      (AutomorphicForm.TransversalMeasure.semiLocalIdele K L) hcf (AutomorphicForm.TransversalMeasure.integralUnits K L)
      (fun v => (hfin v).2.2.2.2.1) (fun v => (hfin v).2.2.2.2.2) hP hsurj hbox ν
  letI mI : MeasurableSpace (InfiniteAdeleRing L)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing L)ˣ := ⟨rfl⟩
  have hEsm : Measurable E.symm := E.symm.continuous.measurable
  haveI := hνA
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, Measure.map E.symm νA, νG, inferInstance, hνG, ?_⟩
  intro S g f hg hf
  have key := hfac S (fun y => g (E.symm y)) f (hg.comp hEsm) hf
  have hq : ∀ t : (AdeleRing (𝓞 L) L)ˣ,
      Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t =
        E.symm (fun v => AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t) := by
    intro t
    apply E.injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    funext v
    exact hE _ v
  calc ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂ν
      = ∫⁻ t, (fun y => g (E.symm y)) (fun v => AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂ν := by
        refine lintegral_congr fun t => ?_
        rw [hq t]
    _ = (∫⁻ y, g (E.symm y) ∂νA) * ∏ v ∈ S, ∫⁻ x, f v x ∂(νG v) := key
    _ = 1 * (∫⁻ x, g x ∂(Measure.map E.symm νA)) * ∏ v ∈ S, ∫⁻ x, f v x ∂(νG v) := by
        rw [lintegral_map hg hEsm, one_mul]

end S_NumberField_Idele_exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure
end P2MW
export P2MW.S_NumberField_Idele_exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure (solution)

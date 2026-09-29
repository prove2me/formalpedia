-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f7f0657f-08f1-552d-a97f-ad17a72b604e

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by

  obtain ⟨a, ha0, ha⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  let ψ' : AddChar (AdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a))
  have hψ'_apply : ∀ y, ψ' y = ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) := fun y => rfl

  have hψ' : IsGlobalAddChar F ψ' := by
    refine ⟨?_, ?_, ?_⟩
    · intro ξ
      show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1
      rw [← map_mul]
      exact hψ.principalInvariant (a * ξ)
    · show Continuous fun y => ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y)
      exact hψ.continuous.comp (continuous_const.mul continuous_id)
    · intro h1
      apply hψ.nontrivial
      ext z
      have hz := DFunLike.congr_fun h1 (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * z)
      rw [hψ'_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul] at hz
      rw [hz, AddChar.one_apply, AddChar.one_apply]

  have hψ'_inf : ∀ x : InfiniteAdeleRing F,
      ψ' (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    rw [hψ'_apply, ← ha x]
    congr 1
    exact Prod.ext rfl (mul_zero _)

  have hB := NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
    F μ hμB hψ' hψ'_inf hf
  rw [hB]

  have hFI : ∀ w, fourierIntegral ψ' μ f w
      = fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) a * w) := by
    intro w
    simp only [fourierIntegral_def, hψ'_apply]
    congr 1 with v
    congr 2
    ring
  simp_rw [hFI, ← map_mul]

  exact (Equiv.mulLeft₀ a ha0).tsum_eq
    (fun ξ => fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ))

end S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one (solution)

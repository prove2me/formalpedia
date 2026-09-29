-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/51b19161-bff1-514d-8946-264f89ac3f5d

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

open NumberField NumberField.AdelicFourier AutomorphicForm

set_option maxHeartbeats 3200000 in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by

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
  have hψ'_inf : ∀ y : InfiniteAdeleRing F,
      ψ' (y, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F y)) : ℂ) := by
    intro y
    rw [hψ'_apply, ← ha y]
    congr 1
    exact Prod.ext rfl (mul_zero _)

  have hI := NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
    F μ hψ' hψ'_inf hf x

  have hFI : ∀ (H : AdeleRing (𝓞 F) F → ℂ) (w : AdeleRing (𝓞 F) F),
      fourierIntegral ψ' μ H w = fourierIntegral ψ μ H (algebraMap F (AdeleRing (𝓞 F) F) a * w) := by
    intro H w
    simp only [fourierIntegral_def, hψ'_apply]
    congr 1 with v
    congr 2
    ring
  have hFI' : fourierIntegral ψ' μ f = fun v => fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) a * v) :=
    funext (hFI f)

  let u : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 a ha0)
  have hu : (u : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) a := rfl
  have hPF : MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) u = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap F (Units.mk0 a ha0)
  have hdil := NumberField.AdelicFourier.fourierIntegral_comp_mul_left F μ ψ (fourierIntegral ψ μ f) u
    ((u : AdeleRing (𝓞 F) F) * x)
  rw [hFI, hFI', ← hu, hdil, hPF, ← mul_assoc, Units.inv_mul, one_mul] at hI
  simpa using hI

end S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet (solution)

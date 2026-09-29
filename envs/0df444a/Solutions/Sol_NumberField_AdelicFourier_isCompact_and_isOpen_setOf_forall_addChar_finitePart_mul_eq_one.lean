-- Prove2me | solution 1 for NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/69561aa0-1f02-5745-9380-163a2772f8c5

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory"

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual"
namespace Ws25
namespace AnnCpt
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y + z ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hy v) (hz v)

theorem mul_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y * z ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hy v) (hz v)

theorem algebraMap_coe_mem_integralFiniteAdeles (q : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F q) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => algebraMap_mem_adicCompletionIntegers (𝓞 F) F v q

theorem continuous_apply_zero {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    Continuous fun x : FiniteAdeleRing (𝓞 F) F => ψ (0, x) :=
  hψ.continuous.comp (continuous_const.prodMk continuous_id)

theorem isCompact_and_isOpen
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F |
          ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by

  have hann :=
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
      F hψ hψ_inf
  set A : Set (FiniteAdeleRing (𝓞 F) F) :=
    {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} with hA
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  have hmemA : ∀ w, w ∈ A ↔ ∃ r : F, r ∈ D ∧ w - ι r ∈ integralFiniteAdeles (𝓞 F) F :=
    fun w => hann w

  have hclosed : IsClosed A := by
    have hcont : ∀ z : FiniteAdeleRing (𝓞 F) F, Continuous fun w => ψ (0, w * z) := fun z =>
      (continuous_apply_zero hψ).comp (continuous_id.mul continuous_const)
    have : A = ⋂ z ∈ integralFiniteAdeles (𝓞 F) F, {w | ψ (0, w * z) = 1} := by
      ext w; simp only [hA, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_eq (hcont z) continuous_const

  obtain ⟨a, ha0, ha⟩ := D.isFractional
  have ha0' : (algebraMap (𝓞 F) F a) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha0

  have hsub : A ⊆ (fun z => ι (algebraMap (𝓞 F) F a)⁻¹ * z) '' integralFiniteAdeles (𝓞 F) F := by
    intro w hw
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw

    obtain ⟨c, hc⟩ : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = a • r := ha r hr
    refine ⟨ι (algebraMap (𝓞 F) F a) * w, ?_, ?_⟩
    · have hsplit : ι (algebraMap (𝓞 F) F a) * w
          = ι (algebraMap (𝓞 F) F c) + ι (algebraMap (𝓞 F) F a) * (w - ι r) := by
        rw [hc, Algebra.smul_def, map_mul, mul_sub]; abel
      rw [hsplit]
      exact add_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles c)
        (mul_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles a) hwr)
    · show ι (algebraMap (𝓞 F) F a)⁻¹ * (ι (algebraMap (𝓞 F) F a) * w) = w
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0', map_one, one_mul]
  have hcompact : IsCompact A :=
    ((isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)).of_isClosed_subset
      hclosed hsub

  have hopen : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun w hw => ?_
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw
    refine ⟨(fun z => ι r + z) '' integralFiniteAdeles (𝓞 F) F, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hmemA _).mpr ⟨r, hr, by rwa [add_sub_cancel_left]⟩
    · exact isOpenMap_add_left (ι r) _ (isOpen_integralFiniteAdeles F)
    · exact ⟨w - ι r, hwr, add_sub_cancel (ι r) w⟩
  exact ⟨hcompact, hopen⟩

end NumberField.AdelicFourier.Ws25.AnnCpt

open NumberField.AdelicFourier.Ws25.AnnCpt in
theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} :=
  isCompact_and_isOpen hψ hψ_inf

end

end S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
end P2MW
export P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one (solution)

-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6fa114f3-5db0-5a56-ab61-4a8530cb67fc

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace
import Theorems.Thm_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.NumberField.AdelicFourier AutomorphicForm"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def schwartzBruhat mem_schwartzBruhat_of_mem_pureTensorSet zero_mem_schwartzBruhat schwartzBruhat_induction exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace comp_mul_algebraMap_mem_pureTensorSet"
namespace Ws25FStab
p2m_open "NumberField.AdelicFourier NumberField"

variable (F : Type) [Field F] [NumberField F]

theorem comp_mul_algebraMap_mem_schwartzBruhat {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ schwartzBruhat F := by
  refine schwartzBruhat_induction (F := F)
    (p := fun f _ => (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ schwartzBruhat F)
    ?_ ?_ ?_ ?_ hf
  · intro f hf
    exact mem_schwartzBruhat_of_mem_pureTensorSet (comp_mul_algebraMap_mem_pureTensorSet F ha hf)
  · exact zero_mem_schwartzBruhat
  · intro f g _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · intro c f _ hf
    exact Submodule.smul_mem _ c hf

theorem fourierIntegral_mem_schwartzBruhat_impl
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by

  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
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

  have hS : fourierIntegral ψ' μ f ∈ schwartzBruhat F :=
    fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace F μ hψ' hψ'_inf hf

  have hFI : fourierIntegral ψ μ f
      = fun w => fourierIntegral ψ' μ f (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * w) := by
    funext w
    simp only [fourierIntegral_def, hψ'_apply]
    congr 1 with v
    congr 2
    rw [mul_neg, ← mul_assoc (algebraMap F (AdeleRing (𝓞 F) F) a) v,
      mul_comm (algebraMap F (AdeleRing (𝓞 F) F) a) v, mul_assoc v,
      ← mul_assoc (algebraMap F (AdeleRing (𝓞 F) F) a), ← map_mul, mul_inv_cancel₀ ha0,
      map_one, one_mul]

  rw [hFI]
  exact comp_mul_algebraMap_mem_schwartzBruhat F (inv_ne_zero ha0) hS

end NumberField.AdelicFourier.Ws25FStab

end

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat.NumberField.AdelicFourier AutomorphicForm"

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F :=
  NumberField.AdelicFourier.Ws25FStab.fourierIntegral_mem_schwartzBruhat_impl F μ hψ hf

end S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat (solution)

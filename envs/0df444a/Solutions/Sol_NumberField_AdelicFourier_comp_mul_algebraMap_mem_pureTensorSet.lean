-- Prove2me | solution 1 for NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6cc94273-eb3a-56cd-8668-ef7e3ea7154d

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField.AdelicFourier IsDedekindDomain"
open scoped Classical SchwartzMap

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet"
namespace Ws25DIL
p2m_open "NumberField.AdelicFourier NumberField"

def mulLeftLinearEquiv {A : Type*} [CommRing A] [Algebra ℝ A] (c c' : A) (h : c' * c = 1) :
    A ≃ₗ[ℝ] A where
  toFun x := c * x
  invFun x := c' * x
  map_add' x y := mul_add c x y
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]

def mulLeftHomeomorph {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃ₜ A where
  toFun x := c * x
  invFun x := c' * x
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

variable (F : Type) [Field F] [NumberField F]

theorem dil_impl {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf

  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a with hc
  set c' : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc'
  have hcc : c' * c = 1 := by rw [hc, hc', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let M : mixedEmbedding.mixedSpace F ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (mulLeftLinearEquiv c c' hcc).toContinuousLinearEquiv
  have hM : ∀ v, M v = c * v := fun v => rfl
  let g' : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g
  have hg' : ∀ v, g' v = g (c * v) := fun v => by
    show (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g) v = _
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    rfl

  set d : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a with hd
  set d' : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ with hd'
  have hdd : d' * d = 1 := by rw [hd, hd', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let Φ : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F := mulLeftHomeomorph d d' hdd
  have hΦ : (fun z => h (d * z)) = h ∘ Φ := rfl
  refine ⟨g', fun z => h (d * z), hlc.comp_continuous (continuous_const.mul continuous_id),
    by rw [hΦ]; exact hcs.comp_homeomorph Φ, ?_⟩
  funext x
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).1 = algebraMap F (InfiniteAdeleRing F) a * x.1 := rfl
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).2 = d * x.2 := rfl
  show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) a * x).1)
      * h (algebraMap F (AdeleRing (𝓞 F) F) a * x).2
    = g' (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h (d * x.2)
  rw [h1, h2, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hg']

end NumberField.AdelicFourier.Ws25DIL

end

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.NumberField.AdelicFourier IsDedekindDomain"
open scoped Classical

theorem solution
    (F : Type) [Field F] [NumberField F] {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F :=
  NumberField.AdelicFourier.Ws25DIL.dil_impl F ha hf

end S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet
end P2MW
export P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet (solution)

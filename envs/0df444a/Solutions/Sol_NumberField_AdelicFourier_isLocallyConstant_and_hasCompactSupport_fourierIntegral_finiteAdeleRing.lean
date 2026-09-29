-- Prove2me | solution 1 for NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/593ae1fa-108d-5db7-8553-99b30e9be1fc

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
import Theorems.Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory"

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "fourierIntegral fourierIntegral_def fourierIntegral_comp_add_right forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one"
namespace Ws25
namespace Sfin
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y + z ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hy v) (hz v)

theorem sub_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y - z ∈ integralFiniteAdeles (𝓞 F) F := fun v => sub_mem (hy v) (hz v)

theorem neg_mem_integralFiniteAdeles {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) : -z ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => neg_mem (hz v)

theorem mul_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y * z ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hy v) (hz v)

theorem zero_mem_integralFiniteAdeles :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun _ => zero_mem _

theorem add_mem_image_iff (d : 𝓞 F) (k : F) {u : FiniteAdeleRing (𝓞 F) F}
    (hu : u ∈ integralFiniteAdeles (𝓞 F) F) (v : FiniteAdeleRing (𝓞 F) F) :
    v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * u ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ v ∈ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F := by
  constructor
  · rintro ⟨z, hz, hzv⟩
    refine ⟨z - u, sub_mem_integralFiniteAdeles hz hu, ?_⟩
    simp only at hzv ⊢
    rw [mul_sub]
    linear_combination hzv
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + u, add_mem_integralFiniteAdeles hz hu, by simp only; rw [mul_add, add_assoc]⟩

theorem exists_mem_image_of_sum_ne_zero (d : 𝓞 F) (s : Finset F) (c : F → ℂ)
    (v : FiniteAdeleRing (𝓞 F) F)
    (hv : (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) v ≠ 0) :
    ∃ k ∈ s, v ∈ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F := by
  by_contra hcon
  apply hv
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : v ∉ (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
      + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F :=
    fun hmem => hcon ⟨k, hk, hmem⟩
  rw [Pi.smul_apply, Set.indicator_apply, if_neg hk', smul_zero]

theorem sum_apply_add_eq (d : 𝓞 F) (s : Finset F) (c : F → ℂ)
    {u : FiniteAdeleRing (𝓞 F) F} (hu : u ∈ integralFiniteAdeles (𝓞 F) F)
    (v : FiniteAdeleRing (𝓞 F) F) :
    (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
        (v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * u)
      = (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) v := by
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, Set.indicator_apply, Pi.one_apply, add_mem_image_iff d k hu v]

section Main

variable [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
  (hψ_inf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
  {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)

include hψ hψ_inf hlc hcs

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] [ν.IsAddHaarMeasure] in

theorem isLocallyConstant_fourierIntegral :
    IsLocallyConstant (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) := by
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf_def
  have hψf : ∀ x, ψf x = ψ (0, x) := fun _ => rfl

  have hO : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf z = 1 := by
    have h1 : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, 1 * z) = 1 :=
      (NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
        F hψ hψ_inf 1).mpr
        ⟨1, FractionalIdeal.one_le_dual_one (A := ℤ) (K := ℚ) (FractionalIdeal.one_mem_one _),
          by rw [map_one, sub_self]; exact zero_mem_integralFiniteAdeles⟩
    intro z hz
    rw [hψf, ← one_mul z]
    exact h1 z hz

  obtain ⟨d, hd, s, c, rfl⟩ :=
    NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs

  have key : ∀ t : FiniteAdeleRing (𝓞 F) F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t ∈ integralFiniteAdeles (𝓞 F) F →
      (∀ k ∈ s, algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t ∈ integralFiniteAdeles (𝓞 F) F) →
      ∀ (g : FiniteAdeleRing (𝓞 F) F → ℂ), (∀ v, g v ≠ 0 → ∃ k ∈ s, v ∈
          (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F) →
      ∀ w, fourierIntegral ψf ν g (w + t) = fourierIntegral ψf ν g w := by
    intro t ht1 ht2 g hg w
    rw [fourierIntegral_def, fourierIntegral_def]
    congr 1 with v
    by_cases hv : g v = 0
    · simp only [hv, mul_zero]
    · obtain ⟨k, hk, z, hz, rfl⟩ := hg v hv
      have hvt : (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) * t
          ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [add_mul, mul_right_comm]
        exact add_mem_integralFiniteAdeles (ht2 k hk) (mul_mem_integralFiniteAdeles ht1 hz)
      simp only
      rw [mul_add, neg_add, AddChar.map_add_eq_mul, hO _ (neg_mem_integralFiniteAdeles hvt),
        mul_one]

  have hP : IsOpen ((fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t) ⁻¹'
      integralFiniteAdeles (𝓞 F) F) :=
    (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hQ : IsOpen (⋂ k ∈ s, (fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t) ⁻¹'
      integralFiniteAdeles (𝓞 F) F) :=
    isOpen_biInter_finset fun k _ =>
      (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hT := hP.inter hQ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun w => ?_
  have hmem : (fun y => y - w) ⁻¹'
      (((fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * t) ⁻¹'
          integralFiniteAdeles (𝓞 F) F) ∩
        ⋂ k ∈ s, (fun t => algebraMap F (FiniteAdeleRing (𝓞 F) F) k * t) ⁻¹'
          integralFiniteAdeles (𝓞 F) F) ∈ nhds w := by
    refine (hT.preimage (continuous_sub_right w)).mem_nhds ?_
    rw [Set.mem_preimage, sub_self]
    refine ⟨?_, Set.mem_iInter₂.mpr fun k _ => ?_⟩
    · rw [Set.mem_preimage, mul_zero]; exact zero_mem_integralFiniteAdeles
    · rw [Set.mem_preimage, mul_zero]; exact zero_mem_integralFiniteAdeles
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (y - w)
      ∈ integralFiniteAdeles (𝓞 F) F := hy.1
  have hy2 : ∀ k ∈ s, algebraMap F (FiniteAdeleRing (𝓞 F) F) k * (y - w)
      ∈ integralFiniteAdeles (𝓞 F) F := fun k hk => Set.mem_iInter₂.mp hy.2 k hk
  have := key (y - w) hy1 hy2 _ (exists_mem_image_of_sum_ne_zero d s c) w
  rwa [add_sub_cancel] at this

theorem hasCompactSupport_fourierIntegral :
    HasCompactSupport (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) := by
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf_def
  have hψf : ∀ x, ψf x = ψ (0, x) := fun _ => rfl

  have hA :=
    (NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
      F hψ hψ_inf).1

  obtain ⟨d, hd, s, c, rfl⟩ :=
    NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  have hdF : (d : F) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)

  have hK : IsCompact ((fun a => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * a) ''
      {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}) :=
    hA.image (continuous_const.mul continuous_id)
  refine HasCompactSupport.intro' hK hK.isClosed fun w hw => ?_
  by_contra hne
  apply hw
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w, fun z hz => ?_, ?_⟩
  ·
    have hcomp : fourierIntegral ψf ν (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) w
        = ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z * w) *
          fourierIntegral ψf ν (∑ k ∈ s, c k •
            ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
                integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) w := by
      have hc := congrFun (fourierIntegral_comp_add_right ψf ν (∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z)) w
      have hper : ((∑ k ∈ s, c k •
          ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
            + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
              integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) ∘
            fun v => v + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z)
          = ∑ k ∈ s, c k •
            ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
                integralFiniteAdeles (𝓞 F) F).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) :=
        funext fun v => sum_apply_add_eq d s c hz v
      rwa [hper] at hc
    have h1 : ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z * w) = 1 :=
      (mul_eq_right₀ hne).mp hcomp.symm
    rw [mul_right_comm] at h1
    exact h1
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) = w
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdF, map_one, one_mul]

end Main

end NumberField.AdelicFourier.Ws25.Sfin

open NumberField.AdelicFourier.Ws25.Sfin in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    IsLocallyConstant (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h)
      ∧ HasCompactSupport (fourierIntegral
        (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν h) :=
  ⟨isLocallyConstant_fourierIntegral ν hψ hψ_inf hlc hcs,
    hasCompactSupport_fourierIntegral ν hψ hψ_inf hlc hcs⟩

end

end S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
end P2MW
export P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing (solution)

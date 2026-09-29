-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4da96d8e-78d7-5b76-830b-49ff7413052f

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

noncomputable section

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * ξ)))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1
            then 1 else 0) := by
  set S := integralFiniteAdeles (𝓞 F) F
  set S' : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' S with hS'_def
  set T := (fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k +
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' S with hT_def
  have hScomp : IsCompact S := isCompact_integralFiniteAdeles F
  have hS'comp : IsCompact S' := hScomp.image (continuous_const.mul continuous_id)
  have hS'meas : MeasurableSet S' := hS'comp.isClosed.measurableSet

  have hT_trans : T = (fun u => u + algebraMap F (FiniteAdeleRing (𝓞 F) F) k) '' S' := by
    rw [hT_def, hS'_def, ← Set.image_comp]; congr 1; funext z; dsimp; ring
  have hνT_eq : ν T = ν S' := by
    rw [hT_trans, Set.image_add_right, measure_preimage_add_right]

  have hSadd : ∀ ⦃y z⦄, y ∈ S → z ∈ S → y + z ∈ S := fun y z hy hz v => add_mem (hy v) (hz v)
  have hSneg : ∀ ⦃z⦄, z ∈ S → -z ∈ S := fun z hz v => neg_mem (hz v)
  have hS'add : ∀ ⦃u v⦄, u ∈ S' → v ∈ S' → u + v ∈ S' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩; exact ⟨y + z, hSadd hy hz, by ring⟩
  have hS'neg : ∀ ⦃u⦄, u ∈ S' → -u ∈ S' := by
    rintro _ ⟨z, hz, rfl⟩; exact ⟨-z, hSneg hz, by ring⟩

  have hmem : ∀ v, v ∈ T ↔ v + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k) ∈ S' := by
    intro v; rw [hT_trans]
    constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro hu; exact ⟨v + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k), hu, by ring⟩
  have hind : (T.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      = ((S'.indicator 1 : FiniteAdeleRing (𝓞 F) F → ℂ) ∘
          (· + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k))) := by
    funext v
    by_cases hv : v ∈ T
    · simp only [Set.indicator_of_mem hv, Function.comp_apply,
        Set.indicator_of_mem ((hmem v).mp hv), Pi.one_apply]
    · simp only [Set.indicator_of_notMem hv, Function.comp_apply,
        Set.indicator_of_notMem (fun h => hv ((hmem v).mpr h))]
  rw [hind,
    fourierIntegral_comp_add_right ψf ν (S'.indicator 1)
      (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k)]
  simp only [neg_mul, ← map_mul]
  rw [mul_assoc]
  congr 1

  rw [fourierIntegral_def]
  have hrw : (fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * S'.indicator 1 v)
      = S'.indicator (fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))) := by
    funext v; by_cases hv : v ∈ S'
    · simp [Set.indicator_of_mem hv]
    · simp [Set.indicator_of_notMem hv]
  rw [hrw, integral_indicator hS'meas]
  have hcont : Continuous fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) :=
    hψf.comp (continuous_id.mul continuous_const).neg

  have hortho : ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν
      = if (∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1)
        then ((ν S').toReal : ℂ) else 0 := by
    by_cases hc : ∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1
    · rw [if_pos hc, setIntegral_congr_fun hS'meas (fun v hv => hc v hv), setIntegral_const]
      simp [Measure.real, Complex.real_smul]
    · rw [if_neg hc]
      push_neg at hc
      obtain ⟨u₀, hu₀, hψu₀⟩ := hc
      set I := ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν with hI_def
      have hS'inv : (fun v => v + u₀) ⁻¹' S' = S' := by
        ext v; constructor
        · intro hv; have := hS'add hv (hS'neg hu₀); simpa using this
        · intro hv; exact hS'add hv hu₀
      have hν_right : ν.map (· + u₀) = ν := by
        have hcomm : (· + u₀) = (u₀ + · : FiniteAdeleRing (𝓞 F) F → _) :=
          funext fun v => add_comm v u₀
        rw [hcomm]; exact map_add_left_eq_self ν u₀
      have hI : I = ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * I := by
        calc I = ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))
              ∂(ν.map (· + u₀)) := by rw [hν_right]
          _ = ∫ v in (· + u₀) ⁻¹' S',
              ψf (-((v + u₀) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              rw [setIntegral_map hS'meas hcont.aestronglyMeasurable
                (measurable_add_const u₀).aemeasurable]
          _ = ∫ v in S', ψf (-((v + u₀) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              rw [hS'inv]
          _ = ∫ v in S', ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))
                * ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              congr 1 with v
              rw [add_mul, neg_add, AddChar.map_add_eq_mul, mul_comm]
          _ = ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * I := by
              rw [integral_const_mul, hI_def]
      have key : (1 - ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))) * I = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]; exact hI
      rcases mul_eq_zero.mp key with h | h
      · exact absurd (sub_eq_zero.mp h).symm hψu₀
      · exact h
  rw [hortho]

  have hcond_iff : (∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1)
      ↔ (∀ z ∈ S, ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1) := by
    have heq : ∀ z, -(algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z
        * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * (-z) := by
      intro z; rw [map_mul]; ring
    constructor
    · intro h z hz
      have := h _ ⟨z, hz, rfl⟩
      rw [heq, mul_neg, AddChar.map_neg_eq_inv, inv_eq_one] at this
      exact this
    · rintro h _ ⟨z, hz, rfl⟩
      rw [heq, mul_neg, AddChar.map_neg_eq_inv, inv_eq_one]
      exact h z hz
  rw [hνT_eq]
  by_cases hc : ∀ z ∈ S, ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1
  · rw [if_pos (hcond_iff.mpr hc), if_pos hc, mul_one]
  · rw [if_neg (fun h => hc (hcond_iff.mp h)), if_neg hc, mul_zero]

end
end S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing (solution)

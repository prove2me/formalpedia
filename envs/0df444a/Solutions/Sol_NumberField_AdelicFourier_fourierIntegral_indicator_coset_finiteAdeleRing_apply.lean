-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_indicator_coset_finiteAdeleRing_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/382d0514-72bd-573f-aa5c-8f526c532703

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Ws23
namespace Alpha
open MeasureTheory NumberField.AdelicFourier

open scoped Classical in

theorem fourierIntegral_indicator_coset_of_isCompact
    {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddLeftInvariant]
    (ψ : AddChar K ℂ) (Λ : Set K) (hΛc : IsCompact Λ)
    (hΛadd : ∀ a ∈ Λ, ∀ b ∈ Λ, a + b ∈ Λ) (hΛsub : ∀ a ∈ Λ, ∀ b ∈ Λ, a - b ∈ Λ) (y u w : K) :
    fourierIntegral ψ μ (((fun z ↦ y + u * z) '' Λ).indicator 1) w
      = ψ (-(y * w)) * ((μ ((fun z ↦ y + u * z) '' Λ)).toReal : ℂ)
        * (if ∀ z ∈ Λ, ψ (u * w * z) = 1 then 1 else 0) := by
  classical
  set B : Set K := (fun z ↦ u * z) '' Λ with hB
  set A : Set K := (fun z ↦ y + u * z) '' Λ with hA

  have hBadd : ∀ a ∈ B, ∀ b ∈ B, a + b ∈ B := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, hΛadd a ha b hb, by simp [mul_add]⟩
  have hBsub : ∀ a ∈ B, ∀ b ∈ B, a - b ∈ B := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a - b, hΛsub a ha b hb, by simp [mul_sub]⟩
  have hBc : IsCompact B := hΛc.image (continuous_const.mul continuous_id)
  have hBm : MeasurableSet B := hBc.measurableSet
  have hAB : A = (fun x ↦ y + x) '' B := by
    rw [hA, hB, Set.image_image]
  have hνAB : μ A = μ B := by
    rw [hAB, Set.image_add_left, measure_preimage_add μ]

  have hstep1 : fourierIntegral ψ μ (A.indicator 1) w = ψ (-(y * w)) * ∫ x in B, ψ (-(x * w)) ∂μ := by
    rw [fourierIntegral_def]
    have h1 : (fun v ↦ ψ (-(v * w)) * A.indicator 1 v) = A.indicator (fun v ↦ ψ (-(v * w))) := by
      funext v
      by_cases hv : v ∈ A
      · simp [Set.indicator_of_mem hv]
      · simp [Set.indicator_of_notMem hv]
    rw [h1, ← integral_add_left_eq_self _ y]
    have h2 : (fun x ↦ A.indicator (fun v ↦ ψ (-(v * w))) (y + x)) =
        fun x ↦ ψ (-(y * w)) * B.indicator (fun v ↦ ψ (-(v * w))) x := by
      funext x
      by_cases hx : x ∈ B
      · have hyx : y + x ∈ A := by rw [hAB]; exact ⟨x, hx, rfl⟩
        rw [Set.indicator_of_mem hyx, Set.indicator_of_mem hx, ← AddChar.map_add_eq_mul]
        congr 1; ring
      · have hyx : y + x ∉ A := by
          rw [hAB]
          rintro ⟨x', hx', hxx'⟩
          have : x' = x := add_left_cancel hxx'
          exact hx (this ▸ hx')
        rw [Set.indicator_of_notMem hyx, Set.indicator_of_notMem hx, mul_zero]
    rw [h2, integral_const_mul, integral_indicator hBm]
  rw [hstep1, hνAB, mul_assoc]
  congr 1

  by_cases htriv : ∀ z ∈ Λ, ψ (u * w * z) = 1
  · rw [if_pos htriv, mul_one]
    have hone : ∀ x ∈ B, ψ (-(x * w)) = 1 := by
      rintro _ ⟨z, hz, rfl⟩
      have hz1 : ψ (u * z * w) = 1 := by rw [mul_right_comm]; exact htriv z hz
      have := AddChar.map_add_eq_mul ψ (-(u * z * w)) (u * z * w)
      rw [neg_add_cancel, AddChar.map_zero_eq_one, hz1, mul_one] at this
      exact this.symm
    rw [setIntegral_congr_fun hBm hone, setIntegral_const]
    simp [Measure.real]
  · rw [if_neg htriv, mul_zero]
    push Not at htriv
    obtain ⟨z₀, hz₀, hne⟩ := htriv
    set t₀ : K := u * z₀ with ht₀
    have ht₀B : t₀ ∈ B := ⟨z₀, hz₀, rfl⟩
    have hne' : ψ (-(t₀ * w)) ≠ 1 := by
      intro h1
      apply hne
      have := AddChar.map_add_eq_mul ψ (-(t₀ * w)) (t₀ * w)
      rw [neg_add_cancel, AddChar.map_zero_eq_one, h1, one_mul] at this
      rw [ht₀, mul_right_comm] at this
      exact this.symm
    have hI : (∫ x in B, ψ (-(x * w)) ∂μ) = ψ (-(t₀ * w)) * ∫ x in B, ψ (-(x * w)) ∂μ := by
      conv_lhs => rw [← integral_indicator hBm, ← integral_add_left_eq_self _ t₀]
      have h3 : (fun x ↦ B.indicator (fun v ↦ ψ (-(v * w))) (t₀ + x)) =
          fun x ↦ ψ (-(t₀ * w)) * B.indicator (fun v ↦ ψ (-(v * w))) x := by
        funext x
        by_cases hx : x ∈ B
        · rw [Set.indicator_of_mem (hBadd _ ht₀B _ hx), Set.indicator_of_mem hx, ← AddChar.map_add_eq_mul]
          congr 1; ring
        · have hx' : t₀ + x ∉ B := fun h ↦ hx (by simpa using hBsub _ h _ ht₀B)
          rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
      rw [h3, integral_const_mul, integral_indicator hBm]
    have h4 : (1 - ψ (-(t₀ * w))) * ∫ x in B, ψ (-(x * w)) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (sub_eq_zero.mp h5).symm hne'
    · exact h5

end Ws23.Alpha

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (y u w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν (((fun z ↦ y + u * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ψf (-(y * w)) * ((ν ((fun z ↦ y + u * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (u * w * z) = 1 then 1 else 0) :=
  Ws23.Alpha.fourierIntegral_indicator_coset_of_isCompact ν ψf (integralFiniteAdeles (𝓞 F) F)
    (isCompact_integralFiniteAdeles F) (fun _ ha _ hb v ↦ add_mem (ha v) (hb v))
    (fun _ ha _ hb v ↦ sub_mem (ha v) (hb v)) y u w

end S_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply (solution)

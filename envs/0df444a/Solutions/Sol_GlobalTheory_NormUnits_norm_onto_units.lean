-- Prove2me | solution 1 for GlobalTheory.NormUnits.norm_onto_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:05.748936+00:00
-- url     : https://prove2.me/submissions/0dba620f-1ef5-4482-a1b2-fcee2e92484c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Theorems.Thm_P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab
import Theorems.Thm_GlobalTheory_NormUnits_norm_eq_of_norm_sub_lt
import Theorems.Thm_GlobalTheory_NormUnits_exists_far_unit
import Theorems.Thm_GlobalTheory_NormUnits_fixed_mem_range
import Theorems.Thm_GlobalTheory_NormUnits_exists_trace_one
import Theorems.Thm_GlobalTheory_NormUnits_exists_point_mod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by
  intro F E _ _ _ _ hU u hu
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : CharZero F := hU.charZero
  have hN : ∀ v : E, ‖v * star v‖ = ‖v‖ ^ 2 := fun v => by rw [norm_mul, hU.norm_star, sq]
  have hsc : Continuous (fun y : E => star y) := by
    have : LipschitzWith 1 (fun y : E => star y) := LipschitzWith.of_dist_le_mul fun x y => by
      simp [dist_eq_norm, ← star_sub, hU.norm_star]
    exact this.continuous

  obtain ⟨ζ, hζ1, hζ⟩ := exists_far_unit F E
  have hfix := fixed_mem_range F E ζ hζ
  obtain ⟨s, hs⟩ := hfix (ζ + star ζ) (by rw [star_add, star_star, add_comm])
  obtain ⟨t, ht⟩ := hfix (ζ * star ζ) (by rw [star_mul, star_star, mul_comm])
  obtain ⟨e, he1, he⟩ := exists_trace_one F E ζ hζ1 hζ s t hs ht
  have hsn : ‖s‖ ≤ 1 := by
    rw [← norm_algebraMap' E s, hs]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hζ1.le (by rw [hU.norm_star, hζ1]))
  have htn : ‖t‖ = 1 := by
    rw [← norm_algebraMap' E t, ht, hN, hζ1, one_pow]
  obtain ⟨a, b, z, -, hb, hz, hone, hQ⟩ := exists_point_mod F _ _ u hsn htn.le hu.le
  have hw : (algebraMap F E a + algebraMap F E b * ζ) * star (algebraMap F E a + algebraMap F E b * ζ) =
      algebraMap F E (a ^ 2 + s * a * b + t * b ^ 2) := by
    have hsw : star (algebraMap F E a + algebraMap F E b * ζ) = algebraMap F E a + algebraMap F E b * star ζ := by
      rw [star_add, star_mul, hU.star_fix, hU.star_fix, mul_comm]
    rw [hsw]
    simp only [map_add, map_mul, map_pow, hs, ht]
    ring
  have hwb : ‖b‖ ≤ ‖algebraMap F E a + algebraMap F E b * ζ‖ := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · have hbE : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb0
      have e1 : algebraMap F E a + algebraMap F E b * ζ = algebraMap F E b * (ζ - algebraMap F E (-(a / b))) := by
        rw [map_neg, map_div₀, sub_neg_eq_add]; field_simp; ring
      rw [e1, norm_mul, norm_algebraMap']
      exact le_mul_of_one_le_right (norm_nonneg _) (hζ _)
  have hz1 : ‖z‖ = 1 := by
    refine le_antisymm hz (not_lt.1 fun hzl => ?_)
    have hcz : ‖u * z ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow, hu, one_mul]; exact pow_lt_one₀ (norm_nonneg _) hzl two_ne_zero
    have hQ1 : ‖a ^ 2 + s * a * b + t * b ^ 2‖ < 1 := by
      have := IsUltrametricDist.norm_add_le_max (a ^ 2 + s * a * b + t * b ^ 2 - u * z ^ 2) (u * z ^ 2)
      rw [sub_add_cancel] at this
      exact this.trans_lt (max_lt hQ hcz)
    have hw1 : ‖algebraMap F E a + algebraMap F E b * ζ‖ < 1 := by
      have : ‖algebraMap F E a + algebraMap F E b * ζ‖ ^ 2 < 1 := by
        rw [← hN, hw, norm_algebraMap']; exact hQ1
      nlinarith [norm_nonneg (algebraMap F E a + algebraMap F E b * ζ)]
    have hb1 : ‖b‖ < 1 := hwb.trans_lt hw1
    have ha1 : ‖a‖ < 1 := by
      rw [← norm_algebraMap' E a]
      have : algebraMap F E a = (algebraMap F E a + algebraMap F E b * ζ) - algebraMap F E b * ζ := by ring
      rw [this]
      refine (norm_sub_le_max' _ _).trans_lt (max_lt hw1 ?_)
      rw [norm_mul, norm_algebraMap', hζ1, mul_one]; exact hb1
    rcases hone with h | h | h <;> linarith
  have hzE : algebraMap F E z ≠ 0 := (map_ne_zero _).2 (by rintro rfl; simp at hz1)
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : E, ‖v₁ * star v₁ - algebraMap F E u‖ < 1 := by
    refine ⟨(algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z, ?_⟩
    have e1 : (algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z *
        star ((algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z) - algebraMap F E u =
        algebraMap F E ((a ^ 2 + s * a * b + t * b ^ 2 - u * z ^ 2) / z ^ 2) := by
      rw [star_div₀, hU.star_fix, div_mul_div_comm, hw]
      simp only [map_div₀, map_sub, map_mul, map_pow, map_add]
      field_simp
    rw [e1, norm_algebraMap', norm_div, norm_pow, hz1, one_pow, div_one]
    exact hQ

  let f : E → ℝ := fun v => ‖v * star v - algebraMap F E u‖
  have hf : Continuous f := continuous_norm.comp ((continuous_id.mul hsc).sub continuous_const)
  have hsph : ∀ v : E, f v < 1 → v ∈ Metric.sphere (0 : E) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have h1 : ‖v * star v‖ = 1 := by
      rw [norm_eq_of_norm_sub_lt (hv.trans_le (by rw [norm_algebraMap', hu])), norm_algebraMap', hu]
    rw [hN] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  obtain ⟨v₀, hv₀S, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn ⟨v₁, hsph v₁ hv₁⟩ hf.continuousOn
  have hv₀1 : ‖v₀‖ = 1 := mem_sphere_zero_iff_norm.1 hv₀S
  have hρ1 : f v₀ < 1 := (hmin (hsph v₁ hv₁)).trans_lt hv₁
  by_cases hρ0 : f v₀ = 0
  · exact ⟨v₀, sub_eq_zero.1 (norm_eq_zero.1 hρ0)⟩
  exfalso
  have hρpos : 0 < f v₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hρ0)
  have hN₀ : ‖v₀ * star v₀‖ = 1 := by rw [hN, hv₀1, one_pow]
  have hN₀0 : v₀ * star v₀ ≠ 0 := by intro h; rw [h, norm_zero] at hN₀; exact zero_ne_one hN₀
  obtain ⟨x, hxN, hxn, hsx⟩ : ∃ x : E, v₀ * star v₀ * (1 + x) = algebraMap F E u ∧ ‖x‖ = f v₀ ∧ star x = x := by
    refine ⟨algebraMap F E u / (v₀ * star v₀) - 1, ?_, ?_, ?_⟩
    · rw [show (1 : E) + (algebraMap F E u / (v₀ * star v₀) - 1) = algebraMap F E u / (v₀ * star v₀) by ring,
        mul_div_cancel₀ _ hN₀0]
    · have : algebraMap F E u / (v₀ * star v₀) - 1 = (algebraMap F E u - v₀ * star v₀) / (v₀ * star v₀) := by
        rw [sub_div, div_self hN₀0]
      rw [this, norm_div, hN₀, div_one, norm_sub_rev]
    · rw [star_sub, star_one, star_div₀, hU.star_fix, star_mul, star_star]
  have hyn : ‖x * e‖ ≤ f v₀ := by rw [norm_mul, hxn]; exact mul_le_of_le_one_right hρpos.le he1
  have hv'S : v₀ * (1 + x * e) ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hv₀1, one_mul,
      norm_eq_of_norm_sub_lt (by rw [add_sub_cancel_left, norm_one]; exact hyn.trans_lt hρ1), norm_one]
  have hfv' : f (v₀ * (1 + x * e)) = ‖x * e‖ ^ 2 := by
    have e1 : v₀ * (1 + x * e) * star (v₀ * (1 + x * e)) - algebraMap F E u =
        v₀ * star v₀ * (x * e * (x * star e)) := by
      rw [star_mul, star_add, star_one, star_mul, hsx]
      linear_combination (v₀ * star v₀ * x) * he + hxN
    show ‖v₀ * (1 + x * e) * star (v₀ * (1 + x * e)) - algebraMap F E u‖ = _
    rw [e1, norm_mul, hN₀, one_mul, norm_mul (x * e), norm_mul x (star e), hU.norm_star, norm_mul, sq]
  have hle : f v₀ ≤ f (v₀ * (1 + x * e)) := hmin hv'S
  rw [hfv'] at hle
  have : ‖x * e‖ ^ 2 ≤ f v₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyn 2
  nlinarith
end GlobalTheory.NormUnits

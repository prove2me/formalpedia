-- Prove2me | solution 1 for GeneralCK.Certificates.E8InverseJet5Bridge.e8QCanonicalJet5_soundAt_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:19:03.164656+00:00
-- url     : https://prove2.me/submissions/17866681-ccab-43f9-96f0-b10c2803c184

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_PilotData_log_two
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

section
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h







theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK
end

section
namespace GeneralCK.Comparison
open Set









@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]



theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)







end GeneralCK.Comparison
end

section
namespace GeneralCK
open Set Filter
open scoped Topology









theorem J_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < J v := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  apply (lt_div_iff₀ hv).2
  linarith



theorem hasDerivAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt J (-1 / (Real.log 2 * v * (1 - v))) v := by
  have hv1 : 1 - v ≠ 0 := by linarith
  have hlog : J =ᶠ[𝓝 v] (fun p => (Real.log (1 - p) - Real.log p) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hv hv'] with p hp
    simp only [J, Real.log_div (by linarith [hp.2] : 1 - p ≠ 0) (ne_of_gt hp.1)]
  have hd := (((hasDerivAt_id v).const_sub 1).log (by simpa using hv1)).sub
    ((hasDerivAt_id v).log (ne_of_gt hv))
  have hd' := (hd.div_const (Real.log 2)).congr_of_eventuallyEq hlog
  convert! hd' using 1
  simp only [id_eq]
  field_simp [hv1]
  ring









end GeneralCK
end

section
namespace GeneralCK

/-- The contact equation has exactly one solution in the open lower half. -/
theorem existsUnique_radialContact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ∃! v : ℝ, 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v) := by
  let g : ℝ → ℝ := fun v => z * H v - h * (1 - 2 * v)
  have hg : Continuous g :=
    (H_continuous.const_mul z).sub
      ((continuous_const.sub (continuous_const.mul continuous_id)).const_mul h)
  have hzero : g 0 = -h := by simp [g]
  have hhalf : g (1 / 2) = z := by simp only [g, H_half]; ring
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    hg.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show (0 : ℝ) ∈ Set.Icc (g 0) (g (1 / 2)) by
    rw [hzero, hhalf]; exact ⟨by linarith, hz.le⟩)
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne hv.1
    intro he
    rw [← he, hzero] at heq
    linarith
  have hv1 : v < 1 / 2 := by
    apply lt_of_le_of_ne hv.2
    intro he
    rw [he, hhalf] at heq
    linarith
  have hveq : z * H v = h * (1 - 2 * v) := sub_eq_zero.mp heq
  refine ⟨v, ⟨hv0, hv1, hveq⟩, ?_⟩
  rintro u ⟨hu0, hu1, hueq⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hH := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨hv0.le, hv1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith
  · exact huv
  · have hH := H_strictMonoOn ⟨hv0.le, hv1.le⟩ ⟨hu0.le, hu1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith

theorem radialContact_spec {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h ∧ radialContact z h < 1 / 2 ∧
      z * H (radialContact z h) = h * (1 - 2 * radialContact z h) := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_radialContact hz hh
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧ z * H u = h * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hu => huniq u hu, fun he => he ▸ hv⟩
  simpa only [radialContact, hset, csInf_singleton] using hv

theorem radialContact_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h := (radialContact_spec hz hh).1

theorem radialContact_lt_half {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    radialContact z h < 1 / 2 := (radialContact_spec hz hh).2.1

theorem radialContact_equation {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * H (radialContact z h) = h * (1 - 2 * radialContact z h) :=
  (radialContact_spec hz hh).2.2

theorem radialContact_eq_of_equation {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv' : v < 1 / 2) (heq : z * H v = h * (1 - 2 * v)) :
    radialContact z h = v := by
  obtain ⟨u, _, huniq⟩ := existsUnique_radialContact hz hh
  exact (huniq _ (radialContact_spec hz hh)).trans (huniq v ⟨hv, hv', heq⟩).symm









theorem radialContact_strictAnti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) :
    radialContact b h < radialContact a h := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec ha hh
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec (ha.trans hab) hh
  by_contra hn
  have huv : radialContact a h ≤ radialContact b h := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ huv
  have hm := mul_le_mul_of_nonneg_left (show 1 - 2 * radialContact b h ≤
      1 - 2 * radialContact a h by linarith) hh.le
  have hg : a * H (radialContact a h) < b * H (radialContact b h) := by
    calc
      a * H (radialContact a h) ≤ a * H (radialContact b h) :=
        mul_le_mul_of_nonneg_left hH ha.le
      _ < b * H (radialContact b h) :=
        mul_lt_mul_of_pos_right hab (H_pos hv (by linarith))
  linarith















end GeneralCK
end

section
namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_image_radius {h : ℝ} (hh : 0 < h) :
    (fun z => radialContact z h) '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  · intro hv
    have hH : 0 < H v := H_pos hv.1 (by linarith [hv.2])
    have hz : 0 < h * (1 - 2 * v) / H v :=
      div_pos (mul_pos hh (by linarith [hv.2])) hH
    refine ⟨h * (1 - 2 * v) / H v, hz, ?_⟩
    apply radialContact_eq_of_equation hz hh hv.1 hv.2
    exact div_mul_cancel₀ _ hH.ne'

theorem continuousAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ContinuousAt (fun r => radialContact r h) z := by
  have hanti : StrictAntiOn (fun r => radialContact r h) (Ioi 0) :=
    fun a ha b _ hab => radialContact_strictAnti_radius ha hab hh
  apply hanti.dual_right.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hz)
  change (fun r => radialContact r h) '' Ioi 0 ∈ 𝓝 (radialContact z h)
  rw [radialContact_image_radius hh]
  exact Ioo_mem_nhds (radialContact_pos hz hh) (radialContact_lt_half hz hh)

theorem radialContact_denominator_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < z * J (radialContact z h) + 2 * h := by
  have hJ := J_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  positivity

theorem hasDerivAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => radialContact r h)
      (-H (radialContact z h) / (z * J (radialContact z h) + 2 * h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1 / 2 := radialContact_lt_half hz hh
  have hH : H v ≠ 0 := (H_pos hv (by linarith)).ne'
  have heq : h * (1 - 2 * v) = z * H v := (radialContact_equation hz hh).symm
  have hd : HasDerivAt (fun u => h * (1 - 2 * u) / H u)
      (-(z * J v + 2 * h) / H v) v := by
    have hd := ((((hasDerivAt_id v).const_mul 2).const_sub 1).const_mul h).div
      (Comparison.hasDerivAt_H hv (by linarith)) hH
    convert! hd using 1
    simp only [id_eq, mul_one, heq]
    field_simp
    ring
  have hD : z * J v + 2 * h ≠ 0 := (radialContact_denominator_pos hz hh).ne'
  have hinv := hd.of_local_left_inverse (continuousAt_radialContact_radius hz hh)
    (div_ne_zero (neg_ne_zero.mpr hD) hH) (by
      filter_upwards [Ioi_mem_nhds hz] with r hr
      have hp := H_pos (radialContact_pos hr hh)
        (show radialContact r h < 1 by linarith [radialContact_lt_half hr hh])
      rw [← radialContact_equation hr hh]
      exact mul_div_cancel_right₀ r hp.ne')
  convert! hinv using 1
  change -H v / (z * J v + 2 * h) = (-(z * J v + 2 * h) / H v)⁻¹
  rw [inv_div, div_neg, neg_div]



theorem hasDerivAt_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h)
      (J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h))) z := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hd := (hasDerivAt_id z).mul
    ((hasDerivAt_J hv hv').comp z (hasDerivAt_radialContact_radius hz hh))
  have heq : (fun r => F r h) =ᶠ[𝓝 z] (fun r => r * J (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    simp only [F, ne_of_gt (show 0 < r from hr), ↓reduceIte]
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [id_eq, one_mul, Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
  ring



namespace Certificates.Mixed

theorem hn_eq_H_mul_log (v : ℝ) : hn v = H v * Real.log 2 := by
  unfold hn H Real.binEntropy
  simp only [Real.log_inv]
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  ring

theorem kap_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    2 * kap v = 2 * hn v + (1 - 2 * v) * (Real.log 2 * J v) := by
  unfold kap hn J
  rw [Real.log_mul hv.ne' (by linarith), Real.log_div (by linarith) hv.ne']
  field_simp
  ring

theorem kap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < kap v := by
  have hi := kap_identity hv (show v < 1 by linarith)
  have hhn : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hj := J_pos hv hv'
  have hr : 0 < (1 - 2 * v) * (Real.log 2 * J v) :=
    mul_pos (by linarith) (mul_pos log_two_pos hj)
  linarith

theorem hasDerivAt_hn {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt hn (J v * Real.log 2) v := by
  simpa only [← hn_eq_H_mul_log] using
    (Comparison.hasDerivAt_H hv hv').mul_const (Real.log 2)

theorem hasDerivAt_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt kap (-(1 - 2 * v) / (2 * v * (1 - v))) v := by
  have hd := (((hasDerivAt_id v).mul ((hasDerivAt_id v).const_sub 1)).log
    (mul_ne_zero hv.ne' (by simpa using (show 1 - v ≠ 0 by linarith)))).neg.div_const 2
  convert! hd using 1
  simp only [id_eq, one_mul, Pi.mul_apply]
  field_simp
  ring

end Certificates.Mixed

open Certificates.Mixed



theorem hasDerivAt_radialSlope {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt radialSlope
      (-hn v * (2 * kap v - (1 - 2 * v)^2) /
        (4 * Real.log 2 * v^2 * (1 - v)^2 * (kap v)^2)) v := by
  have hv1 : v < 1 := by linarith
  have hL : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hvc : 1 - v ≠ 0 := by linarith
  have hr : 1 - 2 * v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hJ : J v = (2 * kap v - 2 * hn v) / ((1 - 2 * v) * Real.log 2) := by
    apply (eq_div_iff (mul_ne_zero hr hL)).2
    nlinarith [kap_identity hv hv1]
  have hdN := (((hasDerivAt_id v).const_mul 2).const_sub 1).mul (hasDerivAt_hn hv hv1)
  have hdD := (((hasDerivAt_id v).const_mul (2 * Real.log 2)).mul
    ((hasDerivAt_id v).const_sub 1)).mul (hasDerivAt_kap hv hv1)
  have hd := (hasDerivAt_J hv hv1).add (hdN.div hdD (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hL) hv.ne') hvc) hk))
  convert! hd using 1
  simp only [id_eq, mul_one, Pi.mul_apply]
  rw [hJ]
  field_simp
  ring

theorem radialContact_denominator_identity {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    (z * J (radialContact z h) + 2 * h) * (1 - 2 * radialContact z h) * Real.log 2 =
      2 * z * kap (radialContact z h) := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hk := kap_identity hv hv'
  rw [hn_eq_H_mul_log] at hk
  have heq := radialContact_equation hz hh
  linear_combination -z * hk - (2 * Real.log 2) * heq

theorem hasDerivAt_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (radialSlope (radialContact z h)) z := by
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  convert! hasDerivAt_F_radius hz hh using 1
  unfold radialSlope
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  field_simp [show J (radialContact z h) * z + 2 * h ≠ 0 by
    simpa only [mul_comm] using hD]
  linear_combination H (radialContact z h) * hi

theorem deriv_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = radialSlope (radialContact z h) :=
  (hasDerivAt_F_radius_slope hz hh).deriv

theorem hasDerivAt_deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (deriv (fun r => F r h))
      (hn (radialContact z h) * (2 * kap (radialContact z h) -
          (1 - 2 * radialContact z h)^2) * H (radialContact z h) /
        (4 * Real.log 2 * (radialContact z h)^2 * (1 - radialContact z h)^2 *
          (kap (radialContact z h))^2 * (z * J (radialContact z h) + 2 * h))) z := by
  have hd := (hasDerivAt_radialSlope (radialContact_pos hz hh)
    (radialContact_lt_half hz hh)).comp z (hasDerivAt_radialContact_radius hz hh)
  have heq : deriv (fun r => F r h) =ᶠ[𝓝 z] (fun r => radialSlope (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact deriv_F_radius_slope hr hh
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem radius_mul_deriv2_F_eq_profile {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z = profile (radialContact z h) := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  unfold profile
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  linear_combination -2 * (H (radialContact z h))^2 *
    (2 * kap (radialContact z h) - (1 - 2 * radialContact z h)^2) * hi

end GeneralCK
end

section
namespace GeneralCK.Scalar







end GeneralCK.Scalar

namespace GeneralCK
open Certificates.Mixed

theorem kap_ge_log_two {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    Real.log 2 ≤ kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hu : v*(1-v) ≤ 1/4 := by nlinarith [sq_nonneg (v-1/2)]
  have hh : Real.log (v*(1-v)) ≤ -2*Real.log 2 := by
    calc
      Real.log (v*(1-v)) ≤ Real.log (1/4) := Real.log_le_log hp hu
      _ = -2*Real.log 2 := by
        rw [show (1/4:ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
        norm_num
  unfold kap
  linarith

theorem kap_sq_gap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < 2*kap v-(1-2*v)^2 := by
  have hk := kap_ge_log_two hv (by linarith)
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  have hr : (1-2*v)^2 ≤ 1 := by nlinarith
  linarith

theorem mixed_profile_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < profile v := by
  have hvc : 0 < 1-v := by linarith
  have hr : 0 < 1-2*v := by linarith
  have hn0 : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hk := kap_pos hv hv'
  have hg := kap_sq_gap_pos hv hv'
  unfold profile
  positivity

theorem deriv2_F_radius_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < deriv (deriv (fun r => F r h)) z := by
  have hp : 0 < z*deriv (deriv (fun r => F r h)) z := by
    rw [radius_mul_deriv2_F_eq_profile hz hh]
    exact mixed_profile_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  exact (mul_pos_iff_of_pos_left hz).mp hp





end GeneralCK
end

section
namespace GeneralCK
open Set

theorem hasDerivAt_e8Theta {x : ℝ} (hx : 0 < x) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (((NormedAlgebra.toNormedSpace ℝ) : NormedSpace ℝ ℝ).toModule) _ _
      e8Theta
      (2 * deriv (deriv (fun r => F r 1)) (2 * x)) x := by
  have hd := (hasDerivAt_deriv_F_radius (show 0 < 2 * x by positivity)
    (by norm_num : (0 : ℝ) < 1)).differentiableAt.hasDerivAt
  have h := hd.comp x ((hasDerivAt_id x).const_mul 2)
  have heq : (deriv (fun r => F r 1)) ∘ (fun y : ℝ => 2 * y) = e8Theta := by
    funext y
    rfl
  rw [← heq]
  convert h using 1 <;> ring

theorem deriv_e8Theta_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv e8Theta x := by
  rw [(hasDerivAt_e8Theta hx).deriv]
  exact mul_pos (by norm_num) (deriv2_F_radius_pos (by positivity) (by norm_num))

theorem continuousOn_e8Theta_pos : ContinuousOn e8Theta (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_e8Theta hx).continuousAt.continuousWithinAt

/-- The normalized slope is strictly increasing on precisely the positive
contact-coordinate domain used in equation (8). -/
theorem strictMonoOn_e8Theta_pos : StrictMonoOn e8Theta (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) continuousOn_e8Theta_pos
  intro x hx
  exact deriv_e8Theta_pos (by simpa using hx)









theorem e8Q_pos {y : ℝ} (hy : y ∈ e8SlopeRange) : 0 < e8Q y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).1

theorem e8Theta_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8Theta (e8Q y) = y := by
  rw [e8Q, dif_pos hy]
  exact (Classical.choose_spec hy).2

/-- The constructed inverse is a left inverse at every positive contact
coordinate. -/
theorem e8Q_e8Theta {x : ℝ} (hx : 0 < x) : e8Q (e8Theta x) = x := by
  have hy : e8Theta x ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  apply strictMonoOn_e8Theta_pos.injOn (e8Q_pos hy) hx
  rw [e8Theta_e8Q hy]

theorem strictMonoOn_e8Q_range : StrictMonoOn e8Q e8SlopeRange := by
  intro s hs t ht hst
  have hqs := e8Q_pos hs
  have hqt := e8Q_pos ht
  by_contra hn
  have hle : e8Q t ≤ e8Q s := le_of_not_gt hn
  have htheta : e8Theta (e8Q t) ≤ e8Theta (e8Q s) :=
    strictMonoOn_e8Theta_pos.monotoneOn hqt hqs hle
  rw [e8Theta_e8Q ht, e8Theta_e8Q hs] at htheta
  exact (not_le_of_gt hst) htheta







end GeneralCK
end

section
namespace GeneralCK
open Set Filter

theorem e8Q_image_slopeRange : e8Q '' e8SlopeRange = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact e8Q_pos hy
  · intro hx
    refine ⟨e8Theta x, ⟨x, hx, rfl⟩, ?_⟩
    exact e8Q_e8Theta hx

/-- The positive slope range is a neighborhood of each of its points.  This
is the local openness needed for differentiating the choice-defined inverse.
-/
theorem e8SlopeRange_mem_nhds {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8SlopeRange ∈ nhds y := by
  let x := e8Q y
  have hx : 0 < x := e8Q_pos hy
  let l : ℝ := x / 2
  let u : ℝ := 3 * x / 2
  have hl : 0 < l := by dsimp [l]; positivity
  have hlu : l ≤ u := by dsimp [l, u]; linarith
  have hxu : x < u := by dsimp [u]; linarith
  have hlx : l < x := by dsimp [l]; linarith
  have hθx : e8Theta x = y := e8Theta_e8Q hy
  have hleft : e8Theta l < y := by
    rw [← hθx]
    exact strictMonoOn_e8Theta_pos hl hx hlx
  have hright : y < e8Theta u := by
    rw [← hθx]
    exact strictMonoOn_e8Theta_pos hx (hx.trans hxu) hxu
  have hcont : ContinuousOn e8Theta (Icc l u) :=
    continuousOn_e8Theta_pos.mono (fun _ hz => hl.trans_le hz.1)
  have hiv : Icc (e8Theta l) (e8Theta u) ⊆ e8Theta '' Icc l u :=
    intermediate_value_Icc hlu hcont
  have hsub : Ioo (e8Theta l) (e8Theta u) ⊆ e8SlopeRange := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hiv ⟨hz.1.le, hz.2.le⟩
    exact ⟨w, hl.trans_le hw.1, rfl⟩
  exact mem_of_superset (Ioo_mem_nhds hleft hright) hsub

theorem continuousAt_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    ContinuousAt e8Q y := by
  apply strictMonoOn_e8Q_range.continuousAt_of_image_mem_nhds
  · exact e8SlopeRange_mem_nhds hy
  · rw [e8Q_image_slopeRange]
    exact Ioi_mem_nhds (e8Q_pos hy)

/-- First inverse-derivative identity for the concrete `e8Q`. -/
theorem hasDerivAt_e8Q {y : ℝ} (hy : y ∈ e8SlopeRange) :
    HasDerivAt e8Q (deriv e8Theta (e8Q y))⁻¹ y := by
  have hq : 0 < e8Q y := e8Q_pos hy
  have hθ := hasDerivAt_e8Theta hq
  have hne : 2 * deriv (deriv (fun r => F r 1)) (2 * e8Q y) ≠ 0 := by
    rw [← hθ.deriv]
    exact ne_of_gt (deriv_e8Theta_pos hq)
  have hinv := hθ.of_local_left_inverse (continuousAt_e8Q hy) hne (by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact e8Theta_e8Q hz)
  rw [hθ.deriv]
  exact hinv





/-- The already-established radial curvature formula, exposed in the form
needed by interval bounds for the inverse recurrence. -/
theorem deriv_e8Theta {x : ℝ} (hx : 0 < x) :
    deriv e8Theta x =
      2 * deriv (deriv (fun r => F r 1)) (2 * x) :=
  (hasDerivAt_e8Theta hx).deriv





end GeneralCK
end

section
namespace GeneralCK

open Set Filter
open Certificates.Mixed

theorem differentiableAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    DifferentiableAt ℝ profile v := by
  have hv1 : v < 1 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hvc : 1-v ≠ 0 := by linarith
  have hr := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hnu := ((hasDerivAt_id v).const_mul 4).mul ((hasDerivAt_id v).const_sub 1)
  have hh := hasDerivAt_hn hv hv1
  have hk' := hasDerivAt_kap hv hv1
  have hnum := (((hr.mul (hh.pow 2)).const_mul 2).mul
    ((hk'.const_mul 2).sub (hr.pow 2)))
  have hden := ((hnu.pow 2).mul (hk'.pow 3)).const_mul (Real.log 2)
  have hd := hnum.div hden (by
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    exact mul_ne_zero log_two_pos.ne'
      (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') hvc))
        (pow_ne_zero _ hk)))
  change DifferentiableAt ℝ
    (fun u : ℝ =>
      2*(1-2*u)*(hn u)^2*(2*kap u-(1-2*u)^2) /
        (Real.log 2*(4*u*(1-u))^2*(kap u)^3)) v
  apply hd.differentiableAt.congr_of_eventuallyEq
  filter_upwards with u
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.div_apply]
  ring

theorem hasDerivAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt profile (deriv profile v) v :=
  (differentiableAt_profile hv hv').hasDerivAt

/-- First derivative of `e8Theta`, rewritten through the compact radial
profile. This equality is valid on the whole positive axis. -/
theorem deriv_e8Theta_eq_profile {x : ℝ} (hx : 0 < x) :
    deriv e8Theta x = profile (radialContact (2*x) 1) / x := by
  rw [deriv_e8Theta hx]
  have hp := radius_mul_deriv2_F_eq_profile
    (z := 2*x) (h := 1) (by positivity) (by norm_num)
  have hf :
      deriv (deriv (fun r => F r 1)) (2*x) =
        profile (radialContact (2*x) 1) / (2*x) := by
    apply (eq_div_iff (by positivity : (2*x : ℝ) ≠ 0)).2
    simpa [mul_comm] using hp
  rw [hf]
  field_simp [hx.ne']

/-- Unconditional second derivative of `e8Theta`. The coefficient remains in
terms of `deriv profile`, avoiding any new analytic premise. -/
theorem hasDerivAt_deriv_e8Theta {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv e8Theta)
      ((((deriv profile (radialContact (2*x) 1) *
          (-H (radialContact (2*x) 1) /
            ((2*x) * J (radialContact (2*x) 1) + 2))) * 2) * x -
        profile (radialContact (2*x) 1)) / x^2) x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hinner : HasDerivAt (fun u : ℝ => radialContact (2*u) 1)
      ((-H v / ((2*x)*J v+2))*2) x := by
    have hc := (hasDerivAt_radialContact_radius (z := 2*x) (h := 1)
      (by positivity) (by norm_num)).comp x ((hasDerivAt_id x).const_mul 2)
    simpa [v, Function.comp_def, mul_assoc] using hc
  have hp := (hasDerivAt_profile hv hvh).comp x hinner
  have hd := hp.div (hasDerivAt_id x) hx.ne'
  have heq : deriv e8Theta =ᶠ[nhds x]
      (profile ∘ (fun u : ℝ => radialContact (2*u) 1)) / id := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    simpa [Function.comp_def, id_eq] using deriv_e8Theta_eq_profile hu
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  dsimp only [v, id_eq, Function.comp_apply]
  ring

end GeneralCK
end

section
namespace GeneralCK

open Set Filter
open Certificates.Mixed

private noncomputable def profileR (v : ℝ) : ℝ := 1 - 2*v
private noncomputable def profileNu (v : ℝ) : ℝ := 4*v*(1-v)
private noncomputable def profileKPrime (v : ℝ) : ℝ :=
  -profileR v / (2*v*(1-v))
private noncomputable def profileA (v : ℝ) : ℝ :=
  2*profileR v*hn v^2*(2*kap v-profileR v^2)
private noncomputable def profileB (v : ℝ) : ℝ :=
  Real.log 2*(profileNu v^2*kap v^3)
private noncomputable def profileAPrime (v : ℝ) : ℝ :=
  2*((-2)*hn v^2 + profileR v*(2*hn v*(J v*Real.log 2))) *
      (2*kap v-profileR v^2) +
    2*profileR v*hn v^2*(2*profileKPrime v-2*profileR v*(-2))
private noncomputable def profileBPrime (v : ℝ) : ℝ :=
  Real.log 2 *
    (2*profileNu v*(4*(1-2*v))*kap v^3 +
      profileNu v^2*(3*kap v^2*profileKPrime v))
noncomputable def profilePrime (v : ℝ) : ℝ :=
  (profileAPrime v*profileB v-profileA v*profileBPrime v) / profileB v^2

/-- The compact profile is smooth to all orders away from its endpoint
singularities. -/
theorem contDiffAt_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    ContDiffAt ℝ ⊤ profile v := by
  have hv1 : v < 1 := by linarith
  have hkap : 0 < -Real.log (v*(1-v))/2 := by
    simpa [kap] using kap_pos hv hv'
  have hden :
      Real.log 2 * (4*v*(1-v))^2 * (-Real.log (v*(1-v))/2)^3 ≠ 0 := by
    positivity
  unfold profile hn kap
  fun_prop (disch := first | assumption | positivity)

theorem hasDerivAt_profile_explicit {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    HasDerivAt profile (profilePrime v) v := by
  have hv1 : v < 1 := by linarith
  have hr0 := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hr : HasDerivAt profileR _ v := hr0.congr_of_eventuallyEq (by
    filter_upwards with u
    simp [profileR])
  have hnu0 := ((hasDerivAt_id v).const_mul 4).mul ((hasDerivAt_id v).const_sub 1)
  have hnu : HasDerivAt profileNu _ v := hnu0.congr_of_eventuallyEq (by
    filter_upwards with u
    simp [profileNu])
  have hh := hasDerivAt_hn hv hv1
  have hk := hasDerivAt_kap hv hv1
  have hk' : HasDerivAt kap (profileKPrime v) v := by
    simpa [profileKPrime, profileR] using hk
  have hA := (((hr.mul (hh.pow 2)).const_mul 2).mul
    ((hk'.const_mul 2).sub (hr.pow 2)))
  have hB := ((hnu.pow 2).mul (hk'.pow 3)).const_mul (Real.log 2)
  have hBne : profileB v ≠ 0 := by
    unfold profileB profileNu
    exact mul_ne_zero log_two_pos.ne'
      (mul_ne_zero
        (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) hv.ne') (by linarith)))
        (pow_ne_zero _ (kap_pos hv hv').ne'))
  have hq := hA.div hB hBne
  have heq : profile =
      ((fun y => 2 * (profileR * hn ^ 2) y) *
        ((fun y => 2 * kap y) - profileR ^ 2)) /
        (fun y => Real.log 2 * (profileNu ^ 2 * kap ^ 3) y) := by
    funext u
    simp [profile, profileR, profileNu, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    ring
  rw [heq]
  refine hq.congr_deriv ?_
  simp [profilePrime, profileA, profileB, profileAPrime,
    profileBPrime, profileR, profileNu, profileKPrime]
  ring

theorem differentiableAt_profilePrime {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    DifferentiableAt ℝ profilePrime v := by
  have hv1 : v < 1 := by linarith
  have hhn := (hasDerivAt_hn hv hv1).differentiableAt
  have hkap := (hasDerivAt_kap hv hv1).differentiableAt
  have hJ := (hasDerivAt_J hv hv1).differentiableAt
  have hvne : v ≠ 0 := hv.ne'
  have hvc : 1-v ≠ 0 := by linarith
  have hkne : kap v ≠ 0 := (kap_pos hv hv').ne'
  unfold profilePrime profileAPrime profileB profileA profileBPrime profileKPrime
    profileR profileNu
  fun_prop (disch := positivity)

theorem differentiableAt_deriv_profile {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    DifferentiableAt ℝ (deriv profile) v := by
  have heq : deriv profile =ᶠ[nhds v] profilePrime := by
    filter_upwards [Ioo_mem_nhds hv hv'] with u hu
    exact (hasDerivAt_profile_explicit hu.1 hu.2).deriv
  exact (differentiableAt_profilePrime hv hv').congr_of_eventuallyEq heq

noncomputable def thetaSecondFormula (x : ℝ) : ℝ :=
  let v := radialContact (2*x) 1
  ((((deriv profile v * (-H v / ((2*x)*J v+2)))*2)*x-profile v) / x^2)

theorem deriv2_e8Theta_eq_formula {x : ℝ} (hx : 0 < x) :
    deriv (deriv e8Theta) x = thetaSecondFormula x := by
  exact (hasDerivAt_deriv_e8Theta hx).deriv

theorem differentiableAt_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ thetaSecondFormula x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hinner : DifferentiableAt ℝ (fun u : ℝ => radialContact (2*u) 1) x := by
    exact ((hasDerivAt_radialContact_radius (z := 2*x) (h := 1)
      (by positivity) (by norm_num)).comp x
        ((hasDerivAt_id x).const_mul 2)).differentiableAt
  have hdp : DifferentiableAt ℝ
      (fun u : ℝ => deriv profile (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (differentiableAt_deriv_profile hv hvh).comp x hinner
  have hp : DifferentiableAt ℝ
      (fun u : ℝ => profile (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (differentiableAt_profile hv hvh).comp x hinner
  have hH : DifferentiableAt ℝ
      (fun u : ℝ => H (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (Comparison.hasDerivAt_H hv (by linarith)).differentiableAt.comp x hinner
  have hJ : DifferentiableAt ℝ
      (fun u : ℝ => J (radialContact (2*u) 1)) x :=
    by simpa [Function.comp_def] using
      (hasDerivAt_J hv (by linarith)).differentiableAt.comp x hinner
  have hden : (2*x)*J v+2 ≠ 0 := by
    have := radialContact_denominator_pos (z := 2*x) (h := 1) (by positivity) (by norm_num)
    simpa [v] using this.ne'
  unfold thetaSecondFormula
  dsimp only
  fun_prop (disch := positivity)

/-- The d2→d3 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv2_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv e8Theta)) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_thetaSecondFormula hx).congr_of_eventuallyEq heq

end GeneralCK
end

section
namespace GeneralCK

open Set Filter

private theorem contDiffAt_succ_of_eventually_hasDerivAt
    {n : ℕ} {f g : ℝ → ℝ} {x : ℝ}
    (hd : ∀ᶠ y in nhds x, HasDerivAt f (g y) y)
    (hg : ContDiffAt ℝ n g x) : ContDiffAt ℝ (n+1) f x := by
  rw [contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun y => ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ) (g y), ?_, ?_⟩
  · exact ⟨{y | HasDerivAt f (g y) y}, hd, fun y hy => hy.hasFDerivAt⟩
  · fun_prop

noncomputable def radialRhs (z : ℝ) : ℝ :=
  -H (radialContact z 1) / (z*J (radialContact z 1)+2)

theorem contDiffAt_H {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    ContDiffAt ℝ ⊤ H v := by
  unfold H Real.binEntropy
  fun_prop (disch := positivity)

theorem contDiffAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    ContDiffAt ℝ ⊤ J v := by
  unfold J
  fun_prop (disch := positivity)

private theorem contDiffAt_radialRhs_of_radial {n : ℕ} {z : ℝ} (hz : 0 < z)
    (hr : ContDiffAt ℝ n (fun r => radialContact r 1) z) :
    ContDiffAt ℝ n radialRhs z := by
  let v := radialContact z 1
  have hv : 0 < v := radialContact_pos hz (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half hz (by norm_num)
  have hH := (contDiffAt_H hv (by linarith)).of_le (m := n) (by simp)
  have hJ := (contDiffAt_J hv (by linarith)).of_le (m := n) (by simp)
  have hden : z*J v+2 ≠ 0 :=
    by simpa [v] using
      (radialContact_denominator_pos (z := z) (h := 1) hz (by norm_num)).ne'
  unfold radialRhs
  fun_prop (disch := first | assumption | positivity)

private theorem eventually_hasDerivAt_radialRhs {z : ℝ} (hz : 0 < z) :
    ∀ᶠ y in nhds z, HasDerivAt (fun r => radialContact r 1) (radialRhs y) y := by
  filter_upwards [Ioi_mem_nhds hz] with y hy
  simpa [radialRhs] using hasDerivAt_radialContact_radius hy (by norm_num : (0:ℝ)<1)

theorem contDiffAt_radialContact_three {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ 3 (fun r => radialContact r 1) z := by
  have h0 : ContDiffAt ℝ 0 (fun r => radialContact r 1) z := by
    rw [contDiffAt_zero]
    exact ⟨Ioi 0, Ioi_mem_nhds hz,
      fun y hy => (continuousAt_radialContact_radius hy (by norm_num)).continuousWithinAt⟩
  have hg0 := contDiffAt_radialRhs_of_radial hz h0
  have h1 := contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg0
  have hg1 := contDiffAt_radialRhs_of_radial hz h1
  have h2 := contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg1
  have hg2 := contDiffAt_radialRhs_of_radial hz h2
  exact contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg2

theorem contDiffAt_thetaSecondFormula_three {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 3 thetaSecondFormula x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hlin : ContDiffAt ℝ 3 (fun u : ℝ => 2*u) x := by fun_prop
  have hrc : ContDiffAt ℝ 3 (fun u : ℝ => radialContact (2*u) 1) x := by
    simpa [Function.comp_def] using
      (contDiffAt_radialContact_three (z := 2*x) (by positivity)).comp x hlin
  have hpTop := contDiffAt_profile hv hvh
  have hp3 := hpTop.of_le (m := 3) (by simp)
  have hdp3 := hpTop.derivWithin (m := 3) (by simp)
  have hH3 := (contDiffAt_H hv (by linarith)).of_le (m := 3) (by simp)
  have hJ3 := (contDiffAt_J hv (by linarith)).of_le (m := 3) (by simp)
  have hpComp : ContDiffAt ℝ 3
      (fun u : ℝ => Certificates.Mixed.profile (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hp3.comp x hrc
  have hdpComp : ContDiffAt ℝ 3
      (fun u : ℝ => deriv Certificates.Mixed.profile (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hdp3.comp x hrc
  have hHComp : ContDiffAt ℝ 3
      (fun u : ℝ => H (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hH3.comp x hrc
  have hJComp : ContDiffAt ℝ 3
      (fun u : ℝ => J (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hJ3.comp x hrc
  have hden : (2*x)*J v+2 ≠ 0 := by
    simpa [v] using
      (radialContact_denominator_pos (z := 2*x) (h := 1)
        (by positivity) (by norm_num)).ne'
  unfold thetaSecondFormula
  dsimp only
  fun_prop (disch := first | assumption | positivity)

theorem contDiffAt_thetaSecondFormula_two {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 thetaSecondFormula x :=
  (contDiffAt_thetaSecondFormula_three hx).of_le (by norm_num)

theorem differentiableAt_deriv_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv thetaSecondFormula) x := by
  have h := (contDiffAt_thetaSecondFormula_two hx).derivWithin
    (m := 1) (by norm_num)
  exact h.differentiableAt_one

/-- The d3→d4 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv3_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_deriv_thetaSecondFormula hx).congr_of_eventuallyEq heq.deriv

theorem differentiableAt_deriv2_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv thetaSecondFormula)) x := by
  have h1 := (contDiffAt_thetaSecondFormula_three hx).derivWithin
    (m := 2) (by norm_num)
  have h2 := h1.derivWithin (m := 1) (by norm_num)
  exact h2.differentiableAt_one

/-- The final d4→d5 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv4_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_deriv2_thetaSecondFormula hx).congr_of_eventuallyEq
    heq.deriv.deriv

end GeneralCK
end

section
namespace GeneralCK.Certificates.E8InverseJet5Bridge

open GeneralCK Set

def ThetaJetReplay (θ : Jet5) : Prop :=
  θ.SoundOn (Ioi 0) ∧
    ∀ x, 0 < x → θ.d0 x = e8Theta x ∧ θ.d1 x = deriv e8Theta x



/-- A compatibility interface retained for callers that supply smoothness
directly.  The concrete instance is discharged unconditionally below. -/
def E8ThetaSmooth345 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv e8Theta)) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

/-- Compatibility interface for the last two soundness links. -/
def E8ThetaSmooth45 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x ∧
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

/-- Compatibility interface for the final soundness link. -/
def E8ThetaSmooth5 : Prop :=
  ∀ x : ℝ, 0 < x →
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x

theorem e8ThetaSmooth45_of_smooth5 (h : E8ThetaSmooth5) :
    E8ThetaSmooth45 := by
  intro x hx
  exact ⟨GeneralCK.differentiableAt_deriv3_e8Theta hx, h x hx⟩

/-- The final smoothness premise follows from the `C³` regularity of the
explicit second-derivative formula. -/
theorem e8Theta_smooth5 : E8ThetaSmooth5 := by
  intro x hx
  exact GeneralCK.differentiableAt_deriv4_e8Theta hx

theorem e8ThetaSmooth345_of_smooth45 (h : E8ThetaSmooth45) :
    E8ThetaSmooth345 := by
  intro x hx
  exact ⟨GeneralCK.differentiableAt_deriv2_e8Theta hx, (h x hx).1, (h x hx).2⟩

/-- Construction of the full replay from explicit smoothness links. -/
theorem e8ThetaCanonicalJet5_replay (h : E8ThetaSmooth345) :
    ThetaJetReplay e8ThetaCanonicalJet5 := by
  constructor
  · intro x hx
    have hh := h x hx
    simp only [e8ThetaCanonicalJet5]
    exact ⟨(hasDerivAt_e8Theta hx).differentiableAt.hasDerivAt,
      (GeneralCK.hasDerivAt_deriv_e8Theta hx).differentiableAt.hasDerivAt,
      hh.1.hasDerivAt, hh.2.1.hasDerivAt, hh.2.2.hasDerivAt⟩
  · intro x _
    simp [e8ThetaCanonicalJet5]

/-- Full canonical replay from the two residual higher-smoothness links. -/
theorem e8ThetaCanonicalJet5_replay_of_smooth45 (h : E8ThetaSmooth45) :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay (e8ThetaSmooth345_of_smooth45 h)

/-- Full canonical replay from the sole residual d4→d5 link. -/
theorem e8ThetaCanonicalJet5_replay_of_smooth5 (h : E8ThetaSmooth5) :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay_of_smooth45 (e8ThetaSmooth45_of_smooth5 h)

/-- Unconditional order-five replay for the concrete E8 theta function. -/
theorem e8ThetaCanonicalJet5_replay_unconditional :
    ThetaJetReplay e8ThetaCanonicalJet5 :=
  e8ThetaCanonicalJet5_replay_of_smooth5 e8Theta_smooth5



theorem e8QJet5_soundAt {θ : Jet5} (hθ : ThetaJetReplay θ)
    {y : ℝ} (hy : y ∈ e8SlopeRange) : (e8QJet5 θ).SoundAt y := by
  let A := fun z => θ.d1 (e8Q z)
  let B := fun z => θ.d2 (e8Q z)
  let C := fun z => θ.d3 (e8Q z)
  let D := fun z => θ.d4 (e8Q z)
  let E := fun z => θ.d5 (e8Q z)
  let r := fun z => (A z)⁻¹
  have hqpos : 0 < e8Q y := e8Q_pos hy
  have hs := hθ.1 (e8Q y) hqpos
  have hAeq : A y = deriv e8Theta (e8Q y) := hθ.2 _ hqpos |>.2
  have hAne : A y ≠ 0 := by
    rw [hAeq]
    exact (deriv_e8Theta_pos hqpos).ne'
  have hq1 : HasDerivAt e8Q (r y) y := by
    simpa [r, A, hAeq] using hasDerivAt_e8Q hy
  have hA : HasDerivAt A (B y*r y) y := by
    convert! hs.2.1.comp y hq1 using 1 <;> simp [A, B, r, Function.comp_def]
  have hB : HasDerivAt B (C y*r y) y := by
    convert! hs.2.2.1.comp y hq1 using 1 <;> simp [B, C, r, Function.comp_def]
  have hC : HasDerivAt C (D y*r y) y := by
    convert! hs.2.2.2.1.comp y hq1 using 1 <;> simp [C, D, r, Function.comp_def]
  have hD : HasDerivAt D (E y*r y) y := by
    convert! hs.2.2.2.2.comp y hq1 using 1 <;> simp [D, E, r, Function.comp_def]
  have hr0 := hA.inv hAne
  have hr : HasDerivAt r (-B y*r y^3) y := by
    convert! hr0 using 1 <;> simp only [r] <;> field_simp [hAne] <;> ring
  refine ⟨hq1, hr, ?_, ?_, ?_⟩
  · have h := (hB.mul (hr.pow 3)).neg
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((hB.pow 2).mul (hr.pow 5)).const_mul 3 |>.sub
      (hC.mul (hr.pow 4))
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((hB.pow 3).mul (hr.pow 7)).const_mul (-15)).add
      ((((hB.mul hC).mul (hr.pow 6)).const_mul 10).sub
        (hD.mul (hr.pow 5)))
    convert! h using 1 <;>
      simp [e8QJet5, A, B, C, D, E, r, Pi.mul_apply, Pi.pow_apply] <;>
      first | (funext u; simp <;> ring) | ring









end GeneralCK.Certificates.E8InverseJet5Bridge
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8InverseJet5Bridge
open GeneralCK Set
theorem solution
    {y : ℝ} (hy : y ∈ e8SlopeRange) :
    (e8QJet5 e8ThetaCanonicalJet5).SoundAt y :=
  e8QJet5_soundAt e8ThetaCanonicalJet5_replay_unconditional hy

-- Prove2me | solution 1 for GeneralCK.Correction.Natural.kernel_eq_actual_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:53:00.168578+00:00
-- url     : https://prove2.me/submissions/321d921d-5276-4ee9-8cea-807d79467985

import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries
import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn
import Theorems.Thm_GeneralCK_entropyInverse_H_lower
import Theorems.Thm_GeneralCK_entropyInverse_spec

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

/-- Simultaneous nonzero scaling leaves the defining root set unchanged. -/
theorem radialContact_scale (z h : ℝ) {c : ℝ} (hc : c ≠ 0) :
    radialContact (c * z) (c * h) = radialContact z h := by
  unfold radialContact
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, mul_assoc, mul_right_inj' hc]







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



theorem radialContact_normalize_radius {z : ℝ} (hz : z ≠ 0) (h : ℝ) :
    radialContact z h = radialContact 1 (h / z) := by
  have hs := radialContact_scale z h (c := z⁻¹) (inv_ne_zero hz)
  simpa only [inv_mul_cancel₀ hz, ← div_eq_inv_mul] using hs.symm

theorem radialContact_normalize_entropy (z : ℝ) {h : ℝ} (hh : h ≠ 0) :
    radialContact z h = radialContact (z / h) 1 := by
  have hs := radialContact_scale z h (c := h⁻¹) (inv_ne_zero hh)
  simpa only [inv_mul_cancel₀ hh, ← div_eq_inv_mul] using hs.symm









end GeneralCK
end

section
namespace GeneralCK.Certificates.Reflection

























theorem biasE_eq_binEntropy {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.binEntropy ((1-c)/2) := by
  have hm : 0 < 1-c := by linarith
  have hp : 0 < 1+c := by linarith
  rw [Real.binEntropy]
  rw [Real.log_inv, Real.log_inv]
  rw [show 1-(1-c)/2 = (1+c)/2 by ring]
  rw [Real.log_div hm.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div hp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  unfold biasE
  ring







end GeneralCK.Certificates.Reflection
end

section
namespace GeneralCK





theorem entropyInverse_mono {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    entropyInverse a ≤ entropyInverse b := by
  obtain ⟨ha0, ha1, hea⟩ := entropyInverse_spec ha (hab.trans hb)
  obtain ⟨hb0, hb1, heb⟩ := entropyInverse_spec (ha.trans hab) hb
  by_contra hn
  have := H_strictMonoOn ⟨hb0, hb1⟩ ⟨ha0, ha1⟩ (lt_of_not_ge hn)
  rw [hea, heb] at this
  linarith









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



theorem entropyInverse_strictMonoOn : StrictMonoOn entropyInverse (Icc 0 1) := by
  intro a ha b hb hab
  apply lt_of_le_of_ne (entropyInverse_mono ha.1 hb.2 hab.le)
  intro he
  have h := congrArg H he
  rw [(entropyInverse_spec ha.1 ha.2).2.2, (entropyInverse_spec hb.1 hb.2).2.2] at h
  exact ne_of_lt hab h





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
namespace GeneralCK
open Set Filter
open scoped Topology



namespace Correction






theorem gap_pos {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) : 0 < gap e f := by
  exact sub_pos.mpr (entropyInverse_strictMonoOn
    ⟨he.le, (hef.trans hf).le⟩ ⟨(he.trans hef).le, hf.le⟩ hef)

theorem mid_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < mid e f := by
  unfold mid
  linarith
















































































end Correction
end GeneralCK
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology






theorem biasE_eq_log_mul_E {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.log 2*E c := by
  rw [biasE_eq_binEntropy hc hc']
  unfold E H
  field_simp



























end GeneralCK.Reflection
end

section
namespace GeneralCK.Correction.Natural
open Certificates.Mixed Certificates.Reflection Reflection

theorem biasE_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasE (1-2*v) = hn v := by
  rw [biasE_eq_log_mul_E (by linarith) (by linarith), hn_eq_H_mul_log]
  unfold Reflection.E
  rw [show (1-(1-2*v))/2=v by ring]
  ring

theorem biasB_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasB (1-2*v) = kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  unfold biasB kap
  rw [show 1-(1-2*v)*(1-2*v)=2^2*(v*(1-v)) by ring,
    Real.log_mul (by norm_num : (2:ℝ)^2 ≠ 0) hp.ne',Real.log_pow]
  ring

theorem A_probability (v : ℝ) :
    2*SmallMean.A (1-2*v) = Real.log 2*J v := by
  unfold SmallMean.A J
  rw [show (1+(1-2*v))/(1-(1-2*v))=(1-v)/v by ring]
  field_simp





theorem Fs_probability (v : ℝ) (hv : 0 < v) (hv' : v < 1) :
    Fs (1-2*v) = Real.log 2*radialSlope v := by
  unfold Fs
  rw [A_probability, biasE_probability hv hv', biasB_probability hv hv']
  unfold radialSlope
  rw [show (1-(1-2*v)^2)/4=v*(1-v) by ring]
  field_simp

theorem Fs_contact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Fs (1-2*radialContact z h) = Real.log 2*deriv (fun r => F r h) z := by
  rw [deriv_F_radius_slope hz hh]
  exact Fs_probability _ (radialContact_pos hz hh)
    (lt_trans (radialContact_lt_half hz hh) (by norm_num))

theorem Fss_contact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Fss (1-2*radialContact z h) (2*Real.log 2*h) =
      Real.log 2*deriv (deriv (fun r => F r h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1/2 := radialContact_lt_half hz hh
  have hk := (kap_pos hv hv').ne'
  have hv1 : v < 1 := by linarith
  have hnv : 1-v ≠ 0 := by linarith
  have heq : z*hn v = h*(1-2*v)*Real.log 2 := by
    rw [hn_eq_H_mul_log]
    linear_combination Real.log 2 * radialContact_equation hz hh
  have hd := radius_mul_deriv2_F_eq_profile hz hh
  change z * _ = profile v at hd
  rw [mul_comm z, ← eq_div_iff hz.ne'] at hd
  rw [hd]
  change Fss (1-2*v) (2*Real.log 2*h) = _
  unfold Fss
  rw [biasE_probability hv hv1, biasB_probability hv hv1]
  unfold profile
  rw [show (1-(1-2*v)^2)/4=v*(1-v) by ring]
  field_simp [hk, hv.ne', hnv, hz.ne', hh.ne', log_two_pos.ne']
  linear_combination 16*(hn v)^2*(2*kap v-(1-2*v)^2)*heq














theorem jn_inverse (e : ℝ) : jn (entropyInverse e) = naturalJ e := by
  unfold jn naturalJ J
  field_simp

theorem entropySum_inverse {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    entropySum (entropyInverse e) (entropyInverse f) = 2*Real.log 2*mid e f := by
  unfold entropySum
  rw [hn_eq_H_mul_log,hn_eq_H_mul_log,
    (entropyInverse_spec he.le (hef.trans hf).le).2.2,
    (entropyInverse_spec (he.trans hef).le hf.le).2.2]
  unfold mid
  ring

theorem contact_inverse {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    contact (entropyInverse e) (entropyInverse f) = 1-2*radialContact (gap e f) (mid e f) := by
  unfold contact
  rw [entropySum_inverse he hef hf]
  unfold biasContact
  rw [radialContact_normalize_radius (gap_pos he hef hf).ne']
  congr 2
  unfold gap
  field_simp

theorem kernel_components {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    au (entropyInverse e) (entropyInverse f) = Aleft e f ∧
    nw (entropyInverse e) (entropyInverse f) = rightNumerator e f ∧
    zu (entropyInverse e) (entropyInverse f) = Zleft e f ∧
    zw (entropyInverse e) (entropyInverse f) = Zright e f ∧
    weight (entropyInverse e) (entropyInverse f) = rankWeight e f := by
  have hg := gap_pos he hef hf
  have hm := mid_pos he hef
  have hnorm : 0 < normalized e f := div_pos hg hm
  have hfs : Fs (contact (entropyInverse e) (entropyInverse f)) =
      Real.log 2*deriv (fun r => F r 1) (normalized e f) := by
    rw [contact_inverse he hef hf,
      radialContact_normalize_entropy (gap e f) hm.ne']
    exact Fs_contact hnorm (by norm_num)
  have hss := Fss_contact hg hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold au
    rw [jn_inverse,jn_inverse,hfs]
    unfold Aleft naturalJ qp q gap
    ring
  · unfold nw
    rw [jn_inverse,jn_inverse,hfs]
    unfold rightNumerator qp q gap
    ring
  · unfold zu
    rw [jn_inverse,entropySum_inverse he hef hf]
    unfold Zleft normalized naturalJ qp q gap
    field_simp
  · unfold zw
    rw [jn_inverse,entropySum_inverse he hef hf]
    unfold Zright normalized naturalJ qp q gap
    field_simp
  · unfold weight
    rw [contact_inverse he hef hf,entropySum_inverse he hef hf,hss]
    unfold rankWeight
    ring

/-- The actual left minor equals the numerical source expression. -/
theorem m11_eq_Mleft {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    m11 (entropyInverse e) (entropyInverse f) = Mleft e f := by
  obtain ⟨ha, _, hz, _, hw⟩ := kernel_components he hef hf
  unfold m11
  rw [ha,hz,hw]
  rfl

/-- The cancellation-free numerical determinant is the actual cleared determinant. -/
theorem kdet_eq_Kfactored {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    kdet (entropyInverse e) (entropyInverse f) = Kfactored e f := by
  obtain ⟨ha, hn, hz, hz', hw⟩ := kernel_components he hef hf
  unfold kdet
  rw [ha,hn,hz,hz',hw,jn_inverse]
  rfl







/-- Direct probability-coordinate interface for a numerical compact certificate. -/
theorem kernel_eq_actual {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    m11 u w = Mleft (H u) (H w) ∧
    kdet u w = Kfactored (H u) (H w) := by
  have he := H_pos hu (by linarith)
  have hef := H_strictMonoOn ⟨hu.le, (huw.trans hw).le⟩
    ⟨(hu.trans huw).le, hw.le⟩ huw
  have hf : H w < 1 := by
    have ht := H_strictMonoOn ⟨(hu.trans huw).le, hw.le⟩
      (by norm_num : (1/2 : ℝ) ∈ Set.Icc 0 (1/2)) hw
    simpa only [H_half] using ht
  have hm := m11_eq_Mleft he hef hf
  have hk := kdet_eq_Kfactored he hef hf
  rw [entropyInverse_H_lower hu.le (huw.trans hw).le,
    entropyInverse_H_lower (hu.trans huw).le hw.le] at hm hk
  exact ⟨hm,hk⟩

end GeneralCK.Correction.Natural
end

section
namespace GeneralCK.Correction.Natural

/-- A closed interval certificate may have `rho ≤ 1`; the actual entropy
Hessian bridge only evaluates interior points, for which `rho < 1` is supplied
separately by the ordered-triangle domain. -/
theorem ratio_point_interior {u rho : ℝ} (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    u < u+rho*(1/2-u) ∧ u+rho*(1/2-u) < 1/2 := by
  constructor
  · nlinarith [mul_pos hr hhalf]
  · nlinarith [mul_pos (sub_pos.mpr hr1) hhalf]






end GeneralCK.Correction.Natural
end

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural

theorem solution {u rho : ℝ} (hu : 0 < u) (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    m11 u (u+rho*(1/2-u)) = Mleft (H u) (H (u+rho*(1/2-u))) ∧
    kdet u (u+rho*(1/2-u)) = Kfactored (H u) (H (u+rho*(1/2-u))) := by
  obtain ⟨huw, hw⟩ := ratio_point_interior hhalf hr hr1
  exact kernel_eq_actual hu huw hw

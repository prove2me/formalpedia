-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001Certified.cellPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T04:36:04.196687+00:00
-- url     : https://prove2.me/submissions/a69f2540-33ec-4082-977c-7409538c84a1

import Definitions.Def_GeneralCK_E8_Prod0001_graph_mixed_data
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_Prod0001_leaf_data
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_first_cell_jet_graphs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_reusable_cell_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8TAxisCellCertificateSchema_Certificate_cellPositive
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001CertifiedArithmetic_centerEnclosed_of_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001CertifiedArithmetic_replay_positive
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001CertifiedArithmetic_wholeEnclosed_of_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001Certified_centerBoxes_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001Certified_wholeBoxes_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeA_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeB_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeC_covers_slope
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_wholeD_covers_slope
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





end Certificates.Mixed

open Certificates.Mixed





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
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology






theorem biasE_eq_log_mul_E {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.log 2*E c := by
  rw [biasE_eq_binEntropy hc hc']
  unfold E H
  field_simp

















theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]









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




































end GeneralCK.Correction.Natural
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology













theorem biasE_pos_wide {c : ℝ} (hc : -1<c) (hc' : c<1) : 0<biasE c := by
  rw [biasE_eq_binEntropy hc hc']
  exact Real.binEntropy_pos (by linarith) (by linarith)







































end GeneralCK.Reflection
end

section
namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection Certificates.Reflection





theorem radialContact_two_mul_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    radialContact (2 * xParamReal c) 1 = (1 - c) / 2 := by
  have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
  have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 0 < H ((1 - c) / 2) := H_pos (by linarith) (by linarith)
  have hz : 0 < 2 * xParamReal c := by
    unfold xParamReal
    positivity
  apply radialContact_eq_of_equation hz (by norm_num)
  · linarith
  · linarith
  have hp := Correction.Natural.biasE_probability
    (v := (1 - c) / 2) (by linarith) (by linarith)
  rw [show 1 - 2 * ((1 - c) / 2) = c by ring] at hp
  unfold xParamReal
  rw [hp, Certificates.Mixed.hn_eq_H_mul_log]
  field_simp [hE.ne', hH.ne']
  ring

/-- Exact stable parametrization of the manuscript slope on `0 < c < 1`. -/
theorem e8Theta_xParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Theta (xParamReal c) = thetaParamReal c := by
  have hx : 0 < xParamReal c := by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hFs := Correction.Natural.Fs_contact
    (z := 2 * xParamReal c) (h := 1) (by positivity) (by norm_num)
  rw [radialContact_two_mul_xParamReal hc hc1,
    show 1 - 2 * ((1 - c) / 2) = c by ring] at hFs
  have hk : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hB : biasB c ≠ 0 := (biasB_pos hc hc1).ne'
  have hcden : 1 - c ^ 2 ≠ 0 := by nlinarith
  calc
    e8Theta (xParamReal c) = Correction.Natural.Fs c / Real.log 2 := by
      unfold e8Theta
      rw [hFs]
      field_simp [hk]
    _ = thetaParamReal c := by
      unfold Correction.Natural.Fs thetaParamReal
      field_simp [hk, hB, hcden]
      ring











end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK.Certificates.E8TAxisStableScalar

open GeneralCK.Reflection GeneralCK.Certificates.Reflection
open GeneralCK.E8AnalyticGerm










theorem z_pos (a : ℝ) : 0 < z a := Real.exp_pos _

theorem one_add_z_pos (a : ℝ) : 0 < 1 + z a := by
  linarith [z_pos a]

theorem z_lt_one {a : ℝ} (ha : 0 < a) : z a < 1 := by
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem r_pos {a : ℝ} (ha : 0 < a) : 0 < r a := by
  exact div_pos (sub_pos.mpr (z_lt_one ha)) (one_add_z_pos a)

theorem r_lt_one (a : ℝ) : r a < 1 := by
  change (1 - z a) / (1 + z a) < 1
  apply (div_lt_one (one_add_z_pos a)).mpr
  linarith [z_pos a]

theorem one_add_r (a : ℝ) : 1 + r a = 2 / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_sub_r (a : ℝ) : 1 - r a = 2 * z a / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_add_r_pos (a : ℝ) : 0 < 1 + r a := by
  rw [one_add_r]
  exact div_pos (by norm_num) (one_add_z_pos a)

theorem one_sub_r_pos (a : ℝ) : 0 < 1 - r a := by
  linarith [r_lt_one a]



theorem one_sub_r_sq (a : ℝ) : 1 - r a ^ 2 = q a := by
  unfold r q
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem log_one_add_r (a : ℝ) :
    Real.log (1 + r a) = Real.log 2 - l1 a := by
  rw [one_add_r]
  exact Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (one_add_z_pos a).ne'

theorem log_one_sub_r (a : ℝ) :
    Real.log (1 - r a) = Real.log 2 - 2 * a - l1 a := by
  rw [one_sub_r, Real.log_div (mul_ne_zero (by norm_num) (z_pos a).ne')
      (one_add_z_pos a).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (z_pos a).ne']
  simp only [z, Real.log_exp, l1]
  ring

theorem A_r (a : ℝ) : SmallMean.A (r a) = a := by
  unfold SmallMean.A
  rw [Real.log_div (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  ring

theorem biasB_r (a : ℝ) : biasB (r a) = ell a := by
  unfold biasB
  rw [show 1 - r a * r a = (1 + r a) * (1 - r a) by ring,
    Real.log_mul (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  unfold ell
  ring

theorem biasE_r (a : ℝ) : biasE (r a) = h a := by
  unfold biasE
  rw [log_one_add_r, log_one_sub_r, one_add_r, one_sub_r]
  unfold h
  field_simp [(one_add_z_pos a).ne'] <;> ring



theorem h_pos {a : ℝ} (ha : 0 < a) : 0 < h a := by
  rw [← biasE_r]
  exact biasE_pos_wide (by linarith [r_pos ha]) (r_lt_one a)

theorem X_eq_xParamReal (a : ℝ) : X a = xParamReal (r a) := by
  unfold X xParamReal
  rw [biasE_r]

theorem Y_eq_thetaParamReal (a : ℝ) : Y a = thetaParamReal (r a) := by
  unfold Y thetaParamReal
  rw [A_r, biasE_r, one_sub_r_sq, biasB_r]

theorem X_pos {a : ℝ} (ha : 0 < a) : 0 < X a := by
  unfold X
  exact div_pos (mul_pos (Real.log_pos (by norm_num)) (r_pos ha))
    (mul_pos (by norm_num) (h_pos ha))



theorem e8Theta_X {a : ℝ} (ha : 0 < a) : e8Theta (X a) = Y a := by
  rw [X_eq_xParamReal, Y_eq_thetaParamReal]
  exact e8Theta_xParamReal (r_pos ha) (r_lt_one a)



end GeneralCK.Certificates.E8TAxisStableScalar
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel












theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

end GeneralCK.Certificates.E8TAxisProd0001Geometry
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0001Geometry E8TAxisProd0001CertifiedArithmetic












end GeneralCK.Certificates.E8TAxisProd0001Certified
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisProd0001Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0001Geometry E8TAxisProd0001CertifiedArithmetic
theorem solution : CellPositive rectangle := by
  apply E8TAxisCellCertificateSchema.Certificate.cellPositive certificate
  · simpa [certificate, rectangle, Rect.Covers, InCell] using center_mem
  · intro s t h
    have hi : InCell s t := by simpa [certificate, rectangle, Rect.Covers, InCell] using h
    rcases hi with ⟨hsl, hsu, htl, htu⟩
    obtain ⟨aa, _, haa, hya⟩ := E8TAxisProd0001EndpointWitnesses.wholeA_covers_slope
      (s := t) ⟨htl, htu⟩
    obtain ⟨ab, _, hab, hyb⟩ := E8TAxisProd0001EndpointWitnesses.wholeB_covers_slope
      (s := 2*s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ac, _, hac, hyc⟩ := E8TAxisProd0001EndpointWitnesses.wholeC_covers_slope
      (s := s+t) ⟨by linarith, by linarith⟩
    obtain ⟨ad, _, had, hyd⟩ := E8TAxisProd0001EndpointWitnesses.wholeD_covers_slope
      (s := s) ⟨hsl, hsu⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hya]; exact ⟨E8TAxisStableScalar.X aa, E8TAxisStableScalar.X_pos haa,
        E8TAxisStableScalar.e8Theta_X haa⟩
    · rw [← hyb]; exact ⟨E8TAxisStableScalar.X ab, E8TAxisStableScalar.X_pos hab,
        E8TAxisStableScalar.e8Theta_X hab⟩
    · rw [← hyc]; exact ⟨E8TAxisStableScalar.X ac, E8TAxisStableScalar.X_pos hac,
        E8TAxisStableScalar.e8Theta_X hac⟩
    · rw [← hyd]; exact ⟨E8TAxisStableScalar.X ad, E8TAxisStableScalar.X_pos had,
        E8TAxisStableScalar.e8Theta_X had⟩
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).1
  · intro s t h
    exact (displacement_mem (by simpa [certificate, rectangle, Rect.Covers, InCell] using h)).2
  · exact centerEnclosed_of_contains centerBoxes_contains
  · intro s t h
    apply wholeEnclosed_of_contains
    apply wholeBoxes_contains
    simpa [certificate, rectangle, Rect.Covers, InCell] using h
  · exact replay_positive

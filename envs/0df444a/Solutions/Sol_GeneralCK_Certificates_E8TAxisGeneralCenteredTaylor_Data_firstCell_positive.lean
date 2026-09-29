-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor.Data.firstCell_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:49:20.702815+00:00
-- url     : https://prove2.me/submissions/684ca604-cee5-4505-bd13-abaf0da92a9e

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_derivative_semantics
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8InverseJet5Bridge_e8QCanonicalJet5_soundAt_unconditional
import Theorems.Thm_GeneralCK_Certificates_E8TAxisTaylor4_exists_remainder
import Theorems.Thm_GeneralCK_Certificates_PilotData_log_two
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

section
namespace GeneralCK.Certificates



namespace DyadicInterval



theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity
theorem scale_cast_pos (p : ℕ) : 0 < (scale p : ℝ) := by exact_mod_cast scale_pos p











theorem floorDiv_mul_le (z : ℤ) {d : ℤ} (hd : 0 < d) : floorDiv z d*d ≤ z :=
  Int.ediv_mul_le z hd.ne'

theorem le_ceilDiv_mul (z : ℤ) {d : ℤ} (hd : 0 < d) : z ≤ ceilDiv z d*d := by
  have h := floorDiv_mul_le (-z) hd
  unfold floorDiv ceilDiv at *
  nlinarith








theorem ofInt_sound (p : ℕ) (z : ℤ) : (ofInt p z).Contains (z : ℝ) := by
  simp [Contains, ofInt]

theorem add_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  rcases hx with ⟨hlx, hux⟩
  rcases hy with ⟨hly, huy⟩
  dsimp [Contains, add]
  push_cast
  constructor <;> nlinarith





private theorem linear_bounds {lo hi x c : ℝ} (hl : lo ≤ x) (hh : x ≤ hi) :
    min (lo*c) (hi*c) ≤ x*c ∧ x*c ≤ max (lo*c) (hi*c) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc),
      (mul_le_mul_of_nonneg_right hh hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh (not_le.mp hc).le),
      (mul_le_mul_of_nonpos_right hl (not_le.mp hc).le).trans (le_max_left _ _)⟩

private theorem product_bounds {al ah bl bh x y : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al*bl) (al*bh)) (min (ah*bl) (ah*bh)) ≤ x*y ∧
      x*y ≤ max (max (al*bl) (al*bh)) (max (ah*bl) (ah*bh)) := by
  have h := linear_bounds (c := y) hx.1 hx.2
  have hl := linear_bounds (c := al) hy.1 hy.2
  have hh := linear_bounds (c := ah) hy.1 hy.2
  simp only [mul_comm y al, mul_comm y ah, mul_comm bl al, mul_comm bh al,
    mul_comm bl ah, mul_comm bh ah] at hl hh
  exact ⟨(min_le_min hl.1 hh.1).trans h.1, h.2.trans (max_le_max hl.2 hh.2)⟩

theorem mul_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have hp := product_bounds hx hy
  have hlo : (productLo a b : ℝ) ≤ ((scale p : ℝ)*x)*((scale p : ℝ)*y) := by
    simpa [productLo, or_assoc] using hp.1
  have hhi : ((scale p : ℝ)*x)*((scale p : ℝ)*y) ≤ (productHi a b : ℝ) := by
    simpa [productHi, or_assoc] using hp.2
  have hroundL : ((floorDiv (productLo a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) ≤ (productLo a b : ℝ) := by
    exact_mod_cast floorDiv_mul_le (productLo a b) (scale_pos p)
  have hroundH : (productHi a b : ℝ) ≤ ((ceilDiv (productHi a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) := by
    exact_mod_cast le_ceilDiv_mul (productHi a b) (scale_pos p)
  have hs := scale_cast_pos p
  constructor
  · change (floorDiv (productLo a b) (scale p) : ℝ) ≤ (scale p : ℝ)*(x*y)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hroundL.trans hlo]
  · change (scale p : ℝ)*(x*y) ≤ (ceilDiv (productHi a b) (scale p) : ℝ)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hhi.trans hroundH]

theorem recip_sound {p : ℕ} {a : DyadicInterval p} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.Contains x) : a.recip.Contains (x⁻¹) := by
  have hs := scale_cast_pos p
  have hlo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hxpos : 0 < x := pos_of_mul_pos_right (hlo.trans_le hx.1) hs.le
  have hhi : (0:ℝ) < a.hi := (mul_pos hs hxpos).trans_le hx.2
  have hhiZ : 0 < a.hi := by exact_mod_cast hhi
  have hrL : (floorDiv (scale p*scale p) a.hi : ℝ)*(a.hi : ℝ) ≤ (scale p : ℝ)^2 := by
    have h := floorDiv_mul_le (scale p*scale p) hhiZ
    exact_mod_cast (by simpa only [pow_two] using h : floorDiv (scale p*scale p) a.hi*a.hi ≤ (scale p)^2)
  have hrH : (scale p : ℝ)^2 ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)*(a.lo : ℝ) := by
    have h := le_ceilDiv_mul (scale p*scale p) ha
    exact_mod_cast (by simpa only [pow_two] using h : (scale p)^2 ≤ ceilDiv (scale p*scale p) a.lo*a.lo)
  constructor
  · change (floorDiv (scale p*scale p) a.hi : ℝ) ≤ (scale p : ℝ)*x⁻¹
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.hi : ℝ) := (le_div_iff₀ hhi).mpr hrL
      _ ≤ (scale p : ℝ)/x := by
        apply (div_le_div_iff₀ hhi hxpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.2 hs.le]
  · change (scale p : ℝ)*x⁻¹ ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.lo : ℝ) := by
        apply (div_le_div_iff₀ hxpos hlo).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.1 hs.le]
      _ ≤ _ := (div_le_iff₀ hlo).mpr hrH






theorem positiveCheck_sound {p : ℕ} {a : DyadicInterval p}
    (h : a.positiveCheck=true) {x : ℝ} (hx : a.Contains x) : 0 < x := by
  have ha : 0 < a.lo := by simpa [positiveCheck] using h
  have ha' : (0:ℝ) < a.lo := by exact_mod_cast ha
  exact pos_of_mul_pos_right (ha'.trans_le hx.1) (scale_cast_pos p).le









end DyadicInterval
end GeneralCK.Certificates
end

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

theorem deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z =
      J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h)) :=
  (hasDerivAt_F_radius hz hh).deriv

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
namespace GeneralCK















theorem e8Theta_pos {x : ℝ} (hx : 0 < x) : 0 < e8Theta x := by
  unfold e8Theta
  have hz : 0 < 2 * x := by positivity
  rw [deriv_F_radius hz (by norm_num : (0 : ℝ) < 1)]
  have hv := radialContact_pos hz (by norm_num : (0 : ℝ) < 1)
  have hvh := radialContact_lt_half hz (by norm_num : (0 : ℝ) < 1)
  have hv1 : radialContact (2 * x) 1 < 1 := by linarith
  have hJ := J_pos hv hvh
  have hH := H_pos hv hv1
  have hcenter := radialContact_denominator_pos hz (by norm_num : (0 : ℝ) < 1)
  have hfrac : 0 <
      (2 * x) * H (radialContact (2 * x) 1) /
        (Real.log 2 * radialContact (2 * x) 1 *
          (1 - radialContact (2 * x) 1) *
          ((2 * x) * J (radialContact (2 * x) 1) + 2 * 1)) := by
    positivity
  linarith

















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



theorem e8SlopeRange_subset_pos : e8SlopeRange ⊆ Ioi 0 := by
  rintro y ⟨x, hx, rfl⟩
  exact e8Theta_pos hx

theorem e8SlopeRange_isPreconnected : IsPreconnected e8SlopeRange := by
  exact isPreconnected_Ioi.image _ continuousOn_e8Theta_pos



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









end GeneralCK
end

section
namespace GeneralCK
open Set Filter



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















end GeneralCK
end

section
namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection.ComplexEntropy
























private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))











theorem hasDerivAt_xParam_zero : CDeriv xParam (1 / 2) 0 := by
  have hE : CDeriv entropyExt 0 0 := by
    simpa [entropyDeriv] using hasDerivAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have h := ((hasDerivAt_const (𝕜 := ℂ) 0 (Real.log 2 : ℂ)).mul
    (hasDerivAt_id 0)).div
      ((hasDerivAt_const (𝕜 := ℂ) 0 2).mul hE) (by
        simp only [Pi.mul_apply, Reflection.ComplexContactGerm.entropyExt_zero]
        exact mul_ne_zero (by norm_num) logTwo_ne)
  convert! h using 1
  · simp only [Reflection.ComplexContactGerm.entropyExt_zero, id_eq,
      zero_mul, mul_zero, add_zero, sub_zero, Pi.mul_apply]
    field_simp [logTwo_ne]
    simpa using (div_self logTwo_ne).symm



private theorem deriv_thetaParam_zero :
    deriv thetaParam 0 = 4 / (Real.log 2 : ℂ) :=
  hasDerivAt_thetaParam_zero.deriv

private theorem deriv_thetaParam_ne : deriv thetaParam 0 ≠ 0 := by
  rw [deriv_thetaParam_zero]
  exact div_ne_zero (by norm_num) logTwo_ne











theorem hasDerivAt_biasGerm_zero :
    CDeriv biasGerm ((Real.log 2 : ℂ) / 4) 0 := by
  have h := analyticAt_thetaParam.hasStrictDerivAt.to_localInverse deriv_thetaParam_ne
  have hk : ((4 / (Real.log 2 : ℂ))⁻¹) = (Real.log 2 : ℂ) / 4 := by
    field_simp [logTwo_ne]
  simpa [biasGerm, deriv_thetaParam_zero, hk] using h.hasDerivAt



/-- The analytic germ has the manuscript's exact linear coefficient. -/
theorem hasDerivAt_qGerm_zero :
    CDeriv qGerm ((Real.log 2 : ℂ) / 8) 0 := by
  have hx : CDeriv xParam (1 / 2) (biasGerm 0) := by
    simpa using hasDerivAt_xParam_zero
  have h := hx.comp (0 : ℂ) hasDerivAt_biasGerm_zero
  convert! h using 1
  · ring















end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK.Reflection.ComplexRealBridge

open Set Function
open Certificates.Reflection
open ComplexEntropy ComplexFixedPoint

/-- On the real interval `(-1,1)`, the principal-log extension is exactly the
real bias entropy used in the manuscript. -/
theorem entropyExt_ofReal {c : ℝ} (hc₀ : -1 < c) (hc₁ : c < 1) :
    entropyExt (c : ℂ) = (biasE c : ℂ) := by
  have hp : 0 ≤ 1 + c := (by linarith : 0 ≤ 1 + c)
  have hm : 0 ≤ 1 - c := (by linarith : 0 ≤ 1 - c)
  have hpLog : Complex.log (1 + (c : ℂ)) = (Real.log (1 + c) : ℂ) := by
    calc
      Complex.log (1 + (c : ℂ)) = Complex.log ((1 + c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 + c) : ℂ) := (Complex.ofReal_log hp).symm
  have hmLog : Complex.log (1 - (c : ℂ)) = (Real.log (1 - c) : ℂ) := by
    calc
      Complex.log (1 - (c : ℂ)) = Complex.log ((1 - c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 - c) : ℂ) := (Complex.ofReal_log hm).symm
  unfold entropyExt biasE
  rw [hpLog, hmLog]
  norm_num













end GeneralCK.Reflection.ComplexRealBridge
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

/-- Therefore the global positive inverse recovers the stable contact coordinate. -/
theorem e8Q_thetaParamReal {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    e8Q (thetaParamReal c) = xParamReal c := by
  rw [← e8Theta_xParamReal hc hc1]
  exact e8Q_e8Theta (by
    unfold xParamReal
    have hE : 0 < biasE c := biasE_pos_wide (by linarith) hc1
    have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity)

theorem atanhExt_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    atanhExt (c : ℂ) = (SmallMean.A c : ℂ) := by
  have hp : 0 ≤ 1 + c := by linarith
  have hm : 0 ≤ 1 - c := by linarith
  have hp0 : 1 + c ≠ 0 := by linarith
  have hm0 : 1 - c ≠ 0 := by linarith
  unfold atanhExt SmallMean.A
  rw [show 1 + (c : ℂ) = ((1 + c : ℝ) : ℂ) by norm_num,
    show 1 - (c : ℂ) = ((1 - c : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_log hp, ← Complex.ofReal_log hm, Real.log_div hp0 hm0]
  norm_num

theorem biasBExt_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    biasBExt (c : ℂ) = (biasB c : ℂ) := by
  have hnonneg : 0 ≤ 1 - c ^ 2 := by nlinarith
  unfold biasBExt biasB
  rw [show 1 - (c : ℂ) ^ 2 = ((1 - c * c : ℝ) : ℂ) by
      norm_num [pow_two],
    ← Complex.ofReal_log (by simpa [pow_two] using hnonneg)]
  norm_num [pow_two]

/-- Both stable complex formulas restrict exactly to their real counterparts. -/
theorem param_ofReal {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    thetaParam (c : ℂ) = (thetaParamReal c : ℂ) ∧
      xParam (c : ℂ) = (xParamReal c : ℂ) := by
  rw [thetaParam, xParam, thetaParamReal, xParamReal,
    atanhExt_ofReal hc0 hc1, biasBExt_ofReal hc0 hc1,
    Reflection.ComplexRealBridge.entropyExt_ofReal hc0 hc1]
  constructor <;> push_cast <;> ring

/-- On all sufficiently small positive slopes in the stable parametrization,
the analytic germ agrees exactly with the choice-defined positive inverse. -/
theorem eventually_qGerm_eq_e8Q_param :
    ∀ᶠ c in nhdsWithin (0 : ℝ) (Ioi 0),
      qGerm (thetaParamReal c : ℂ) = (e8Q (thetaParamReal c) : ℂ) := by
  have hleft := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse
    (by
      rw [hasDerivAt_thetaParam_zero.deriv]
      exact div_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))))
  change ∀ᶠ z in nhds (0 : ℂ), biasGerm (thetaParam z) = z at hleft
  have hcast : Tendsto ((↑) : ℝ → ℂ) (nhds (0 : ℝ)) (nhds (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hpull : Filter.Eventually
      (fun c : ℝ => biasGerm (thetaParam (c : ℂ)) = (c : ℂ)) (nhds 0) :=
    hcast.eventually hleft
  have hsmall : Filter.Eventually (fun c : ℝ => c ∈ Ioo (-1) 1) (nhds 0) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hpull' := hpull.filter_mono
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0)
  have hsmall' := hsmall.filter_mono
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0)
  filter_upwards [self_mem_nhdsWithin, hpull', hsmall'] with c hcpos hfix hc
  rcases param_ofReal hc.1 hc.2 with ⟨htheta, hx⟩
  rw [← htheta, qGerm, hfix, hx]
  exact_mod_cast (e8Q_thetaParamReal hcpos hc.2).symm

end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK

theorem e8Q_zero : e8Q 0 = 0 := by
  rw [e8Q]
  split_ifs with h
  · have hfalse : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    exact False.elim (hfalse (by simpa using e8SlopeRange_subset_pos h))
  · rfl









theorem deriv_e8Delta_right (Q : ℝ → ℝ) (s t : ℝ)
    (hB : DifferentiableAt ℝ Q (2 * s + t))
    (hC : DifferentiableAt ℝ Q (s + t))
    (hA : DifferentiableAt ℝ Q t) :
    deriv (fun u => e8Delta Q s u) t = e8DeltaDerivT Q s t := by
  have hBt := hB.hasDerivAt.comp t
    ((hasDerivAt_const t (2 * s)).add (hasDerivAt_id t))
  have hCt := hC.hasDerivAt.comp t
    ((hasDerivAt_const t s).add (hasDerivAt_id t))
  have hAt := hA.hasDerivAt
  have hD := hasDerivAt_const t (Q s)
  have h := ((hBt.sub hD).mul (hCt.sub hAt)).sub
    ((hBt.sub hCt).mul (hD.add hAt))
  have heq : (fun u => e8Delta Q s u) =ᶠ[nhds t]
      ((Q ∘ fun u => 2 * s + u) - fun _ => Q s) *
          ((Q ∘ fun u => s + u) - Q) -
        ((Q ∘ fun u => 2 * s + u) - (Q ∘ fun u => s + u)) *
          ((fun _ => Q s) + Q) := by
    filter_upwards with u
    rfl
  have hd := (h.congr_of_eventuallyEq heq).deriv
  convert hd using 1 <;> simp only [e8DeltaDerivT, Function.comp_apply,
    Pi.sub_apply, Pi.add_apply] <;> ring

















end GeneralCK
end

section
namespace GeneralCK.Certificates.E8PositiveAxisGermJet

open Set Filter SignType
open GeneralCK E8AnalyticGerm

theorem thetaParamReal_zero : thetaParamReal 0 = 0 := by
  have h := (param_ofReal (c := 0) (by norm_num) (by norm_num)).1
  norm_num [thetaParam_zero] at h
  exact_mod_cast h.symm

/-- The real stable slope parametrization is a local equivalence at the
origin, with its exact positive derivative. -/
theorem hasStrictDerivAt_thetaParamReal_zero :
    HasStrictDerivAt thetaParamReal (4 / Real.log 2) 0 := by
  have hcast : ((4 / Real.log 2 : ℝ) : ℂ) =
      (4 : ℂ) / (Real.log 2 : ℂ) := by
    exact_mod_cast rfl
  have hc : HasStrictDerivAt thetaParam
      ((4 / Real.log 2 : ℝ) : ℂ) 0 := by
    rw [hcast, ← hasDerivAt_thetaParam_zero.deriv]
    exact analyticAt_thetaParam.hasStrictDerivAt
  have hr := hc.real_of_complex
  have heq :
      (fun c : ℝ => (thetaParam (c : ℂ)).re) =ᶠ[nhds 0] thetaParamReal := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact congrArg Complex.re (param_ofReal hc.1 hc.2).1
  simpa only [Complex.ofReal_re] using hr.congr_of_eventuallyEq heq

/-- The parametrized real-axis identity fills an ordinary punctured
neighborhood of slope zero.  This is the form needed for local derivative
congruence. -/
theorem eventually_qGerm_eq_e8Q :
    ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      qGerm (y : ℂ) = (e8Q y : ℂ) := by
  let a : ℝ := 4 / Real.log 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hθ : HasStrictDerivAt thetaParamReal a 0 := by
    simpa [a] using hasStrictDerivAt_thetaParamReal_zero
  let g : ℝ → ℝ := hθ.localInverse thetaParamReal a 0 ha.ne'
  have hg : HasStrictDerivAt g a⁻¹ 0 := by
    simpa [g, thetaParamReal_zero] using hθ.to_localInverse ha.ne'
  have hg0 : g 0 = 0 := by
    simpa [g, thetaParamReal_zero] using
      (hθ.hasStrictFDerivAt_equiv ha.ne').localInverse_apply_image
  have hright : ∀ᶠ y in nhds (0 : ℝ), thetaParamReal (g y) = y := by
    simpa [g, thetaParamReal_zero] using hθ.eventually_right_inverse ha.ne'
  have hsign : ∀ᶠ y in nhds (0 : ℝ), sign (g y) = sign y := by
    simpa [hg0] using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := g) (x₀ := 0) (by simpa [hg.hasDerivAt.deriv] using inv_pos.mpr ha) hg0
  have hgpos : ∀ᶠ y in nhdsWithin (0 : ℝ) (Ioi 0), 0 < g y := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hsy hy
    rw [← sign_eq_one_iff, hsy, sign_eq_one_iff]
    exact hy
  have hgtend : Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa [hg0] using
          hg.hasDerivAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        hgpos⟩
  have hpull := hgtend.eventually eventually_qGerm_eq_e8Q_param
  filter_upwards [hpull, hright.filter_mono nhdsWithin_le_nhds] with y hy hrighty
  simpa [hrighty] using hy

/-- All sufficiently small positive slopes lie in the actual positive range
of `e8Theta`.  This removes the zero-filled branch before differentiating the
inverse recurrence. -/
theorem eventually_mem_e8SlopeRange :
    ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), y ∈ e8SlopeRange := by
  have hqder : HasDerivAt (fun y : ℝ => (qGerm (y : ℂ)).re)
      (Real.log 2 / 8) 0 := by
    convert hasDerivAt_qGerm_zero.real_of_complex using 1
    norm_num [Complex.div_re]
    exact (Complex.log_ofReal_re 2).symm
  have hqderpos : 0 < deriv (fun y : ℝ => (qGerm (y : ℂ)).re) 0 := by
    rw [hqder.deriv]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hsign : ∀ᶠ y : ℝ in nhds (0 : ℝ),
      sign ((qGerm (y : ℂ)).re) = sign y := by
    simpa using eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := fun y : ℝ => (qGerm (y : ℂ)).re) (x₀ := 0)
      hqderpos
      (by simp)
  filter_upwards [eventually_qGerm_eq_e8Q,
    hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y heq hs hy
  have hqpos : 0 < (qGerm (y : ℂ)).re := by
    rw [← sign_eq_one_iff, hs, sign_eq_one_iff]
    exact hy
  have hey : e8Q y = (qGerm (y : ℂ)).re := by
    simpa using congrArg Complex.re heq.symm
  by_contra hn
  have hz : e8Q y = 0 := by simp [e8Q, hn]
  linarith











end GeneralCK.Certificates.E8PositiveAxisGermJet
end

section
namespace GeneralCK.Certificates.E8TAxisCenteredReplaySoundness

open DyadicInterval E8TAxisOneCellArithmetic Set















/-- Exact real polynomial corresponding to the grouped raw ray derivatives. -/
theorem centeredValue_eq (c r : ℕ → ℕ → ℝ) (x y : ℝ) :
    centeredValue c r x y = c 0 1 +
      (c 0 2 * y + c 1 1 * x) +
      (c 0 3 * y ^ 2 + 2 * c 1 2 * x * y + c 2 1 * x ^ 2) / 2 +
      (c 0 4 * y ^ 3 + 3 * c 1 3 * x * y ^ 2 +
        3 * c 2 2 * x ^ 2 * y + c 3 1 * x ^ 3) / 6 +
      (r 0 5 * y ^ 4 + 4 * r 1 4 * x * y ^ 3 +
        6 * r 2 3 * x ^ 2 * y ^ 2 + 4 * r 3 2 * x ^ 3 * y + r 4 1 * x ^ 4) / 24 := by
  unfold centeredValue
  ring






end GeneralCK.Certificates.E8TAxisCenteredReplaySoundness
end

section
namespace GeneralCK

open Set Filter
open Certificates Certificates.E8PositiveAxisGermJet
open Certificates.E8InverseJet5Bridge E8AnalyticGerm



theorem e8RegularQ_eq_e8Q {y : ℝ} (hy : 0 ≤ y) :
    e8RegularQ y = e8Q y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [e8RegularQ, e8Q_zero]
  · simp [e8RegularQ, hy]









theorem e8SlopeRange_downward {x y : ℝ}
    (hx : x ∈ e8SlopeRange) (hy : 0 < y) (hyx : y ≤ x) :
    y ∈ e8SlopeRange := by
  have hsmallN : ∀ᶠ z : ℝ in nhds 0, z < y := Iio_mem_nhds hy
  have hsmall : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), z < y :=
    hsmallN.filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz, hzy⟩ := (eventually_mem_e8SlopeRange.and hsmall).exists
  exact e8SlopeRange_isPreconnected.ordConnected.out hz hx ⟨hzy.le, hyx⟩

private theorem contDiffOn_succ_of_derivative {U : Set ℝ} (hU : IsOpen U)
    {f g : ℝ → ℝ} {n : ℕ}
    (hd : ∀ x ∈ U, HasDerivAt f (g x) x)
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g U) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f U := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen hU).2
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    norm_cast at h
  · exact hg.congr (fun x hx => (hd x hx).deriv)

theorem e8Q_contDiffOn_four : ContDiffOn ℝ 4 e8Q e8SlopeRange := by
  have hopen : IsOpen e8SlopeRange := isOpen_iff_mem_nhds.mpr
    (fun _ hx => e8SlopeRange_mem_nhds hx)
  let j := e8QJet5 e8ThetaCanonicalJet5
  have hj : ∀ x ∈ e8SlopeRange, j.SoundAt x :=
    fun _ hx => e8QCanonicalJet5_soundAt_unconditional hx
  have h4 : ContDiffOn ℝ 0 j.d4 e8SlopeRange :=
    contDiffOn_zero.mpr (fun x hx =>
      (hj x hx).2.2.2.2.continuousAt.continuousWithinAt)
  have h3 : ContDiffOn ℝ 1 j.d3 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 0) (fun x hx => (hj x hx).2.2.2.1) h4
  have h2 : ContDiffOn ℝ 2 j.d2 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 1) (fun x hx => (hj x hx).2.2.1) h3
  have h1 : ContDiffOn ℝ 3 j.d1 e8SlopeRange :=
    contDiffOn_succ_of_derivative hopen (n := 2) (fun x hx => (hj x hx).2.1) h2
  exact contDiffOn_succ_of_derivative hopen (n := 3) (fun x hx => (hj x hx).1) h1

theorem e8RegularQ_contDiffAt_of_mem {y : ℝ} (hy : y ∈ e8SlopeRange) :
    ContDiffAt ℝ 4 e8RegularQ y := by
  have hq : ContDiffAt ℝ 4 e8Q y :=
    e8Q_contDiffOn_four.contDiffAt (e8SlopeRange_mem_nhds hy)
  apply hq.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
  exact e8RegularQ_eq_e8Q hz.le









end GeneralCK
end

section
namespace GeneralCK.Certificates.E8TAxisDeltaDirectionalJet

open GeneralCK Set
open E8InverseJet5Bridge





theorem sound4At_of_soundAt {j : Jet5} {u : ℝ} (h : j.SoundAt u) :
    Sound4At j u :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩



theorem Sound4At.add {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (a.add b) u :=
  ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.add hb.2.2.2⟩

theorem Sound4At.neg {a : Jet5} {u : ℝ} (ha : Sound4At a u) :
    Sound4At a.neg u :=
  ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.neg⟩



theorem Sound4At.sub {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (sub a b) u :=
  ha.add hb.neg

theorem Sound4At.mul {a b : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) : Sound4At (a.mul b) u := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring
  · have h := (((ha.2.2.2.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext v; simp <;> ring) | ring



theorem Sound4At.affine {j : Jet5} {c m u : ℝ}
    (h : Sound4At j (c + m * u)) : Sound4At (affine j c m) u := by
  have hi : HasDerivAt (fun v : ℝ => c + m * v) m u := by
    convert! (hasDerivAt_const u c).add ((hasDerivAt_id u).const_mul m) using 1 <;>
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! h.1.comp u hi using 1 <;> simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]
  · convert! (h.2.1.comp u hi).mul_const m using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring
  · convert! (h.2.2.1.comp u hi).mul_const (m ^ 2) using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring
  · convert! (h.2.2.2.comp u hi).mul_const (m ^ 3) using 1 <;>
      (try simp [E8TAxisDeltaDirectionalJet.affine, Function.comp_def]) <;> ring



theorem sound4At_shift {j : Jet5} {u : ℝ} (h : j.SoundAt u) :
    Sound4At (shift j) u :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩





theorem qJet_soundAt {y : ℝ} (hy : y ∈ e8SlopeRange) : qJet.SoundAt y :=
  e8QCanonicalJet5_soundAt_unconditional hy

theorem qJet_sound4At {y : ℝ} (hy : y ∈ e8SlopeRange) : Sound4At qJet y :=
  sound4At_of_soundAt (qJet_soundAt hy)

theorem qPrimeJet_sound4At {y : ℝ} (hy : y ∈ e8SlopeRange) :
    Sound4At qPrimeJet y :=
  sound4At_shift (qJet_soundAt hy)



theorem qJet_d0_eq_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qJet.d0 y = e8RegularQ y :=
  (e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le).symm

theorem qPrimeJet_d0_eq_deriv_regular {y : ℝ} (hy : y ∈ e8SlopeRange) :
    qPrimeJet.d0 y = deriv e8RegularQ y := by
  have hq : HasDerivAt e8Q (qPrimeJet.d0 y) y := (qJet_soundAt hy).1
  have he : e8RegularQ =ᶠ[nhds y] e8Q := by
    filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
    exact e8RegularQ_eq_e8Q hz.le
  exact (hq.congr_of_eventuallyEq he).deriv.symm



theorem sound4At_deltaTGraph {a b c d ap bp cp : Jet5} {u : ℝ}
    (ha : Sound4At a u) (hb : Sound4At b u) (hc : Sound4At c u)
    (hd : Sound4At d u) (hap : Sound4At ap u) (hbp : Sound4At bp u)
    (hcp : Sound4At cp u) : Sound4At (deltaTGraph a b c d ap bp cp) u :=
  ((hbp.mul (hc.sub ha)).add ((hb.sub hd).mul (hcp.sub hap))).add
    (((hbp.sub hcp).mul (hd.add ha)).neg) |>.add (((hb.sub hc).mul hap).neg)





theorem deltaTJet_sound4At {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4At (deltaTJet s0 t0 ds dt) u := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u ∈ e8SlopeRange := by
    rw [show (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.1
  have hC : (s0 + t0) + (ds + dt) * u ∈ e8SlopeRange := by
    rw [show (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) by ring]
    exact h.2.2.1
  exact sound4At_deltaTGraph
    (qJet_sound4At h.1).affine (qJet_sound4At hB).affine
    (qJet_sound4At hC).affine (qJet_sound4At h.2.2.2).affine
    (qPrimeJet_sound4At h.1).affine (qPrimeJet_sound4At hB).affine
    (qPrimeJet_sound4At hC).affine

theorem deltaTJet_sound4On {s0 t0 ds dt : ℝ} {S : Set ℝ}
    (h : ∀ u ∈ S, InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    Sound4On (deltaTJet s0 t0 ds dt) S :=
  fun u hu => deltaTJet_sound4At (h u hu)

theorem deltaTJet_d0_eq_regular {s0 t0 ds dt u : ℝ}
    (h : InputsInRange (s0 + ds * u) (t0 + dt * u)) :
    (deltaTJet s0 t0 ds dt).d0 u =
      e8RegularDeltaT (s0 + ds * u) (t0 + dt * u) := by
  have hB : (2 * s0 + t0) + (2 * ds + dt) * u =
      2 * (s0 + ds * u) + (t0 + dt * u) := by ring
  have hC : (s0 + t0) + (ds + dt) * u =
      (s0 + ds * u) + (t0 + dt * u) := by ring
  have hregB : DifferentiableAt ℝ e8RegularQ
      (2 * (s0 + ds * u) + (t0 + dt * u)) :=
    (e8RegularQ_contDiffAt_of_mem h.2.1).differentiableAt (by norm_num)
  have hregC : DifferentiableAt ℝ e8RegularQ
      ((s0 + ds * u) + (t0 + dt * u)) :=
    (e8RegularQ_contDiffAt_of_mem h.2.2.1).differentiableAt (by norm_num)
  have hregA : DifferentiableAt ℝ e8RegularQ (t0 + dt * u) :=
    (e8RegularQ_contDiffAt_of_mem h.1).differentiableAt (by norm_num)
  rw [e8RegularDeltaT, deriv_e8Delta_right e8RegularQ _ _ hregB hregC hregA]
  dsimp only [deltaTJet, deltaTGraph, sub, Jet5.add, Jet5.neg, Jet5.mul, affine]
  rw [hB, hC, qJet_d0_eq_regular h.1, qJet_d0_eq_regular h.2.1,
    qJet_d0_eq_regular h.2.2.1, qJet_d0_eq_regular h.2.2.2,
    qPrimeJet_d0_eq_deriv_regular h.1,
    qPrimeJet_d0_eq_deriv_regular h.2.1,
    qPrimeJet_d0_eq_deriv_regular h.2.2.1]
  simp only [e8DeltaDerivT]
  ring




end GeneralCK.Certificates.E8TAxisDeltaDirectionalJet
end

section
namespace GeneralCK.Certificates.E8TAxisBivariateTaylor

open GeneralCK E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisOneCellArithmetic Set

set_option maxHeartbeats 2000000

theorem ray_d0 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d0 u = mixed qJet (s0 + x*u) (t0 + y*u) 0 1 := by
  simp only [deltaTJet, deltaTGraph, sub, affine, qPrimeJet, shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d1 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d1 u =
      mixed qJet (s0+x*u) (t0+y*u) 0 2 * y +
      mixed qJet (s0+x*u) (t0+y*u) 1 1 * x := by
  simp only [deltaTJet, deltaTGraph, sub, affine, qPrimeJet, shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d2 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d2 u =
      mixed qJet (s0+x*u) (t0+y*u) 0 3 * y^2 +
      2 * mixed qJet (s0+x*u) (t0+y*u) 1 2 * x*y +
      mixed qJet (s0+x*u) (t0+y*u) 2 1 * x^2 := by
  simp only [deltaTJet, deltaTGraph, sub, affine, qPrimeJet, shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d3 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d3 u =
      mixed qJet (s0+x*u) (t0+y*u) 0 4 * y^3 +
      3 * mixed qJet (s0+x*u) (t0+y*u) 1 3 * x*y^2 +
      3 * mixed qJet (s0+x*u) (t0+y*u) 2 2 * x^2*y +
      mixed qJet (s0+x*u) (t0+y*u) 3 1 * x^3 := by
  simp only [deltaTJet, deltaTGraph, sub, affine, qPrimeJet, shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring

theorem ray_d4 (s0 t0 x y u : ℝ) :
    (deltaTJet s0 t0 x y).d4 u =
      mixed qJet (s0+x*u) (t0+y*u) 0 5 * y^4 +
      4 * mixed qJet (s0+x*u) (t0+y*u) 1 4 * x*y^3 +
      6 * mixed qJet (s0+x*u) (t0+y*u) 2 3 * x^2*y^2 +
      4 * mixed qJet (s0+x*u) (t0+y*u) 3 2 * x^3*y +
      mixed qJet (s0+x*u) (t0+y*u) 4 1 * x^4 := by
  simp only [deltaTJet, deltaTGraph, sub, affine, qPrimeJet, shift,
    Jet5.add, Jet5.neg, Jet5.mul, mixed]
  rw [show 2*s0+t0+(2*x+y)*u = 2*(s0+x*u)+(t0+y*u) by ring,
    show s0+t0+(x+y)*u = (s0+x*u)+(t0+y*u) by ring]
  ring






end GeneralCK.Certificates.E8TAxisBivariateTaylor
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

theorem q_pos (a : ℝ) : 0 < q a := by
  unfold q
  exact div_pos (mul_pos (by norm_num) (z_pos a)) (pow_pos (one_add_z_pos a) 2)

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

theorem ell_pos {a : ℝ} (ha : 0 < a) : 0 < ell a := by
  rw [← biasB_r]
  exact biasB_pos (r_pos ha) (r_lt_one a)

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
namespace GeneralCK.Certificates.E8TAxisOneCellGeometry

open GeneralCK DyadicInterval E8TAxisOneCellArithmetic E8TAxisDeltaDirectionalJet Set










theorem center_mem : InFirstCell centerS centerT := by
  norm_num [InFirstCell, sLower, tLower, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InFirstCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, tLower] at hs0 ht0
  norm_num [Contains, ds, dt, centerS, centerT, scale, precision]
  constructor <;> constructor <;> linarith

theorem segment_mem {s t u : ℝ} (h : InFirstCell s t) (hu : u ∈ Icc (0 : ℝ) 1) :
    InFirstCell (centerS + (s - centerS) * u) (centerT + (t - centerT) * u) := by
  have segment {a b c x : ℝ} (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
      c + (x - c) * u ∈ Icc a b := by
    have hh := (convex_Icc a b) hc hx (sub_nonneg.mpr hu.2) hu.1
      (show (1 - u) + u = 1 by ring)
    convert hh using 1 <;> simp only [smul_eq_mul] <;> ring
  have hc := center_mem
  have hs := segment ⟨hc.1, hc.2.1⟩ ⟨h.1, h.2.1⟩
  have ht := segment hc.2.2 h.2.2
  exact ⟨hs.1, hs.2, ht⟩

theorem inputsInRange_of_cell {s t : ℝ} (h : InFirstCell s t)
    (hmax : (17 / 100 : ℝ) ∈ e8SlopeRange) : InputsInRange s t := by
  have hs : 0 < s := lt_of_lt_of_le (by norm_num [sLower]) h.1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num [tLower]) h.2.2.1
  have hB : 2 * s + t ≤ 17 / 100 := by linarith [h.2.1, h.2.2.2]
  exact ⟨e8SlopeRange_downward hmax ht (by linarith),
    e8SlopeRange_downward hmax (by positivity) hB,
    e8SlopeRange_downward hmax (by positivity) (by linarith),
    e8SlopeRange_downward hmax hs (by linarith)⟩

/-- A coarse analytic range bound suffices for all Taylor segments.  This
does not assert coverage by any of the numerical inverse-parameter boxes. -/
theorem upperSlope_mem : (17 / 100 : ℝ) ∈ e8SlopeRange := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hc : 2 ≤ 2 / Real.log 2 := (le_div_iff₀ hL).mpr (by linarith)
  have hf : 0 ≤ E8TAxisStableScalar.r 1 * E8TAxisStableScalar.h 1 /
      (E8TAxisStableScalar.q 1 * E8TAxisStableScalar.ell 1) := by
    exact (div_pos
      (mul_pos (E8TAxisStableScalar.r_pos (by norm_num))
        (E8TAxisStableScalar.h_pos (by norm_num)))
      (mul_pos (E8TAxisStableScalar.q_pos 1)
        (E8TAxisStableScalar.ell_pos (by norm_num)))).le
  have hY : 2 ≤ E8TAxisStableScalar.Y 1 := by
    unfold E8TAxisStableScalar.Y
    nlinarith [mul_nonneg (div_pos (by norm_num : (0 : ℝ) < 2) hL).le hf]
  apply e8SlopeRange_downward
    (show E8TAxisStableScalar.Y 1 ∈ e8SlopeRange from
      ⟨E8TAxisStableScalar.X 1, E8TAxisStableScalar.X_pos (by norm_num),
        E8TAxisStableScalar.e8Theta_X (by norm_num)⟩) (by norm_num)
  linarith

theorem segment_inputsInRange {s t : ℝ} (h : InFirstCell s t)
    :
    ∀ u ∈ Icc (0 : ℝ) 1,
      InputsInRange (centerS + (s - centerS) * u) (centerT + (t - centerT) * u) :=
  fun _ hu => inputsInRange_of_cell (segment_mem h hu) upperSlope_mem




end GeneralCK.Certificates.E8TAxisOneCellGeometry
end

section
namespace GeneralCK.Certificates.E8TAxisReparamInterval

open DyadicInterval E8TAxisReparamJet5



theorem powI_sound {p : ℕ} {x : DyadicInterval p} {r : ℝ}
    (hx : x.Contains r) (n : ℕ) : (powI x n).Contains (r ^ n) := by
  induction n with
  | zero => simpa [powI] using ofInt_sound p 1
  | succ n ih => simpa [powI, pow_succ] using mul_sound ih hx












end GeneralCK.Certificates.E8TAxisReparamInterval
end

section
namespace GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor

open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisBivariateTaylor
open E8TAxisOneCellGeometry



namespace Data









theorem term_sound {p : ℕ} {b : Data p} {z x y : ℝ} {i j : ℕ}
    (hz : (b.coeff i (j + 1)).Contains z)
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    (b.term i j).Contains
      (z * x ^ i * y ^ j / ((i.factorial * j.factorial : ℕ) : ℝ)) := by
  have hn : 0 < i.factorial * j.factorial :=
    Nat.mul_pos (Nat.factorial_pos i) (Nat.factorial_pos j)
  have hp : 0 < (ofInt p (i.factorial * j.factorial : ℕ)).lo := by
    dsimp only [ofInt]
    exact mul_pos (scale_pos p) (by exact_mod_cast hn)
  have hh := mul_sound
    (mul_sound (mul_sound hz (E8TAxisReparamInterval.powI_sound hx i))
      (E8TAxisReparamInterval.powI_sound hy j))
    (recip_sound hp (ofInt_sound p (i.factorial * j.factorial : ℕ)))
  simpa only [term, Int.cast_natCast, div_eq_mul_inv] using hh

theorem centeredValue_mem {p : ℕ} {b : Data p} {c r : ℕ → ℕ → ℝ} {x y : ℝ}
    (hc : b.CenterEnclosed c) (hr : b.RemainderEnclosed r)
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    b.replay.Contains (centeredValue c r x y) := by
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hr with ⟨h10, h11, h12, h13, h14⟩
  have t01 := term_sound (i := 0) (j := 1) h1 hx hy
  have t10 := term_sound (i := 1) (j := 0) h2 hx hy
  have t02 := term_sound (i := 0) (j := 2) h3 hx hy
  have t11 := term_sound (i := 1) (j := 1) h4 hx hy
  have t20 := term_sound (i := 2) (j := 0) h5 hx hy
  have t03 := term_sound (i := 0) (j := 3) h6 hx hy
  have t12 := term_sound (i := 1) (j := 2) h7 hx hy
  have t21 := term_sound (i := 2) (j := 1) h8 hx hy
  have t30 := term_sound (i := 3) (j := 0) h9 hx hy
  have t04 := term_sound (i := 0) (j := 4) h10 hx hy
  have t13 := term_sound (i := 1) (j := 3) h11 hx hy
  have t22 := term_sound (i := 2) (j := 2) h12 hx hy
  have t31 := term_sound (i := 3) (j := 1) h13 hx hy
  have t40 := term_sound (i := 4) (j := 0) h14 hx hy
  have hh := add_sound
    (add_sound (add_sound (add_sound (add_sound
      (add_sound (add_sound (add_sound (add_sound
        (add_sound (add_sound (add_sound (add_sound
          (add_sound h0 t01) t10) t02) t11) t20) t03) t12) t21) t30)
      t04) t13) t22) t31) t40
  simpa [replay, centeredValue, Nat.factorial] using hh

end Data

/-- A point on the segment supplies all five remainder coefficients in the
same real centered polynomial used by the interval replay. -/
theorem exists_centeredValue {s0 t0 x y : ℝ}
    (hrange : ∀ u ∈ Icc (0 : ℝ) 1, InputsInRange (s0 + x * u) (t0 + y * u)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      e8RegularDeltaT (s0 + x) (t0 + y) =
        centeredValue (mixed qJet s0 t0)
          (mixed qJet (s0 + x * u) (t0 + y * u)) x y := by
  have hj := deltaTJet_sound4On hrange
  obtain ⟨u, hu, heq⟩ := E8TAxisTaylor4.exists_remainder
    (fun v hv => (hj v hv).1) (fun v hv => (hj v hv).2.1)
    (fun v hv => (hj v hv).2.2.1) (fun v hv => (hj v hv).2.2.2)
  refine ⟨u, hu, ?_⟩
  have hend : (deltaTJet s0 t0 x y).d0 1 = e8RegularDeltaT (s0 + x) (t0 + y) := by
    simpa only [mul_one] using deltaTJet_d0_eq_regular (hrange 1 (by norm_num))
  rw [hend, ray_d0 s0 t0 x y 0, ray_d1 s0 t0 x y 0,
    ray_d2 s0 t0 x y 0, ray_d3 s0 t0 x y 0, ray_d4 s0 t0 x y u] at heq
  simp only [mul_zero, add_zero] at heq
  rw [centeredValue_eq]
  exact heq

namespace Data

theorem replay_contains {p : ℕ} {b : Data p} {s0 t0 x y : ℝ}
    (hrange : ∀ u ∈ Icc (0 : ℝ) 1, InputsInRange (s0 + x * u) (t0 + y * u))
    (hc : b.CenterEnclosed (mixed qJet s0 t0))
    (hr : ∀ u ∈ Ioo (0 : ℝ) 1,
      b.RemainderEnclosed (mixed qJet (s0 + x * u) (t0 + y * u)))
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    b.replay.Contains (e8RegularDeltaT (s0 + x) (t0 + y)) := by
  obtain ⟨u, hu, heq⟩ := exists_centeredValue hrange
  rw [heq]
  exact centeredValue_mem hc (hr u hu) hx hy

/-- Specialization to the retained first-cell displacement intervals. -/
theorem firstCell_contains {b : Data E8TAxisOneCellArithmetic.precision}
    (hds : b.ds = E8TAxisOneCellArithmetic.ds)
    (hdt : b.dt = E8TAxisOneCellArithmetic.dt)
    (hc : b.CenterEnclosed (mixed qJet centerS centerT))
    (hr : ∀ s t, InFirstCell s t → b.RemainderEnclosed (mixed qJet s t))
    {s t : ℝ} (h : InFirstCell s t) :
    b.replay.Contains (e8RegularDeltaT s t) := by
  have hd := displacement_mem h
  have hx : b.ds.Contains (s - centerS) := by rw [hds]; exact hd.1
  have hy : b.dt.Contains (t - centerT) := by rw [hdt]; exact hd.2
  have hh := replay_contains (segment_inputsInRange h) hc
    (fun u hu => hr _ _ (segment_mem h ⟨hu.1.le, hu.2.le⟩)) hx hy
  simpa only [show centerS + (s - centerS) = s by ring,
    show centerT + (t - centerT) = t by ring] using hh



end Data





end GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor.Data
open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisBivariateTaylor
open E8TAxisOneCellGeometry
theorem solution {b : Data E8TAxisOneCellArithmetic.precision}
    (hds : b.ds = E8TAxisOneCellArithmetic.ds)
    (hdt : b.dt = E8TAxisOneCellArithmetic.dt)
    (hc : b.CenterEnclosed (mixed qJet centerS centerT))
    (hr : ∀ s t, InFirstCell s t → b.RemainderEnclosed (mixed qJet s t))
    (hp : b.replay.positiveCheck = true) {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t :=
  positiveCheck_sound hp (firstCell_contains hds hdt hc hr h)

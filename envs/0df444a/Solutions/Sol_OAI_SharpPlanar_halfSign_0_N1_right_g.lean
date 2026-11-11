-- Prove2me | solution 1 for OAI.SharpPlanar.halfSign_0_N1_right_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:34:05.886947+00:00
-- url     : https://prove2.me/submissions/901b4705-973b-41e6-94e1-d30680cab5e4

import Mathlib
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1651
import Definitions.Def_OAIQ098G1653
import Definitions.Def_OAIQ098G1675
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1695
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_Bernstein0_N1_right_ts_contains_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_X_norm_g
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_bernsteinBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_direct_spectral_bound_g
import Theorems.Thm_OAI_SharpPlanar_error_zero_cap_g
import Theorems.Thm_OAI_SharpPlanar_fullMoment_direct_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
import Theorems.Thm_OAI_SharpPlanar_pieceL_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_realSpectral_norm_g
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_g
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_summand_bound_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_coeff_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_u_bound_g
import Theorems.Thm_OAI_SharpPlanar_v_bound_g
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Finset

lemma choose_ratio_identity {d k r : ℕ} (hr : r ≤ d) (hk : r ≤ k) :
    (k.choose r : ℝ) / (d.choose r : ℝ) * (d.choose k : ℝ) =
      ((d-r).choose (k-r) : ℝ) := by
  have hden : (d.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  have he : (d.choose k : ℝ) * (k.choose r : ℝ) =
      (d.choose r : ℝ) * ((d-r).choose (k-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul hk
  rw [div_mul_eq_mul_div,div_eq_iff hden]
  simpa [mul_comm] using he

lemma monomial_bernstein {d r : ℕ} (hr : r ≤ d) (v : ℝ) :
    (∑ k ∈ Ico r (d+1), (k.choose r : ℝ) / (d.choose r : ℝ) *
      bernsteinWeight d k v) = v^r := by
  rw [sum_Ico_eq_sum_range]
  have hs : d+1-r = d-r+1 := by omega
  rw [hs]
  trans v^r * (∑ k ∈ range (d-r+1), v^k * (1-v)^(d-r-k) * ((d-r).choose k : ℝ))
  · rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hrk : r+k-r = k := by omega
    have hsub : d-(r+k) = d-r-k := by omega
    unfold bernsteinWeight
    rw [← mul_assoc,← mul_assoc,choose_ratio_identity hr (Nat.le_add_right r k),hrk,hsub,pow_add]
    ring
  · rw [← add_pow]
    simp

lemma bernstein_identity (d : ℕ) (T : ℕ → ℝ) (v : ℝ) :
    (∑ r ∈ range (d+1), T r * v^r) =
      ∑ k ∈ range (d+1), powerToBernstein d T k * bernsteinWeight d k v := by
  unfold powerToBernstein
  simp_rw [sum_mul]
  have hswap := sum_Ico_Ico_comm 0 (d+1)
    (fun r k => (k.choose r : ℝ) / (d.choose r : ℝ) * T r * bernsteinWeight d k v)
  simp only [Nat.Ico_zero_eq_range] at hswap
  rw [← hswap]
  apply sum_congr rfl
  intro r hr
  have hrd : r ≤ d := by simpa only [mem_range,Nat.lt_succ_iff] using hr
  rw [← monomial_bernstein hrd v,mul_sum]
  apply sum_congr rfl
  intro k hk
  ring

lemma bernsteinWeight_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (d k : ℕ) :
    0 ≤ bernsteinWeight d k v := by
  unfold bernsteinWeight
  have : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  have hv0 : 0 ≤ v := hv.1
  positivity
lemma sum_bernsteinWeight (d : ℕ) (v : ℝ) :
    (∑ k ∈ range (d+1), bernsteinWeight d k v) = 1 := by
  have h := add_pow v (1-v) d
  simp only [add_sub_cancel,one_pow] at h
  rw [h]
  apply sum_congr rfl
  intro k hk
  unfold bernsteinWeight
  ring


lemma bernstein_lower {d : ℕ} {T : ℕ → ℝ} {a v : ℝ}
    (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k ∈ range (d+1), a ≤ powerToBernstein d T k) :
    a ≤ ∑ r ∈ range (d+1), T r * v^r := by
  rw [bernstein_identity]
  calc
    a = ∑ k ∈ range (d+1), a * bernsteinWeight d k v := by rw [← mul_sum,sum_bernsteinWeight,mul_one]
    _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hB k hk) (bernsteinWeight_nonneg hv d k)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound_g n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound_g p.x n j ht)
    exact (X_summable_pairs_g p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound_g p.x n j ht)
          ((X_summable_pairs_g p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm_g]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound_g _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos_g) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos_g.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density_g p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval_g hj ht) |>.intervalIntegrable

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma pieceMass_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceMass j t ≤ pieceMass j s := by
  have ht : 0 ≤ t := hs.trans hst
  unfold pieceMass
  split_ifs with htz hsz hsz
  · rfl
  · exfalso
    have hz : slopeCap j*s=0 := by
      apply le_antisymm
      · calc
          _ ≤ slopeCap j*t := mul_le_mul_of_nonneg_left hst (slopeCap_nonneg_g _)
          _ = 0 := htz
      · exact mul_nonneg (slopeCap_nonneg_g _) hs
    exact hsz hz
  · exact min_le_left _ _
  · apply min_le_min_left
    apply one_div_le_one_div_of_le
    · have hh : 0 < slopeCap j*s := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg_g _) hs) (Ne.symm hsz)
      simpa only [mul_assoc] using mul_pos Real.pi_pos hh
    · exact mul_le_mul_of_nonneg_left hst (mul_nonneg Real.pi_pos.le (slopeCap_nonneg_g _))

lemma pieceL_shift_bound (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    pieceL j (s+t) ≤ Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t)*pieceL j s := by
  have hm := pieceMass_antitone j hs (show s ≤ s+t by linarith)
  unfold pieceL
  rw [mul_add,Real.exp_add]
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
        Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t))*pieceMass j s := by
      exact mul_le_mul_of_nonneg_left hm (mul_nonneg (lambdaCap_nonneg_g _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    _ = _ := by ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein0
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma bound0 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 37) (v := 50) (bernsteinBox_contains_g ts_contains_g ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound (k : Fin 29) : (37:ℝ)/50<powerToBernstein 28 (sourcePower true 0 (1/2) 0) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N1_right
end SharpPlanar.Bernstein0

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

lemma Pmoment_hasDerivAt (ell : ℕ) (s : ℝ) :
    HasDerivAt (Pmoment ell) (Pmoment (ell+1) s) s := by
  have hh (j : ℕ) : HasDerivAt (fun s : ℝ =>
      2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s))
      (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^(ell+1) *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)) s := by
    have he := (((hasDerivAt_id (s : ℂ)).const_mul
      (Complex.I*Real.pi*((j : ℝ)/6 : ℝ))).comp_ofReal).cexp.const_mul
        (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell)
    convert he using 1 <;> first | rfl | (simp only [mul_one, pow_succ, id_eq]; ring)
  have hd := ((hasDerivAt_const s (Pcoeff 0*(0 : ℂ)^ell)).add
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.Icc (1 : ℕ) 6) => hh j)))
  have hdr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert hdr using 1 <;> first | rfl | simp [Pmoment]

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

lemma integrable_moment_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    Integrable (fun t => ‖t‖^n * ‖f t‖) (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn (fun t : ℝ => ‖t‖^n) (Icc a b) := by fun_prop
  exact IntegrableOn.continuousOn_mul hc hf.norm isCompact_Icc

end SharpPlanar

namespace SharpPlanar

lemma spectral_integrable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (s : ℝ) :
    Integrable (fun t => Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I)*f t) μ := by
  refine (hf.norm).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with t
    simp [Complex.norm_exp]

lemma spectral_hasDerivAt {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hm : Integrable (fun t => ‖t‖*‖f t‖) μ) (s : ℝ) :
    HasDerivAt (spectral μ f)
      (spectral μ (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) s) s := by
  have hf' : Integrable (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) μ := by
    refine (hm.const_mul Real.pi).mono' ?_ ?_
    · exact (((by fun_prop : Continuous (fun t : ℝ =>
          ((Real.pi*t : ℝ):ℂ)*Complex.I))).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · filter_upwards with t
      simp [abs_of_pos Real.pi_pos, mul_assoc]
  have he (t x : ℝ) : HasDerivAt (fun x : ℝ =>
      Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
      (Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
        (((Real.pi*t : ℝ):ℂ)*Complex.I*f t)) x := by
    convert ((((hasDerivAt_id x).const_mul (Real.pi*t)).ofReal_comp.mul_const
      Complex.I).cexp.mul_const (f t)) using 1 <;> first | rfl | (simp only [mul_one, id_eq]; ring)
  have hr := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun t => Real.pi*(‖t‖*‖f t‖))
    (F := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
    (F' := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
      (((Real.pi*t : ℝ):ℂ)*Complex.I*f t))
    (Filter.univ_mem) (Filter.Eventually.of_forall fun x => (spectral_integrable hf x).aestronglyMeasurable)
    (spectral_integrable hf s) (spectral_integrable hf' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t x _ => by
      simp [Complex.norm_exp, abs_of_pos Real.pi_pos, mul_assoc])
    (hm.const_mul Real.pi) (Filter.Eventually.of_forall fun t x _ => he t x)
  exact hr.2

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma interval_spectral_eq (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ t in a..b, f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f s := by
  unfold spectral
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [mul_comm (f t)]
  congr 1
  congr 1
  push_cast
  ring

lemma interval_exponential_hasDerivAt {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in a..b,
      f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in a..b, f t * (Complex.I*Real.pi*(t:ℂ)) *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
  have hfi : IntegrableOn f (Icc a b) volume := hf.integrableOn_Icc
  have hder := spectral_hasDerivAt hfi (by
    simpa only [pow_one] using integrable_moment_Icc hfi 1) s
  have hfun : (fun s : ℝ => ∫ t in a..b, f t*Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f :=
    funext (interval_spectral_eq f hab)
  rw [hfun]
  convert hder using 1
  all_goals try with_reducible_and_instances rfl
  rw [interval_spectral_eq _ hab]
  congr 1
  funext t
  push_cast
  ring

lemma basisMoment_hasDerivAt (sec : Bool) (n ell : ℕ) (s : ℝ) :
    HasDerivAt (basisMoment sec n ell) (basisMoment sec n (ell+1) s) s := by
  have hd (j : ℕ) : HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^(ell+1) *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
    convert interval_exponential_hasDerivAt (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
      (f:=fun t => (if sec then v n j t else u n j t)*(Complex.I*Real.pi*(t:ℂ))^ell)
      (by cases sec <;> apply Continuous.continuousOn <;>
        apply Continuous.mul <;> first | exact continuous_u n j | exact continuous_v n j | fun_prop) s using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext t
    rw [pow_succ]
    ring
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range 6) => hd j))

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma basisMoment_bound (sec : Bool) (n ell : ℕ) (s : ℝ) :
    |basisMoment sec n ell s| ≤ densityBound * Real.pi^ell := by
  have hj (j : ℕ) (hj : j < 6) :
      ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ densityBound*Real.pi^ell/6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun t => (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6) (C:=densityBound*Real.pi^ell) (fun t ht => ?_)
    · convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
      ring
    · rw [mul_assoc,norm_mul]
      apply mul_le_mul _ (realSpectral_norm_g ell (piece_interval_g hj (uIoc_subset_uIcc ht)) s)
        (norm_nonneg _) densityBound_nonneg
      cases sec
      · exact u_bound_g n j (piece_interval_g hj (uIoc_subset_uIcc ht))
      · exact v_bound' n j (piece_interval_g hj (uIoc_subset_uIcc ht))
  unfold basisMoment
  calc
    _ ≤ ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j ∈ Finset.range 6, ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 6, densityBound*Real.pi^ell/6 := by
      exact Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = _ := by simp <;> ring

lemma cardinalSeries_summand_bound (p : CardinalData) (ell : ℕ) (s : ℝ) (n : Node) :
    ‖p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s‖ ≤
      (densityBound*Real.pi^ell)*(|p.x (n,false)|+|p.x (n,true)|) := by
  calc
    _ ≤ ‖p.x (n,false)*basisMoment false n.val ell s‖ +
        ‖p.x (n,true)*basisMoment true n.val ell s‖ := norm_add_le _ _
    _ = |p.x (n,false)| * |basisMoment false n.val ell s| +
        |p.x (n,true)| * |basisMoment true n.val ell s| := by simp [norm_mul,Real.norm_eq_abs]
    _ ≤ |p.x (n,false)| * (densityBound*Real.pi^ell)+
        |p.x (n,true)| * (densityBound*Real.pi^ell) := by
      gcongr <;> apply basisMoment_bound
    _ = _ := by ring

lemma cardinalSeries_summable (p : CardinalData) (ell : ℕ) (s : ℝ) :
    Summable (fun n : Node => p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s) :=
  ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^ell)).of_norm_bounded
    (cardinalSeries_summand_bound p ell s)

lemma cardinalSeries_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (cardinalSeries p ell) (cardinalSeries p (ell+1) s) s := by
  have hsum := hasDerivAt_tsum
    ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^(ell+1)))
    (fun n y => ((basisMoment_hasDerivAt false n.val ell y).const_mul (p.x (n,false))).add
      ((basisMoment_hasDerivAt true n.val ell y).const_mul (p.x (n,true))))
    (fun n y => cardinalSeries_summand_bound p (ell+1) y n)
    (cardinalSeries_summable p ell 0) s
  exact ((((Pmoment_hasDerivAt ell s).const_mul p.C).add
    ((basisMoment_hasDerivAt false 0 ell s).const_mul p.c₀)).add
    ((basisMoment_hasDerivAt true 0 ell s).const_mul p.d₀)).add hsum


end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pieceL_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceL j t ≤ pieceL j s := by
  have he : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(t-s)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hh := mul_nonneg (mul_nonneg Real.pi_pos.le (dampingCap_pos_g ⟨j.val+1,by omega⟩).le) (sub_nonneg.mpr hst)
    nlinarith
  have hh:=pieceL_shift_bound j hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hh
  exact hh.trans (by nlinarith [pieceL_nonneg_g j hs])
lemma atomL_antitone (j : Fin 7) {s t : ℝ} (hst : s ≤ t) : atomL j t ≤ atomL j s := by
  unfold atomL
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_pos Real.pi_pos (dampingCap_pos_g j)]
  · exact mul_nonneg (by fin_cases j <;> norm_num [atomMass]) (lambdaCap_nonneg_g _)
lemma transformEnvelope_antitone (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    transformEnvelope ell t ≤ transformEnvelope ell s := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pieceL_antitone j hs hst)
    (densityCap_nonneg_g _)) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _)
lemma atomicEnvelope_antitone (ell : ℕ) {s t : ℝ} (hst : s ≤ t) :
    atomicEnvelope ell t ≤ atomicEnvelope ell s := by
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_right (atomL_antitone j hst)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg_g _)) _)
lemma direct_envelope_coarse (ell : ℕ) : directEnvelope ell ≤ 
    (∑ j : Fin 6,densityCap j/6)*Real.pi^ell := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀ (by positivity)
    have hj : (j.val:ℝ)+1 ≤ 6 := by exact_mod_cast (by omega : j.val+1 ≤ 6)
    nlinarith [Real.pi_pos]
  · exact div_nonneg (densityCap_nonneg_g _) (by norm_num)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_KernelDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped Topology
lemma kernelMoment_hasDerivAt (ell : ℕ) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => kernelMoment ell s t) (kernelMoment (ell+1) s t) s := by
  have hd := ((((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I*Real.pi*z t)).cexp).const_mul
    (lambda t*(Complex.I*Real.pi*z t)^ell))
  simpa only [kernelMoment,pow_succ,Complex.ofReal_one,id_eq,mul_one,one_mul,mul_assoc,
    mul_left_comm,mul_comm] using hd
lemma continuous_joint_kernel (ell : ℕ) :
    Continuous (fun st : ℝ×ℝ => kernelMoment ell st.1 st.2) := by
  unfold kernelMoment
  exact ((continuous_lambda.comp continuous_snd).mul
    ((continuous_const.mul (continuous_z.comp continuous_snd)).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (continuous_z.comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp continuous_fst)))
lemma piece_hasDerivAt (p : CardinalData) (ell j : ℕ) (hj : j<6) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * kernelMoment ell s t)
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * kernelMoment (ell+1) s t) s := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (fun st : ℝ×ℝ => kernelMoment (ell+1) st.1 st.2)
      (Set.Icc (s-1) (s+1) ×ˢ Set.Icc (0:ℝ) 1) from (continuous_joint_kernel _).continuousOn)
  have hr := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => density p j t * kernelMoment ell s t)
    (F' := fun s t => density p j t * kernelMoment (ell+1) s t)
    (s := Set.Icc (s-1) (s+1))
    (bound := fun _ => densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)*max C 0)
    (Icc_mem_nhds (by linarith : s-1 < s) (by linarith : s < s+1))
    (Filter.Eventually.of_forall fun x => (intervalIntegrable_iff.mp (piece_integrable p ell j hj x)).aestronglyMeasurable)
    (piece_integrable p ell j hj s)
    (intervalIntegrable_iff.mp (piece_integrable p (ell+1) j hj s)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => by
      rw [norm_mul]
      exact mul_le_mul (density_bound p j (piece_interval_g hj (Set.uIoc_subset_uIcc ht)))
        ((hC (x,t) ⟨hx,piece_interval_g hj (Set.uIoc_subset_uIcc ht)⟩).trans (le_max_left _ _))
        (norm_nonneg _) (by have := densityBound_nonneg; positivity))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => (kernelMoment_hasDerivAt ell t x).const_mul _)
  exact hr.2
lemma K_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (K p ell) (K p (ell+1) s) s := by
  have ha := ((kernelMoment_hasDerivAt ell 0 s).const_mul (Pcoeff 0)).add
    (HasDerivAt.fun_sum (u := Finset.Icc (1:ℕ) 6) fun j _ =>
      (kernelMoment_hasDerivAt ell ((j:ℝ)/6) s).const_mul (2*Pcoeff j))
  have hi := HasDerivAt.fun_sum (u := Finset.range 6) fun j hj =>
    piece_hasDerivAt p ell j (Finset.mem_range.mp hj) s
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((ha.const_mul (p.C:ℂ)).add hi)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma fullMoment_transformed (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a true m ell=K (tableData a) ell m/(ell.factorial:ℝ) :=
  tableMomentK_eq_g a m ell
lemma tableHJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (tableHJet a ell) (tableHJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_JetError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma exactJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (exactJet a ell) (exactJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TaylorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Set
lemma jet_iteratedDeriv {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) (ell : ℕ) :
    iteratedDeriv ell (J 0)=J ell := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    exact (hJ ell s).deriv
lemma jet_contDiff {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) : ContDiff ℝ (⊤ : ℕ∞) (J 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro ell _
  rw [jet_iteratedDeriv hJ]
  exact fun s => (hJ ell s).differentiableAt
lemma jetTaylor_at_zero (J : ℕ → ℝ → ℝ) (n : ℕ) (m : ℝ) : jetTaylor J n m 0=J 0 m := by
  unfold jetTaylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0; simp [zero_pow hb0]
  · simp
lemma jetTaylor_eq_within {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    {m u : ℝ} (hu : u≠0) (n : ℕ) :
    taylorWithinEval (J 0) n (uIcc m (m+u)) m (m+u)=jetTaylor J n m u := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by intro he; apply hu; linarith))
    ((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffAt (left_mem_uIcc),jet_iteratedDeriv hJ]
  simp only [add_sub_cancel_left,smul_eq_mul]
  ring

lemma jetTaylor_error {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (n : ℕ) (m u M : ℝ)
    (hM : ∀ s ∈ uIcc m (m+u), |J (n+1) s| ≤ M) :
    |J 0 (m+u)-jetTaylor J n m u| ≤ M*|u|^(n+1)/((n+1).factorial:ℝ) := by
  by_cases hu : u=0
  · subst u; simp [jetTaylor_at_zero]
  obtain ⟨s,hs,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := J 0) (n := n) (x₀ := m) (x := m+u) (by intro he; apply hu; linarith : m≠m+u)
    (((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : ((n+1):ℕ∞) ≤ ⊤))).contDiffOn)
  rw [jetTaylor_eq_within hJ hu,jet_iteratedDeriv hJ,add_sub_cancel_left] at he
  rw [he,abs_div,abs_mul,abs_pow,abs_of_pos (show 0 < ((n+1).factorial:ℝ) from Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2.le⟩)
    (pow_nonneg (abs_nonneg u) _)) (Nat.cast_nonneg _)
lemma jetPartial_error {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (q : ℕ) (m u M : ℝ)
    (hM : ∀ s ∈ uIcc m (m+u), |J q s| ≤ M) :
    |J 0 (m+u)-jetPartial J q m u| ≤ M*|u|^q/(q.factorial:ℝ) := by
  cases q with
  | zero => simpa [jetPartial] using hM (m+u) right_mem_uIcc
  | succ n => exact jetTaylor_error hJ n m u M hM
lemma jetPartial_split (T : ℕ → ℝ → ℝ) (ν d : ℕ) (m u : ℝ) :
    jetPartial T (ν+(d+1)) m u=jetPartial T ν m u+u^ν*deletedPolynomial T ν d m u := by
  unfold jetPartial deletedPolynomial
  rw [Finset.sum_range_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.add_comm ν r,pow_add]
  ring
lemma jetPartial_sub (J T : ℕ → ℝ → ℝ) (q : ℕ) (m u : ℝ) :
    jetPartial (fun ell s => J ell s-T ell s) q m u=
      jetPartial J q m u-jetPartial T q m u := by
  simp only [jetPartial,sub_div,sub_mul,Finset.sum_sub_distrib]

lemma deletedPolynomial_error {J T : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (hT : ∀ ell s, HasDerivAt (T ell) (T (ell+1) s) s)
    (ν d : ℕ) (m u E R : ℝ)
    (hj : ∀ k<ν, J k m=0)
    (hE : ∀ s ∈ uIcc m (m+u), |J ν s-T ν s|≤E)
    (hR : ∀ s ∈ uIcc m (m+u), |T (ν+(d+1)) s|≤R) :
    |J 0 (m+u)-u^ν*deletedPolynomial T ν d m u| ≤
      E*|u|^ν/(ν.factorial:ℝ)+R*|u|^(ν+(d+1))/((ν+(d+1)).factorial:ℝ) := by
  have hp : jetPartial J ν m u=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [hj k (Finset.mem_range.mp hk)]
  have hd := jetPartial_error (fun ell s => (hJ ell s).sub (hT ell s)) ν m u E hE
  have ht := jetPartial_error hT (ν+(d+1)) m u R hR
  change |J 0 (m+u)-T 0 (m+u)-jetPartial (fun ell s => J ell s-T ell s) ν m u| ≤ _ at hd
  rw [jetPartial_sub,hp,zero_sub] at hd
  rw [jetPartial_split] at ht
  calc
    _ = |((J 0 (m+u)-T 0 (m+u))- -jetPartial T ν m u)+
        (T 0 (m+u)-(jetPartial T ν m u+u^ν*deletedPolynomial T ν d m u))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hd ht)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfGapCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma normalizedH_eq (a : Bool) (m : ℝ) (ell : ℕ) :
    normalizedH a m ell=tableHJet a ell m/(ell.factorial:ℝ) := by
  rw [normalizedH,fullMoment_direct_g,fullMoment_transformed]
  exact (add_div _ _ _).symm
lemma sourcePower_sum (a : Bool) (m y v : ℝ) (nu d : ℕ) :
    (∑ r ∈ Finset.range (d+1), sourcePower a m y nu r*v^r)=
      (if a then 1 else -1)*deletedPolynomial (tableHJet a) nu d m (y*v) := by
  simp only [sourcePower,normalizedH_eq,deletedPolynomial,Finset.mul_sum,mul_pow]
  apply Finset.sum_congr rfl
  intro r hr
  ring
lemma sourcePower_lower {a : Bool} {m y v L : ℝ} {nu : ℕ}
    (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a m y nu) k.val) :
    L ≤ (if a then 1 else -1)*deletedPolynomial (tableHJet a) nu 28 m (y*v) := by
  rw [← sourcePower_sum]
  apply bernstein_lower hv
  intro k hk
  exact hB ⟨k,Finset.mem_range.mp hk⟩
lemma scaled_remainder_bound {x z Z E R f g : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ R) (hz : z ≤ Z) (hg : 0 ≤ g) :
    E*x/f+R*(x*z)/g ≤ x*(E/f+R*Z/g) := by
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (mul_nonneg hr hx)) hg
  calc
    _ = E*x/f+(R*x*z)/g := by ring
    _ ≤ E*x/f+(R*x*Z)/g := by linarith only [hh]
    _ = _ := by ring
lemma signed_error_lower (a : Bool) {J P x A B L : ℝ}
    (he : |J-x*P|≤x*(A+B)) (hl : x*L ≤ x*((if a then 1 else -1)*P)) :
    (L-A-B)*x ≤ (if a then 1 else -1)*J := by
  cases a <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hl ⊢ <;>
    nlinarith [(abs_le.mp he).1,(abs_le.mp he).2]

lemma halfGap_lower {a : Bool} {m y v Y E R L : ℝ} {nu : ℕ}
    (hv : v ∈ Set.Icc 0 1) (hu : |y*v| ≤ Y) (hpow : (y*v)^nu=|y*v|^nu)
    (hj : ∀ k<nu,exactJet a k m=0)
    (hE : ∀ s ∈ Set.uIcc m (m+y*v), |exactJet a nu s-tableHJet a nu s|≤E)
    (hR : ∀ s ∈ Set.uIcc m (m+y*v), |tableHJet a (nu+29) s|≤R)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a m y nu) k.val) :
    (L-E/(nu.factorial:ℝ)-R*Y^29/((nu+29).factorial:ℝ))*|y*v|^nu ≤
      (if a then 1 else -1)*exactJet a 0 (m+y*v) := by
  have herr := deletedPolynomial_error (exactJet_deriv a) (tableHJet_deriv a)
    nu 28 m (y*v) E R hj hE hR
  have hr0 : 0 ≤ R := (abs_nonneg _).trans (hR m Set.left_mem_uIcc)
  have hn0 : 0 ≤ |y*v|^nu := pow_nonneg (abs_nonneg _) _
  have hu29 : |y*v|^29 ≤ Y^29 := pow_le_pow_left₀ (abs_nonneg _) hu _
  have her := scaled_remainder_bound (E := E) (f := (nu.factorial:ℝ))
    (g := ((nu+29).factorial:ℝ)) hn0 hr0 hu29 (Nat.cast_nonneg _)
  rw [← pow_add] at her
  have hh : |exactJet a 0 (m+y*v)-(y*v)^nu*deletedPolynomial (tableHJet a) nu 28 m (y*v)| ≤
      |y*v|^nu*(E/(nu.factorial:ℝ)+R*Y^29/((nu+29).factorial:ℝ)) := herr.trans her
  have hl := mul_le_mul_of_nonneg_left (sourcePower_lower hv hB) hn0
  rw [hpow] at hh
  exact signed_error_lower a hh hl
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfGapAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfGap_absmul {y v : ℝ} (hv : v  ∈  Set.Icc 0 1) : |y*v| ≤ |y| := by
  rw [abs_mul,abs_of_nonneg hv.1]
  nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr hv.2)]
lemma halfGap_segment_lower {v m y s N : ℝ} (hv : v  ∈  Set.Icc 0 1)
    (hm : N ≤ m) (hy : N ≤ m+y) (hs : s ∈ Set.uIcc m (m+y*v)) : N ≤ s := by
  have he : N ≤ m+y*v := by
    nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hm)]
  exact (le_min hm he).trans hs.1
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pi_le_upper : Real.pi ≤ piUpper := pi_fine_g.2.le
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma table_constant_bound (a : Bool) : |(tableData a).C| ≤ (17:ℝ)/1000 := by
  cases a <;> norm_num [tableData,tableConstant]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma table_direct_bound (a : Bool) (ell : ℕ) (s : ℝ) :
    |cardinalSeries (tableData a) ell s| ≤ 80*Real.pi^ell := by
  apply (direct_spectral_bound_g _ _ _).trans
  have h0:=pow_nonneg Real.pi_pos.le ell
  have hd:=mul_le_mul_of_nonneg_left (direct_envelope_coarse ell)
    (show 0 ≤ |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ by positivity)
  have hm:=table_coeff_mass_g a
  have hc:=table_constant_bound a
  have hs : (∑ j : Fin 6,densityCap j/6)=(47321:ℝ)/1500 := by
    first | (simp [densityCap,densityNum,densityDen,Fin.sum_univ_succ]; all_goals first | (norm_num [densityCap,densityNum,densityDen,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [densityCap,densityNum,densityDen,Fin.sum_univ_succ]; done) | norm_num [densityCap,densityNum,densityDen,Fin.sum_univ_succ]
  rw [hs] at hd
  nlinarith [mul_le_mul_of_nonneg_right hc h0,mul_le_mul_of_nonneg_right hm.le h0]
lemma table_jet_envelope (a : Bool) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |tableHJet a ell t| ≤ 80*Real.pi^ell+(23:ℝ)/10*transformEnvelope ell s+
      (17:ℝ)/1000*atomicEnvelope ell s := by
  have hk:=sharp_moment_bound_g (tableData (!a)) ell (hs.trans hst)
  change |K (tableData (!a)) ell t| ≤ 
    (|(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖)*transformEnvelope ell t+
    |(tableData (!a)).C| *atomicEnvelope ell t at hk
  have h1:=mul_le_mul (show |(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖ ≤ (23:ℝ)/10 by linarith [table_coeff_mass_g (!a)])
    (transformEnvelope_antitone ell hs hst) (transformEnvelope_nonneg_g ell (hs.trans hst)) (by norm_num : (0:ℝ) ≤ 23/10)
  have h2:=mul_le_mul (table_constant_bound (!a)) (atomicEnvelope_antitone ell hst)
    (atomicEnvelope_nonneg_g ell t) (by norm_num : (0:ℝ) ≤ 17/1000)
  exact (abs_add_le _ _).trans (by linarith [table_direct_bound a ell t])
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma table_jet_rat (a : Bool) (ell n : ℕ) {s : ℝ} (hs : (n:ℝ) ≤ s) :
    |tableHJet a ell s| ≤ taylorEnvelope ell n := by
  apply (table_jet_envelope a ell (Nat.cast_nonneg n) hs).trans
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le pi_le_upper ell) (by norm_num))
    (mul_le_mul_of_nonneg_left (transformEnvelope_le_rat_g ell n) (by norm_num)))
    (mul_le_mul_of_nonneg_left (atomicEnvelope_le_rat_g ell n) (by norm_num))
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_SignBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar sign margins

Rational bounds for coefficient perturbations and Taylor remainders on half-gaps.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma taylor_cap0 : taylorEnvelope 29 0*(1/2:ℝ)^29/((29 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfGapTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma analytic_zero {v : ℝ} (hv : v  ∈  Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(37:ℝ)/50  ≤  powerToBernstein 28 (sourcePower true 0 (1/2) 0) k.val) :
    (7:ℝ)/10  ≤  exactJet true 0 (0+(1/2)*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 0 (0+(1/2)*v)) : 0 ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have he := halfGap_lower (a := true) (E := 4/1000) (R := taylorEnvelope 29 0)
    (Y := 1/2) hv (by simpa using halfGap_absmul (y := (1:ℝ)/2) hv)
    (by simp : ((1/2)*v)^0=|(1/2)*v|^0) (by omega : ∀ k<0,exactJet true k 0=0)
    (fun s hss => (error_zero_cap_g true (hs s hss)).le)
    (fun s hss => table_jet_rat true 29 0 (by simpa using hs s hss)) hB
  have hc:=taylor_cap0
  norm_num [Nat.factorial] at he hc
  simp only [zero_add]
  linarith
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_0_N1_right_g_oai {s : ℝ} (hs : s ∈ Set.Icc 0 (1/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-0)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (0:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  have hh:=analytic_zero hv (fun k => by have hh := (Bernstein0.N1_right.bound k).le; norm_num at hh ⊢; exact hh)
  rw [he] at hh
  simp only [ite_true, if_true,one_mul]
  linarith
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.halfSign_0_N1_right_g_oai := @OAI.SharpPlanar.halfSign_0_N1_right_g_oai

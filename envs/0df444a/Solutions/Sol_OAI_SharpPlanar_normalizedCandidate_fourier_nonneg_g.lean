-- Prove2me | solution 1 for OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:03:07.424895+00:00
-- url     : https://prove2.me/submissions/34b5f68a-d1e9-4176-b9d3-7c2de1b51e6a

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1652
import Definitions.Def_OAIQ098G1653
import Definitions.Def_OAIQ098G1675
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1688
import Definitions.Def_OAIQ098G1695
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein12_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein12_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein13_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein13_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein15_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein15_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein16_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein16_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein19_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein19_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein21_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein21_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein24_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein24_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein25_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein25_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein27_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein27_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein28_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein28_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein3_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein3_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein33_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein33_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein36_N1_left_ts_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein36_N1_right_ts_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein37_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein37_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein39_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein39_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein40_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein40_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein7_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein7_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein9_N1_left_bound_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein9_N1_right_bound_g
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_interpolation_exists_unique_g
import Theorems.Thm_OAI_SharpPlanar_Q_0_g
import Theorems.Thm_OAI_SharpPlanar_Q_1_g
import Theorems.Thm_OAI_SharpPlanar_Q_3_g
import Theorems.Thm_OAI_SharpPlanar_Q_4_g
import Theorems.Thm_OAI_SharpPlanar_Q_7_g
import Theorems.Thm_OAI_SharpPlanar_Q_9_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_X_norm_g
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g
import Theorems.Thm_OAI_SharpPlanar_bernsteinBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
import Theorems.Thm_OAI_SharpPlanar_direct_spectral_bound_g
import Theorems.Thm_OAI_SharpPlanar_error_large_cap_g
import Theorems.Thm_OAI_SharpPlanar_error_two_cap_g
import Theorems.Thm_OAI_SharpPlanar_exactLeft_origin_positive_g
import Theorems.Thm_OAI_SharpPlanar_exact_sign_tail_g
import Theorems.Thm_OAI_SharpPlanar_fullMoment_direct_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_halfSign_0_N1_right_g
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_normalizedCandidate_fourier_g
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
import Theorems.Thm_OAI_SharpPlanar_trig_table_g
import Theorems.Thm_OAI_SharpPlanar_u_bound_g
import Theorems.Thm_OAI_SharpPlanar_v_bound_g
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_g

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

theorem B_eq_inv_b_sq : B = (b ^ 2)⁻¹ := by rw [b_sq_g]; norm_num [B]

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


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_g]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

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

lemma weighted_exp_integral (c : ℂ) (hc : c ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((T : ℂ)-t)*Complex.exp (c*t)) =
      (Complex.exp (c*T)-1-c*T)/c^2 := by
  let F : ℝ → ℂ := fun t => (((T : ℂ)-t)*Complex.exp (c*t))/c +
      Complex.exp (c*t)/c^2
  have hd (t : ℝ) : HasDerivAt F (((T : ℂ)-t)*Complex.exp (c*t)) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (c*t))
        (Complex.exp (c*t)*c) t := by
      convert (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal).cexp using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    have ht : HasDerivAt (fun t : ℝ => (T : ℂ)-t) (-1) t := by
      convert ((hasDerivAt_id (t : ℂ)).const_sub (T : ℂ)).comp_ofReal using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    convert ((ht.mul he).div_const c).add (he.div_const (c^2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (field_simp [hc]; ring)
  have hi : IntervalIntegrable (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (c*t)) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp only [F, Complex.ofReal_zero, sub_self, zero_mul, mul_zero, Complex.exp_zero,
    sub_zero, zero_div]
  field_simp
  ring

lemma exponential_division_one (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1)/(U : ℂ) =
      Complex.I*Real.pi * ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 1; ring
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

lemma exponential_division_two (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1-Complex.I*Real.pi*T*U)/(U : ℂ)^2 =
      -(Real.pi : ℂ)^2 * ∫ t in (0 : ℝ)..T,
        ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => ((T : ℂ)-t)*Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 2; ring
  rw [he, weighted_exp_integral _ hc]
  have hh : Complex.I*Real.pi*(U : ℂ)*T = Complex.I*Real.pi*T*U := by ring
  rw [hh]
  field_simp
  simp [Complex.I_sq]
  ring

end SharpPlanar

namespace SharpPlanar

lemma triangular_piece_integrals (N : ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ l, Continuous (f l)) :
    (∑ j ∈ Finset.range N, ∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc 1 N, ∫ t in a 0..a l, f l t := by
  have ht (j : ℕ) : (∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    exact intervalIntegral.integral_finsetSum fun l _ => (hf l).intervalIntegrable _ _
  simp_rw [ht]
  have hswap := Finset.sum_Ico_Ico_comm' 0 (N+1)
    (fun j l => ∫ t in a j..a (j+1), f l t)
  have hi (j : ℕ) : Finset.Ico (j+1) (N+1) = Finset.Icc (j+1) N := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [Nat.Ico_zero_eq_range, hi] at hswap
  have hleft : (∑ j ∈ Finset.range (N+1),
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t) =
      ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    rw [Finset.sum_range_succ]
    simp
  rw [hleft] at hswap
  rw [hswap]
  have hadj (l : ℕ) : (∑ j ∈ Finset.range l, ∫ t in a j..a (j+1), f l t) =
      ∫ t in a 0..a l, f l t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hf l).intervalIntegrable _ _)
  simp_rw [hadj]
  symm
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro l hl hn
    have : l = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at *
      omega
    simp [this]

lemma u_integrand (n j : ℕ) (s t : ℝ) :
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold u
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

lemma v_integrand (n j : ℕ) (s t : ℝ) :
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold v
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (Complex.I*Real.pi*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

end SharpPlanar

namespace SharpPlanar

lemma P_as_table (s : ℝ) : P s =
    ∏ a ∈ residues,
      (2 - 2*(Real.cos (Real.pi*s/6)*cosTable a + Real.sin (Real.pi*s/6)*sinTable a)) := by
  unfold P
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2*(Real.pi*(s-a)/12) = Real.pi*s/6-Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table_g a (by have := residue_lt ha; omega)).1,
    (trig_table_g a (by have := residue_lt ha; omega)).2]

end SharpPlanar

namespace SharpPlanar

lemma phase_nat (j : ℕ) (s : ℝ) :
    Complex.exp (Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s) =
      ((Real.cos (Real.pi*s/6) : ℂ) + Real.sin (Real.pi*s/6)*Complex.I)^j := by
  rw [show Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s =
      (j : ℂ) * ((Real.pi*s/6 : ℝ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_ofReal_mul_I]

lemma polynomial_fourier_algebra (c d : ℝ) (hcd : c^2+d^2=1) :
    (∏ a ∈ residues, (2-2*(c*cosTable a+d*sinTable a))) =
    (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*((c : ℂ)+(d : ℂ)*Complex.I)^j).re := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  norm_num [residues, cosTable, sinTable, Finset.sum_Icc_succ_top, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  simp only [b_sq_g, b_pow_3, hd2, hd3, hd4, hd5, hd6]
  ring


theorem P_fourier (s : ℝ) :
    P s = (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re := by
  simp_rw [phase_nat]
  rw [P_as_table]
  exact polynomial_fourier_algebra _ _ (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)])

end SharpPlanar

namespace SharpPlanar

lemma Pmoment_zero (s : ℝ) : Pmoment 0 s = P s := by
  rw [P_fourier]
  simp [Pmoment]

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

lemma trig_nat_mod12 (n : ℕ) :
    Real.sin (Real.pi*n/6) = sinTable (n%12) ∧
    Real.cos (Real.pi*n/6) = cosTable (n%12) := by
  have hn : (n : ℝ) = (n%12 : ℕ) + 12*(n/12 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 12).symm
  have ha : Real.pi*n/6 = Real.pi*(n%12 : ℕ)/6 + (n/12 : ℕ)*(2*Real.pi) := by
    conv_lhs => rw [hn]
    ring
  rw [ha, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  exact trig_table_g (n%12) (by omega)

lemma Pmoment_mod (ell n : ℕ) : Pmoment ell n = Pmoment ell (n%12 : ℕ) := by
  unfold Pmoment
  simp only [phase_nat]
  rw [(trig_nat_mod12 n).1, (trig_nat_mod12 n).2,
    (trig_table_g (n%12) (by omega)).1, (trig_table_g (n%12) (by omega)).2]


lemma phase_node (j n : ℕ) :
    Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ)) =
      (cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I := by
  rw [show Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ) =
      ((Real.pi*(j*n : ℕ)/6 : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, (trig_nat_mod12 (j*n)).1, (trig_nat_mod12 (j*n)).2]

lemma Pmoment_node_formula (ell n : ℕ) :
    Pmoment ell n =
      (Pcoeff 0*(0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
        2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
          ((cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I)).re := by
  unfold Pmoment
  simp_rw [phase_node]

lemma Pmoment_node_0 :
    Pmoment 0 (0 : ℕ) = 0 ∧ Pmoment 1 (0 : ℕ) = 0 ∧
      Pmoment 2 (0 : ℕ) = 2*Q 0 ∧ Pmoment 3 (0 : ℕ) = 6*Q 0*D 0 := by
  rw [Q_0_g, D_0_g, Pmoment_node_formula 0 0, Pmoment_node_formula 1 0,
    Pmoment_node_formula 2 0, Pmoment_node_formula 3 0]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf

lemma Pmoment_node_1 :
    Pmoment 0 (1 : ℕ) = 0 ∧ Pmoment 1 (1 : ℕ) = 0 ∧
      Pmoment 2 (1 : ℕ) = 2*Q 1 ∧ Pmoment 3 (1 : ℕ) = 6*Q 1*D 1 := by
  rw [Q_1_g, D_1_g, Pmoment_node_formula 0 1, Pmoment_node_formula 1 1,
    Pmoment_node_formula 2 1, Pmoment_node_formula 3 1]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_3 :
    Pmoment 0 (3 : ℕ) = 0 ∧ Pmoment 1 (3 : ℕ) = 0 ∧
      Pmoment 2 (3 : ℕ) = 2*Q 3 ∧ Pmoment 3 (3 : ℕ) = 6*Q 3*D 3 := by
  rw [Q_3_g, D_3_g, Pmoment_node_formula 0 3, Pmoment_node_formula 1 3,
    Pmoment_node_formula 2 3, Pmoment_node_formula 3 3]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_4 :
    Pmoment 0 (4 : ℕ) = 0 ∧ Pmoment 1 (4 : ℕ) = 0 ∧
      Pmoment 2 (4 : ℕ) = 2*Q 4 ∧ Pmoment 3 (4 : ℕ) = 6*Q 4*D 4 := by
  rw [Q_4_g, D_4_g, Pmoment_node_formula 0 4, Pmoment_node_formula 1 4,
    Pmoment_node_formula 2 4, Pmoment_node_formula 3 4]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_7 :
    Pmoment 0 (7 : ℕ) = 0 ∧ Pmoment 1 (7 : ℕ) = 0 ∧
      Pmoment 2 (7 : ℕ) = 2*Q 7 ∧ Pmoment 3 (7 : ℕ) = 6*Q 7*D 7 := by
  rw [Q_7_g, D_7_g, Pmoment_node_formula 0 7, Pmoment_node_formula 1 7,
    Pmoment_node_formula 2 7, Pmoment_node_formula 3 7]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_9 :
    Pmoment 0 (9 : ℕ) = 0 ∧ Pmoment 1 (9 : ℕ) = 0 ∧
      Pmoment 2 (9 : ℕ) = 2*Q 9 ∧ Pmoment 3 (9 : ℕ) = 6*Q 9*D 9 := by
  rw [Q_9_g, D_9_g, Pmoment_node_formula 0 9, Pmoment_node_formula 1 9,
    Pmoment_node_formula 2 9, Pmoment_node_formula 3 9]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring


theorem Pmoment_node_data (n : ℕ) (hn : n%12 ∈ residues) :
    Pmoment 0 n = 0 ∧ Pmoment 1 n = 0 ∧
      Pmoment 2 n = 2*Q n ∧ Pmoment 3 n = 6*Q n*D n := by
  rw [Pmoment_mod 0 n, Pmoment_mod 1 n, Pmoment_mod 2 n, Pmoment_mod 3 n,
    ← Q_mod n, ← D_mod n]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;> rw [hn]
  · exact Pmoment_node_0
  · exact Pmoment_node_1
  · exact Pmoment_node_3
  · exact Pmoment_node_4
  · exact Pmoment_node_7
  · exact Pmoment_node_9

end SharpPlanar

namespace SharpPlanar

lemma foldedU_unfold (n : ℕ) (s : ℝ) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedU
  simp_rw [u_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))) (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedV_unfold (n : ℕ) (s : ℝ) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedV
  simp_rw [v_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))))
      (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedU_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2)).re := by
  rw [foldedU_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_two (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

lemma foldedV_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ))).re := by
  rw [foldedV_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_one (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he, intervalIntegral.integral_const_mul]


lemma exp_phase_split (T s v : ℝ) :
    Complex.exp (Complex.I*Real.pi*T*v)*
      Complex.exp (Complex.I*Real.pi*T*(s-v)) =
        Complex.exp (Complex.I*Real.pi*T*s) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma foldedU_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = (P s-P n-Pmoment 1 n*(s-n))/(s-n)^2 := by
  rw [foldedU_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)-
        (2*Pcoeff l*(Complex.I*Real.pi*((l:ℝ)/6:ℝ))*
          Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))*(s-n : ℝ))/(s-n : ℝ)^2 := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)-
          (2*Pcoeff l*(Complex.I*Real.pi*(l/6 : ℝ))*
            Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n))*(s-n : ℝ) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [P_fourier s, P_fourier n]
  simp [Pmoment, Complex.mul_re]

lemma foldedV_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedV n s = (P s-P n)/(s-n) := by
  rw [foldedV_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ)) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))/(s-n : ℝ) := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, P_fourier s, P_fourier n]
  simp [Complex.mul_re]

lemma folded_basis_quotients (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = P s/(s-n)^2 ∧ foldedV n s = P s/(s-n) := by
  obtain ⟨h0,h1,-,-⟩ := Pmoment_node_data n hn
  rw [Pmoment_zero] at h0
  rw [foldedU_quotient n s hs, foldedV_quotient n s hs, h0, h1]
  simp

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

lemma fourierIntegral_temperate {μ : Measure ℝ} (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  refine ⟨VectorFourier.contDiff_fourierIntegral L (fun n _ => hm n), fun n => ?_⟩
  refine ⟨0, ∫ t, ‖VectorFourier.fourierPowSMulRight L f t n‖ ∂μ, fun s => ?_⟩
  rw [VectorFourier.iteratedFDeriv_fourierIntegral L
    (N := (⊤ : ℕ∞)) (fun n _ => hm n) hf.aestronglyMeasurable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  simpa only [pow_zero, mul_one] using
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 μ L.toLinearMap₁₂
      (fun t => VectorFourier.fourierPowSMulRight L f t n) s

lemma spectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) : spectral μ f =
    VectorFourier.fourierIntegral 𝐞 μ spectralForm.toLinearMap₁₂ f := by
  funext s
  unfold spectral VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with t
  have hL : spectralForm.toLinearMap₁₂ t s = (-1/2 : ℝ)*t*s := by
    change (-1/2 : ℝ)*(t*s) = _
    ring
  rw [hL]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

lemma spectral_temperate {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (spectral μ f) := by
  rw [spectral_eq]
  exact fourierIntegral_temperate spectralForm hf hm

lemma integrable_moment_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    Integrable (fun t => ‖t‖^n * ‖f t‖) (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn (fun t : ℝ => ‖t‖^n) (Icc a b) := by fun_prop
  exact IntegrableOn.continuousOn_mul hc hf.norm isCompact_Icc

lemma spectral_Icc_temperate {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) :
    Function.HasTemperateGrowth (spectral (volume.restrict (Icc a b)) f) :=
  spectral_temperate hf (integrable_moment_Icc hf)

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

lemma basisMoment_zero (sec : Bool) (n : ℕ) : basisMoment sec n 0 =
    if sec then foldedV n else foldedU n := by
  cases sec <;> funext s <;> simp [basisMoment,foldedU,foldedV]

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

lemma basisU_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)^2*basisMoment false n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [Bool.false_eq_true,ite_false, if_false]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).1]
    field_simp

lemma basisV_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)*basisMoment true n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [ite_true, if_true]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).2]
    field_simp


lemma P_hasDerivAt (s : ℝ) : HasDerivAt P (Pmoment 1 s) s := by
  simpa only [show Pmoment 0 = P from funext Pmoment_zero] using Pmoment_hasDerivAt 0 s

lemma basisU_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*(s-n)*basisMoment false n 0 s + (s-n)^2*basisMoment false n 1 s = Pmoment 1 s := by
  have hd := (((hasDerivAt_id s).sub_const (n:ℝ)).pow 2).mul
    (basisMoment_hasDerivAt false n 0 s)
  have heq : (fun s : ℝ => (s-n)^2*basisMoment false n 0 s) = P :=
    funext (basisU_factor n hn)
  simp only [Pi.mul_def, Pi.pow_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisU_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment false n 0 s + 4*(s-n)*basisMoment false n 1 s +
      (s-n)^2*basisMoment false n 2 s = Pmoment 2 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := ((hl.const_mul 2).mul (basisMoment_hasDerivAt false n 0 s)).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 1 s))
  have heq : (fun s : ℝ => 2*(s-n)*basisMoment false n 0 s +
      (s-n)^2*basisMoment false n 1 s) = Pmoment 1 := funext (basisU_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisU_factor_deriv3 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    6*basisMoment false n 1 s + 6*(s-n)*basisMoment false n 2 s +
      (s-n)^2*basisMoment false n 3 s = Pmoment 3 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := (((basisMoment_hasDerivAt false n 0 s).const_mul 2).add
    ((hl.const_mul 4).mul (basisMoment_hasDerivAt false n 1 s))).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 2 s))
  have heq : (fun s : ℝ => 2*basisMoment false n 0 s +
      4*(s-n)*basisMoment false n 1 s+(s-n)^2*basisMoment false n 2 s) = Pmoment 2 :=
    funext (basisU_factor_deriv2 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 2 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisV_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    basisMoment true n 0 s + (s-n)*basisMoment true n 1 s = Pmoment 1 s := by
  have hd := ((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 0 s)
  have heq : (fun s : ℝ => (s-n)*basisMoment true n 0 s) = P :=
    funext (basisV_factor n hn)
  simp only [Pi.mul_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisV_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment true n 1 s + (s-n)*basisMoment true n 2 s = Pmoment 2 s := by
  have hd := (basisMoment_hasDerivAt true n 0 s).add
    (((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 1 s))
  have heq : (fun s : ℝ => basisMoment true n 0 s +
      (s-n)*basisMoment true n 1 s) = Pmoment 1 := funext (basisV_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)


theorem basis_diagonal_jets (n : ℕ) (hn : n%12 ∈ residues) :
    basisMoment false n 0 n = Q n ∧ basisMoment false n 1 n = Q n*D n ∧
    basisMoment true n 0 n = 0 ∧ basisMoment true n 1 n = Q n := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data n hn
  have hu0 := basisU_factor_deriv2 n hn n
  have hu1 := basisU_factor_deriv3 n hn n
  have hv0 := basisV_factor_deriv1 n hn n
  have hv1 := basisV_factor_deriv2 n hn n
  simp only [sub_self,zero_mul,zero_pow (by omega : 2 ≠ 0),add_zero] at hu0 hu1 hv0 hv1
  rw [h1] at hv0
  exact ⟨by linarith,by linarith,hv0,by linarith⟩


theorem basis_off_diagonal_jets (n m : ℕ) (hn : n%12 ∈ residues)
    (hm : m%12 ∈ residues) (hnm : m ≠ n) :
    basisMoment false n 0 m = 0 ∧ basisMoment false n 1 m = 0 ∧
    basisMoment true n 0 m = 0 ∧ basisMoment true n 1 m = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data m hm
  rw [Pmoment_zero] at h0
  have hsub : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hu0 := basisU_factor n hn m
  have hv0 := basisV_factor n hn m
  rw [h0] at hu0 hv0
  have hu : basisMoment false n 0 m = 0 := (mul_eq_zero.mp hu0).resolve_left (pow_ne_zero 2 hsub)
  have hv : basisMoment true n 0 m = 0 := (mul_eq_zero.mp hv0).resolve_left hsub
  have hu1 := basisU_factor_deriv1 n hn m
  have hv1 := basisV_factor_deriv1 n hn m
  rw [hu,h1,mul_zero,zero_add] at hu1
  rw [hv,h1,zero_add] at hv1
  exact ⟨hu,(mul_eq_zero.mp hu1).resolve_left (pow_ne_zero 2 hsub),
    hv,(mul_eq_zero.mp hv1).resolve_left hsub⟩

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


lemma cardinalSeries_jets (p : CardinalData) (m : Node) :
    cardinalSeries p 0 m.val = Q m.val * p.x (m,false) ∧
    cardinalSeries p 1 m.val = Q m.val * (D m.val*p.x (m,false)+p.x (m,true)) := by
  obtain ⟨hP0,hP1,-,-⟩ := Pmoment_node_data m.val m.property.2
  obtain ⟨hU0,hU1,hV0,hV1⟩ := basis_diagonal_jets m.val m.property.2
  have hm : m.val ≠ 0 := Nat.ne_of_gt m.property.1
  have hz : 0%12 ∈ residues := by norm_num [residues]
  obtain ⟨hc0,hc1,hd0,hd1⟩ := basis_off_diagonal_jets 0 m.val hz m.property.2 hm
  have hother (n : Node) (hn : n ≠ m) :
      basisMoment false n.val 0 m.val = 0 ∧ basisMoment false n.val 1 m.val = 0 ∧
      basisMoment true n.val 0 m.val = 0 ∧ basisMoment true n.val 1 m.val = 0 := by
    apply basis_off_diagonal_jets n.val m.val n.property.2 m.property.2
    intro he
    exact hn (Subtype.ext he.symm)
  have hs0 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 0 m.val +
      p.x (n,true)*basisMoment true n.val 0 m.val)) = p.x (m,false)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU0,hV0]; ring
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h0,h2]
  have hs1 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 1 m.val +
      p.x (n,true)*basisMoment true n.val 1 m.val)) =
      p.x (m,false)*(Q m.val*D m.val)+p.x (m,true)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU1,hV1]
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h1,h3]
  constructor
  · simp only [cardinalSeries,hP0,hc0,hd0,hs0,mul_zero,zero_add]
    ring
  · simp only [cardinalSeries,hP1,hc1,hd1,hs1,mul_zero,zero_add]
    ring

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

lemma expCut_eq (c x : ℝ) (hx : 0 ≤ x) : expCut c x = Real.exp (-c*x) := by
  simp [expCut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := by
  change expCut c (‖x‖^2) = _
  exact expCut_eq c _ (sq_nonneg _)

end SharpPlanar


open scoped SchwartzMap

namespace SharpPlanar

lemma spectral_dirac_eq (t : ℝ) (c : ℂ) (s : ℝ) :
    spectral (Measure.dirac t) (fun _ => c) s =
      Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * c := by
  simp [spectral]

lemma spectral_dirac_temperate (t : ℝ) (c : ℂ) :
    Function.HasTemperateGrowth (spectral (Measure.dirac t) (fun _ => c)) := by
  apply spectral_temperate
  · exact integrable_dirac (by finiteness)
  · intro n
    exact integrable_dirac (by finiteness)


lemma cardinal_temperate (p : CardinalData) :
    Function.HasTemperateGrowth (cardinal p) := by
  have h₀ := spectral_dirac_temperate 0 ((p.C : ℂ)*Pcoeff 0)
  have h₁ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) := by
    exact Function.HasTemperateGrowth.sum fun j _ => spectral_dirac_temperate _ _
  have h₂ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s) := by
    apply Function.HasTemperateGrowth.sum
    intro j hj
    apply spectral_Icc_temperate
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply (continuousOn_density_g p j).mono
    intro t ht
    have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hj0 : (0 : ℝ) ≤ j := by positivity
    constructor <;> linarith [ht.1, ht.2]
  exact Complex.reCLM.hasTemperateGrowth.comp ((h₀.add h₁).add h₂)


lemma radiusCoord_temperate :
    Function.HasTemperateGrowth (fun x : Plane => b*‖x‖^2) := by
  fun_prop

lemma qSchwartz_apply (p : CardinalData) (x : Plane) :
    qSchwartz p x = Real.exp (-Real.pi*h*(b*‖x‖^2)) * cardinal p (b*‖x‖^2) := by
  have hq : Function.HasTemperateGrowth (fun x : Plane => cardinal p (b*‖x‖^2)) :=
    (cardinal_temperate p).comp radiusCoord_temperate
  rw [qSchwartz, SchwartzMap.smulLeftCLM_apply_apply hq, gaussianSchwartz_apply]
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma spectral_interval_direct (p : CardinalData) (j : ℕ) (s : ℝ) :
    spectral (volume.restrict (Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j) s =
    ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel 0 s t := by
  rw [spectral,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directKernel,pow_zero,one_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

lemma cardinal_eq_cardinalSeries (p : CardinalData) (s : ℝ) :
    cardinal p s = cardinalSeries p 0 s := by
  unfold cardinal
  simp_rw [spectral_dirac_eq,spectral_interval_direct]
  have hat : (Complex.exp (((Real.pi*0*s:ℝ):ℂ)*Complex.I)*((p.C:ℂ)*Pcoeff 0) +
      ∑ j ∈ Finset.Icc (1:ℕ) 6,
        Complex.exp (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I)*(2*(p.C:ℂ)*Pcoeff j)) =
      (p.C:ℂ)*(Pcoeff 0 + ∑ j ∈ Finset.Icc (1:ℕ) 6,
        2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*s)) := by
    simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I) =
        Complex.I*Real.pi*((j:ℝ)/6)*s := by push_cast <;> ring
    rw [he]
    ring
  rw [hat,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series_g]
  simp only [cardinalSeries,Pmoment,pow_zero,mul_one]
  push_cast
  ring

lemma cardinal_hasDerivAt (p : CardinalData) (s : ℝ) :
    HasDerivAt (cardinal p) (cardinalSeries p 1 s) s := by
  simpa only [funext (cardinal_eq_cardinalSeries p)] using cardinalSeries_hasDerivAt p 0 s

lemma cardinal_jets (p : CardinalData) (m : Node) :
    cardinal p m.val = Q m.val*p.x (m,false) ∧
      deriv (cardinal p) m.val = Q m.val*(p.x (m,true)+D m.val*p.x (m,false)) := by
  rcases cardinalSeries_jets p m with ⟨h0,h1⟩
  rw [cardinal_eq_cardinalSeries,h0,(cardinal_hasDerivAt p m.val).deriv]
  exact ⟨rfl,by simpa only [add_comm] using h1⟩

end SharpPlanar

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein36
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

namespace SharpPlanar.Bernstein36
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (1/2) 2) k.val := by
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
namespace N1_left
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains_g ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower true 36 (-3/2) 2) k.val := by
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
end N1_left
end SharpPlanar.Bernstein36

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoupledFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coupled interpolation system

The finite inverse and tail estimates solve the interpolation equations in the space of absolutely summable coefficients.
-/

namespace SharpPlanar
open Numerical

lemma interpolationInverse_eq (neg : Bool) (r : X) :
    interpolationInverse neg r - signedS neg (interpolationInverse neg r) = r :=
  (Classical.choose_spec (interpolation_exists_unique_g neg r)).1
lemma coupled_equations (g₁ g₂ : X) :
    coupledLeft g₁ g₂-S (coupledRight g₁ g₂)=g₁ ∧
    coupledRight g₁ g₂-S (coupledLeft g₁ g₂)=g₂ := by
  have hp := interpolationInverse_eq false (g₁+g₂)
  have hm := interpolationInverse_eq true (g₁-g₂)
  change interpolationInverse false (g₁+g₂)-S (interpolationInverse false (g₁+g₂))=g₁+g₂ at hp
  change interpolationInverse true (g₁-g₂)- -S (interpolationInverse true (g₁-g₂))=g₁-g₂ at hm
  constructor <;> (apply lp.ext; funext ni)
  all_goals
    have hp' := congrArg (fun x : X => x ni) hp
    have hm' := congrArg (fun x : X => x ni) hm
    simp only [coupledLeft,coupledRight,map_smul,map_add,map_sub,lp.coeFn_sub,lp.coeFn_add,
      lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,lp.coeFn_neg,Pi.neg_apply] at *
    linarith
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
lemma density_split (p : CardinalData) (j : ℕ) (t : ℝ) :
    density p j t = density (fixedPart p) j t+density (positiveData p.x) j t := by
  simp only [density,fixedPart,positiveData,lp.coeFn_zero,Pi.zero_apply,
    Complex.ofReal_zero,zero_mul,zero_add,tsum_zero,add_zero]
lemma K_split (p : CardinalData) (ell : ℕ) (s : ℝ) :
    K p ell s = K (fixedPart p) ell s+K (positiveData p.x) ell s := by
  have hp (j : ℕ) (hj : j<6) :
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t*kernelMoment ell s t) =
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (fixedPart p) j t*kernelMoment ell s t)+
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t*kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_split,add_mul]
  unfold K
  simp only [fixedPart,positiveData,Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Complex.add_re,add_assoc,← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)
lemma K_fixed₁ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₁ x) ell s=K (fixed₁ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma K_fixed₂ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₂ x) ell s=K (fixed₂ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma transformedJets_fixed₁ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₁ x) ni=transformedJets (fixed₁ 0) ni + S x ni := by
  change _=transformedJets (fixed₁ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₁ x 0 _,K_fixed₁ x 1 _]; ring
  · rw [K_fixed₁ x 0 _]; ring
lemma transformedJets_fixed₂ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₂ x) ni=transformedJets (fixed₂ 0) ni + S x ni := by
  change _=transformedJets (fixed₂ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₂ x 0 _,K_fixed₂ x 1 _]; ring
  · rw [K_fixed₂ x 0 _]; ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FixedRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact contact interpolation solution

The inverse interpolation operator determines the coefficient lists for the prescribed contacts.
-/

namespace SharpPlanar
lemma exactLists_equations : exactList₁-S exactList₂=g₁ ∧ exactList₂-S exactList₁=g₂ :=
  coupled_equations g₁ g₂
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
lemma H₁_hasDerivAt (s : ℝ) :
    HasDerivAt H₁ (cardinalSeries exactData₁ 1 s+K exactData₂ 1 s) s :=
  (cardinal_hasDerivAt exactData₁ s).add (K_hasDerivAt exactData₂ 0 s)
lemma H₂_hasDerivAt (s : ℝ) :
    HasDerivAt H₂ (cardinalSeries exactData₂ 1 s+K exactData₁ 1 s) s :=
  (cardinal_hasDerivAt exactData₂ s).add (K_hasDerivAt exactData₁ 0 s)
lemma exactLists_coordinate (ni : Node×Bool) :
    exactList₁ ni=transformedJets exactData₂ ni-contactList ni ∧
    exactList₂ ni=transformedJets exactData₁ ni := by
  have h1 := congrArg (fun x : X => x ni) exactLists_equations.1
  have h2 := congrArg (fun x : X => x ni) exactLists_equations.2
  simp only [g₁,g₂,lp.coeFn_sub,Pi.sub_apply] at h1 h2
  change exactList₁ ni-S exactList₂ ni=transformedJets (fixed₂ 0) ni-contactList ni at h1
  change exactList₂ ni-S exactList₁ ni=transformedJets (fixed₁ 0) ni at h2
  simp only [exactData₁,exactData₂]
  rw [transformedJets_fixed₁ exactList₁ ni,transformedJets_fixed₂ exactList₂ ni]
  constructor <;> linarith
lemma contactList_apply (n : Node) (d : Bool) :
    contactList (n,d)=if n.val=1 ∧ d=true then 1 else 0 := by
  classical
  unfold contactList columnVector
  rw [lp.single_apply]
  by_cases hn : n.val=1
  · have he : n=firstNode := Subtype.ext hn
    subst n
    cases d <;> simp [firstNode]
  · have he : n≠firstNode := by intro hh; exact hn (congrArg Subtype.val hh)
    simp [hn,he]
lemma H₁_jets (n : Node) : H₁ n.val=0 ∧ deriv H₁ n.val=if n.val=1 then -Q n.val else 0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).1
  have hd := (exactLists_coordinate (n,true)).1
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,contactList_apply,
    and_false,and_true] at hc hd
  have hv := (cardinal_jets exactData₁ n).1
  have hj := (cardinal_jets exactData₁ n).2
  change cardinal exactData₁ n.val=Q n.val*exactList₁ (n,false) at hv
  change deriv (cardinal exactData₁) n.val=
    Q n.val*(exactList₁ (n,true)+D n.val*exactList₁ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₁ _).deriv] at hj
  constructor
  · unfold H₁; rw [hv,hc]; field_simp <;> ring
  · rw [(H₁_hasDerivAt _).deriv,hj,hc,hd]
    split <;> field_simp <;> ring
lemma H₂_jets (n : Node) : H₂ n.val=0 ∧ deriv H₂ n.val=0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).2
  have hd := (exactLists_coordinate (n,true)).2
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hc hd
  have hv := (cardinal_jets exactData₂ n).1
  have hj := (cardinal_jets exactData₂ n).2
  change cardinal exactData₂ n.val=Q n.val*exactList₂ (n,false) at hv
  change deriv (cardinal exactData₂) n.val=
    Q n.val*(exactList₂ (n,true)+D n.val*exactList₂ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₂ _).deriv] at hj
  constructor
  · unfold H₂; rw [hv,hc]; field_simp <;> ring
  · rw [(H₂_hasDerivAt _).deriv,hj,hc,hd]
    field_simp <;> ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FourierPairSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

open scoped FourierTransform RealInnerProductSpace

namespace SharpPlanar


lemma gaussianCoeff_re (t : ℝ) : (gaussianCoeff t).re = Real.pi*b*h := by
  simp [gaussianCoeff]

lemma gaussianCoeff_re_pos (t : ℝ) : 0 < (gaussianCoeff t).re := by
  rw [gaussianCoeff_re]
  exact mul_pos (mul_pos Real.pi_pos b_pos_g) h_pos_g

lemma spectralGaussian_norm (t : ℝ) (x : Plane) :
    ‖spectralGaussian t x‖ = Real.exp (-Real.pi*b*h*‖x‖^2) := by
  rw [spectralGaussian, Complex.norm_exp]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, gaussianCoeff_re]
  congr 1
  ring

lemma spectralGaussian_continuous : Continuous (fun q : Plane × ℝ => spectralGaussian q.2 q.1) := by
  unfold spectralGaussian gaussianCoeff
  fun_prop

lemma poisson_gaussian_plane {a : ℂ} (ha : 0 < a.re) (ξ : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-a * (‖x‖ : ℂ)^2)) ξ =
      (Real.pi : ℂ)/a * Complex.exp (-(Real.pi : ℂ)^2 * (‖ξ‖ : ℂ)^2/a) := by
  simpa [Plane, finrank_euclideanSpace_fin] using fourier_gaussian_innerProductSpace ha ξ

lemma gaussianCoeff_ne (t : ℝ) : gaussianCoeff t ≠ 0 := by
  intro he
  have := gaussianCoeff_re_pos t
  simp [he] at this

lemma gaussianCoeff_lambda (t : ℝ) : (Real.pi : ℂ)/gaussianCoeff t = lambda t := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  have ht := denominator_ne t
  apply (div_eq_iff (gaussianCoeff_ne t)).mpr
  unfold gaussianCoeff lambda
  field_simp [mul_ne_zero hb ht, ht, hb]
  ring_nf
  simp [Complex.I_sq]

lemma z_lambda_relation (t : ℝ) : Complex.I*z t - h = -lambda t/b := by
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  have ht := denominator_ne t
  have hbB : (b : ℂ)^2*(B : ℂ) = 1 := by
    rw [B_eq_inv_b_sq]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero 2 hb)
  unfold z lambda
  field_simp [ht, hb, mul_ne_zero hb ht]
  ring_nf
  simp only [Complex.I_sq]
  linear_combination (norm := skip) -Complex.I * hbB
  ring_nf
  simp

lemma gaussianCoeff_exponent (t r : ℝ) :
    -(Real.pi : ℂ)^2 * (r : ℂ)^2 / gaussianCoeff t =
      -(Real.pi : ℂ)*h*(b*r^2) + Complex.I*Real.pi*z t*(b*r^2) := by
  have hlam := gaussianCoeff_lambda t
  have hz := z_lambda_relation t
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  calc
    _ = -(Real.pi : ℂ) * (r : ℂ)^2 * lambda t := by rw [← hlam]; ring
    _ = ((Complex.I*z t - h)*b)*Real.pi*r^2 := by rw [hz]; field_simp
    _ = _ := by ring

lemma spectralGaussian_fourier (t : ℝ) (ξ : Plane) :
    𝓕 (spectralGaussian t) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        kernelMoment 0 (b*‖ξ‖^2) t := by
  change 𝓕 (fun x : Plane => Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)) ξ = _
  rw [poisson_gaussian_plane (gaussianCoeff_re_pos t), gaussianCoeff_lambda,
    gaussianCoeff_exponent]
  unfold kernelMoment
  simp only [pow_zero, mul_one]
  rw [Complex.ofReal_exp, Complex.exp_add]
  push_cast
  ring

lemma spectralGaussian_integrable (t : ℝ) : Integrable (spectralGaussian t) := by
  convert GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (gaussianCoeff_re_pos t) 0 (0 : Plane) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [spectralGaussian, neg_mul]

lemma gaussian_damping_integrable :
    Integrable (fun x : Plane => Real.exp (-Real.pi*b*h*‖x‖^2)) := by
  simpa only [spectralGaussian_norm] using (spectralGaussian_integrable 0).norm

lemma spectralGaussian_joint_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    Integrable (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2)
      (volume.prod μ) := by
  have hc : Continuous (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1) := by
    apply Continuous.mul
    · fun_prop
    · exact spectralGaussian_continuous
  apply (gaussian_damping_integrable.mul_prod hf.norm).mono'
    (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
  apply Filter.Eventually.of_forall
  intro q
  change ‖(Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2‖ ≤ _
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, spectralGaussian_norm]


lemma spectralGaussian_fourier_integral {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (fun x : Plane => ∫ t, spectralGaussian t x * f t ∂μ) ξ =
      ∫ t, 𝓕 (spectralGaussian t) ξ * f t ∂μ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hj : Integrable (Function.uncurry (fun x : Plane => fun t : ℝ =>
      (Real.fourierChar (-inner ℝ x ξ) : ℂ) * (spectralGaussian t x * f t)))
      (volume.prod μ) := by
    convert spectralGaussian_joint_integrable hf ξ using 1
    all_goals try with_reducible_and_instances rfl
    ext q
    rcases q with ⟨x, t⟩
    change _ * (_ * _) = _ * _ * _
    ring
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  ring

end SharpPlanar

namespace SharpPlanar



lemma fourier_integrable {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane => (Real.fourierChar (-inner ℝ x ξ) : ℂ) * g x) := by
  simpa only [Circle.smul_def, smul_eq_mul] using
    (Real.fourierIntegral_convergent_iff ξ).mpr hg

lemma fourier_conj_even {g : Plane → ℂ} (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => conj (g x)) ξ = conj (𝓕 g ξ) := by
  simp only [Real.fourier_eq', smul_eq_mul]
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun x : Plane =>
    conj (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_left, he, map_mul]
  congr 1
  simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma complex_re_as_sum (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  apply Complex.ext <;> simp

lemma fourier_integrable_exp {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane =>
      Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x) := by
  convert fourier_integrable hg ξ using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  congr 1
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring


lemma fourier_re_even {g : Plane → ℂ} (hg : Integrable g)
    (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => ((g x).re : ℂ)) ξ = ((𝓕 g ξ).re : ℂ) := by
  have hgc : Integrable (fun x => conj (g x)) := by
    exact RCLike.conjCLE.toContinuousLinearMap.integrable_comp hg
  calc
    _ = (𝓕 g ξ + 𝓕 (fun x => conj (g x)) ξ) / 2 := by
      simp only [Real.fourier_eq', smul_eq_mul]
      rw [← integral_add (fourier_integrable_exp hg ξ)
        (fourier_integrable_exp hgc ξ), ← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      rw [complex_re_as_sum]
      ring
    _ = _ := by rw [fourier_conj_even he, ← complex_re_as_sum]

end SharpPlanar

namespace SharpPlanar

lemma gaussianSpectral_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) : Integrable (gaussianSpectral μ f) := by
  have hi := (spectralGaussian_joint_integrable hf (0 : Plane)).integral_prod_left
  unfold gaussianSpectral
  simpa [Real.fourierChar_apply] using hi

lemma gaussianSpectral_even (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f (-x) = gaussianSpectral μ f x := by
  simp [gaussianSpectral, spectralGaussian]

lemma gaussianSpectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f x =
      (Real.exp (-Real.pi*h*(b*‖x‖^2)) : ℂ) * spectral μ f (b*‖x‖^2) := by
  rw [gaussianSpectral, spectral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold spectralGaussian gaussianCoeff
  congr 1
  push_cast
  ring

lemma gaussianSpectral_fourier {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (gaussianSpectral μ f) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t, kernelMoment 0 (b*‖ξ‖^2) t * f t ∂μ := by
  unfold gaussianSpectral
  rw [spectralGaussian_fourier_integral hf]
  simp_rw [spectralGaussian_fourier, mul_assoc]
  rw [integral_const_mul]

lemma gaussianSpectral_dirac_fourier (t : ℝ) (c : ℂ) (ξ : Plane) :
    𝓕 (gaussianSpectral (Measure.dirac t) (fun _ => c)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) * kernelMoment 0 (b*‖ξ‖^2) t * c := by
  rw [gaussianSpectral_fourier (integrable_dirac (by finiteness)), integral_dirac]
  ring

lemma density_piece_integrable (p : CardinalData) {j : ℕ} (hj : j < 6) :
    IntegrableOn (density p j) (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply (continuousOn_density_g p j).mono
  intro t ht
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hj)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor <;> linarith [ht.1, ht.2]

lemma fourier_add_integrable {f g : Plane → ℂ} (hf : Integrable f)
    (hg : Integrable g) (ξ : Plane) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  simp only [Real.fourier_eq', smul_eq_mul, mul_add]
  rw [integral_add (fourier_integrable_exp hf ξ) (fourier_integrable_exp hg ξ)]

lemma fourier_sum_integrable {ι : Type*} (s : Finset ι) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Plane) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  classical
  simp only [Real.fourier_eq', smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => fourier_integrable_exp (hf i hi) ξ)]

lemma qComplex_integrable (p : CardinalData) : Integrable (qComplex p) := by
  apply Integrable.add
  · apply Integrable.add
    · exact gaussianSpectral_integrable (integrable_dirac (by finiteness))
    · exact integrable_finsetSum _ fun j _ =>
        gaussianSpectral_integrable (integrable_dirac (by finiteness))
  · exact integrable_finsetSum _ fun j hj =>
      gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))

lemma qComplex_even (p : CardinalData) (x : Plane) : qComplex p (-x) = qComplex p x := by
  simp only [qComplex, gaussianSpectral_even]

lemma qComplex_re (p : CardinalData) (x : Plane) : (qComplex p x).re = qSchwartz p x := by
  rw [qSchwartz_apply]
  simp only [qComplex, gaussianSpectral_eq, ← Finset.mul_sum, ← mul_add]
  simp only [cardinal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma qComplex_fourier (p : CardinalData) (ξ : Plane) :
    (𝓕 (qComplex p) ξ).re =
      Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) := by
  have h₀ : Integrable (gaussianSpectral (Measure.dirac 0)
      (fun _ => (p.C : ℂ)*Pcoeff 0)) :=
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₁ : ∀ j ∈ Finset.Icc (1 : ℕ) 6,
      Integrable (gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j)) := fun _ _ =>
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₂ : ∀ j ∈ Finset.range 6,
      Integrable (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) := fun j hj =>
    gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))
  unfold qComplex
  have h01 : Integrable (fun x =>
      gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
      ∑ j ∈ Finset.Icc (1 : ℕ) 6, gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) := h₀.add (integrable_finsetSum _ h₁)
  rw [fourier_add_integrable h01
      (integrable_finsetSum _ h₂),
    fourier_add_integrable h₀ (integrable_finsetSum _ h₁),
    fourier_sum_integrable _ _ h₁, fourier_sum_integrable _ _ h₂]
  simp_rw [gaussianSpectral_dirac_fourier]
  have hd : ∀ j ∈ Finset.range 6,
      𝓕 (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
          density p j t * kernelMoment 0 (b*‖ξ‖^2) t := by
    intro j hj
    rw [gaussianSpectral_fourier (density_piece_integrable p (Finset.mem_range.mp hj)),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hd]
  simp only [mul_assoc, ← Finset.mul_sum, ← mul_add]
  have ha : kernelMoment 0 (b*‖ξ‖^2) 0 * ((p.C : ℂ)*Pcoeff 0) +
      (∑ j ∈ Finset.Icc (1 : ℕ) 6,
        kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6) * (2*((p.C : ℂ)*Pcoeff j))) =
      (p.C : ℂ) * (Pcoeff 0 * kernelMoment 0 (b*‖ξ‖^2) 0 +
        ∑ j ∈ Finset.Icc (1 : ℕ) 6,
          2 * Pcoeff j * kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [ha]
  simp only [K, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma qSchwartz_fourier (p : CardinalData) (ξ : Plane) :
    𝓕 (fun x : Plane => (qSchwartz p x : ℂ)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) : ℝ) := by
  simp_rw [← qComplex_re]
  rw [fourier_re_even (qComplex_integrable p) (qComplex_even p), qComplex_fourier]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma kSchwartz_apply (p : CardinalData) (x : Plane) :
    kSchwartz p x=Real.exp (-Real.pi*h*(b*‖x‖^2))*K p 0 (b*‖x‖^2) := by
  change (𝓕 (qComplexSchwartz p) x).re=_
  rw [SchwartzMap.fourier_coe]
  change (𝓕 (fun x : Plane => (qSchwartz p x:ℂ)) x).re=_
  rw [qSchwartz_fourier]
  rfl
lemma pairLeft_apply (p q : CardinalData) (x : Plane) :
    pairLeft p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal p (b*‖x‖^2)+K q 0 (b*‖x‖^2)) := by
  change qSchwartz p x+kSchwartz q x=_
  rw [qSchwartz_apply,kSchwartz_apply,mul_add]
lemma pairRight_apply (p q : CardinalData) (x : Plane) :
    pairRight p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal q (b*‖x‖^2)+K p 0 (b*‖x‖^2)) :=
  pairLeft_apply q p x
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
lemma exactJet_zero_false (s : ℝ) : exactJet false 0 s=H₁ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_zero_true (s : ℝ) : exactJet true 0 s=H₂ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_one_false (s : ℝ) : exactJet false 1 s=deriv H₁ s := (H₁_hasDerivAt s).deriv.symm
lemma exactJet_one_true (s : ℝ) : exactJet true 1 s=deriv H₂ s := (H₂_hasDerivAt s).deriv.symm
lemma exactJet_node_zero (a : Bool) (n : Node) : exactJet a 0 n.val=0 := by
  cases a
  · rw [exactJet_zero_false]; exact (H₁_jets n).1
  · rw [exactJet_zero_true]; exact (H₂_jets n).1
lemma exactJet_node_first (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true) :
    exactJet a 1 n.val=0 := by
  cases a
  · rw [exactJet_one_false,(H₁_jets n).2,ite_eq_right (by simpa using hn)]
  · rw [exactJet_one_true]; exact (H₂_jets n).2
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
lemma exactJet_jets_two (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true) :
    ∀ k<2,exactJet a k n.val=0 := by
  intro k hk
  interval_cases k
  · exact exactJet_node_zero a n
  · exact exactJet_node_first a n hn
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
lemma taylor_cap1 : taylorEnvelope 31 0*(1/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap3 : taylorEnvelope 31 1*(1:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap4 : taylorEnvelope 31 2*(1:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap5 : taylorEnvelope 31 3*(1/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap6 : taylorEnvelope 31 4*(3/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  first | (simp [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap, massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase, atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap7 : taylorEnvelope 31 5*(3/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
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
lemma halfGap_nonneg_Y {a : Bool} {m y v Y E R L : ℝ} {nu : ℕ}
    (hv : v  ∈  Set.Icc 0 1) (hy : |y*v|  ≤  Y) (hpow : (y*v)^nu=|y*v|^nu)
    (hj : ∀ k<nu,exactJet a k m=0)
    (hE : ∀ s  ∈  Set.uIcc m (m+y*v), |exactJet a nu s-tableHJet a nu s| ≤ E)
    (hR : ∀ s  ∈  Set.uIcc m (m+y*v), |tableHJet a (nu+29) s| ≤ R)
    (hB : ∀ k : Fin 29,L  ≤  powerToBernstein 28 (sourcePower a m y nu) k.val)
    (hc : E/(nu.factorial:ℝ)+R*Y^29/((nu+29).factorial:ℝ) ≤ L) :
    0  ≤  (if a then 1 else -1)*exactJet a 0 (m+y*v) := by
  have he := halfGap_lower hv hy hpow hj hE hR hB
  exact (mul_nonneg (by linarith : 0 ≤ L-E/(nu.factorial:ℝ)-R*Y^29/((nu+29).factorial:ℝ))
    (pow_nonneg (abs_nonneg _) _)).trans he
lemma segment_bound {m y v s Y : ℝ} (hv : v  ∈  Set.Icc 0 1) (hy : |y|  ≤  Y)
    (hs : s  ∈  Set.uIcc m (m+y*v)) : m-Y  ≤  s := by
  apply halfGap_segment_lower hv (by linarith [(abs_nonneg y).trans hy]) _ hs
  have hyy: -Y ≤ y := (abs_le.mp hy).1
  linarith
lemma analytic_large (a : Bool) (n : Node) (hn : 7 ≤ n.val) {y v : ℝ}
    (hy : |y| ≤ 3/2) (hv : v  ∈  Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(9:ℝ)/1000  ≤  powerToBernstein 28 (sourcePower a n.val y 2) k.val) :
    0  ≤  (if a then 1 else -1)*exactJet a 0 (n.val+y*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v)) : 5 ≤ s := by
    have h:=segment_bound hv hy hss
    have hn' : (7:ℝ) ≤ n.val := by exact_mod_cast hn
    linarith
  apply halfGap_nonneg_Y (E := 4/1000) (R := taylorEnvelope 31 5) (Y := 3/2) hv
    ((halfGap_absmul hv).trans hy) (by rw [sq_abs])
    (exactJet_jets_two a n (Or.inl (by omega)))
  · intro s hss
    have h:=error_large_cap_g a (by linarith [hs s hss] : (2:ℝ) ≤ s)
    linarith
  · intro s hss
    exact table_jet_rat a 31 5 (hs s hss)
  · exact hB
  · have hh:=taylor_cap7
    norm_num [Nat.factorial] at hh ⊢
    linarith
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfGapSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma analytic_two_cap (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true)
    {N : ℕ} {y v Y E R L : ℝ}
    (hv : v ∈ Set.Icc 0 1) (hy : |y| ≤ Y)
    (hseg : ∀ s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v), (N:ℝ) ≤ s)
    (herr : ∀ s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v),
      |exactJet a 2 s-tableHJet a 2 s|/2 < E)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a n.val y 2) k.val)
    (hcap : taylorEnvelope 31 N*Y^29/((31:ℕ).factorial:ℝ) < R)
    (hr : E+R ≤ L) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (n.val+y*v) := by
  apply halfGap_nonneg_Y (E := 2*E) (R := taylorEnvelope 31 N) (Y := Y) hv
    ((halfGap_absmul hv).trans hy) (by rw [sq_abs]) (exactJet_jets_two a n hn)
  · intro s hs
    have hh := herr s hs
    linarith
  · intro s hs
    exact table_jet_rat a 31 N (hseg s hs)
  · exact hB
  · norm_num [Nat.factorial] at hcap ⊢
    linarith
lemma analytic_first_left {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(18:ℝ)/100 ≤ powerToBernstein 28 (sourcePower true 1 (-1/2) 2) k.val) :
    0 ≤ exactJet true 0 (1+(-1/2)*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 1 (1+(-1/2)*v)) : (1:ℝ)/2 ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap true firstNode (Or.inr rfl) (N := 0) (y := -1/2)
    (Y := (1:ℝ)/2) (E := 11/1000) (R := 1/1000) (L := 18/100) hv (by norm_num)
    (fun s hss => by have h := hs s (by simpa only [firstNode,Nat.cast_one] using hss); norm_num <;> linarith)
    (fun s hss => error_two_cap_g true (hs s (by simpa only [firstNode,Nat.cast_one] using hss))) (by simpa only [firstNode,Nat.cast_one] using hB) taylor_cap1 (by norm_num)
  simpa [firstNode] using hh
lemma analytic_first_right_true {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(18:ℝ)/100 ≤ powerToBernstein 28 (sourcePower true 1 1 2) k.val) :
    0 ≤ exactJet true 0 (1+1*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 1 (1+1*v)) : (1:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap true firstNode (Or.inr rfl) (N := 1) (y := 1)
    (Y := (1:ℝ)) (E := 11/1000) (R := 1/1000) (L := 18/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [firstNode,Nat.cast_one] using hss))
    (fun s hss => error_two_cap_g true (by have h := hs s (by simpa only [firstNode,Nat.cast_one] using hss); linarith)) (by simpa only [firstNode,Nat.cast_one] using hB) taylor_cap3 (by norm_num)
  simpa [firstNode] using hh
lemma analytic_3_left (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 3 (-1) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (3+(-1)*v) := by
  let n : Node := ⟨3,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 3 (3+(-1)*v)) : (2:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 2) (y := -1)
    (Y := (1:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap_g a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap4 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_3_right (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 3 (1/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (3+(1/2)*v) := by
  let n : Node := ⟨3,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 3 (3+(1/2)*v)) : (3:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 3) (y := 1/2)
    (Y := (1/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap_g a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap5 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_4_left (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 4 (-1/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (4+(-1/2)*v) := by
  let n : Node := ⟨4,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 4 (4+(-1/2)*v)) : (3:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 3) (y := -1/2)
    (Y := (1/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap_g a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap5 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_4_right (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 4 (3/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (4+(3/2)*v) := by
  let n : Node := ⟨4,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 4 (4+(3/2)*v)) : (4:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 4) (y := 3/2)
    (Y := (3/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap_g a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap6 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_1_N1_right {s : ℝ} (hs : s ∈ Set.Icc 1 2) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-1)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (1:ℝ)+1*v=s := by dsimp [v] <;> ring
  have hh:=analytic_first_right_true hv (fun k => by have hh := (Bernstein1.N1_right.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (1:ℝ)+1*v=s := by simpa using he
  rw [he'] at hh
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,neg_one_mul,one_mul] using hh
lemma halfSign_1_N1_left {s : ℝ} (hs : s ∈ Set.Icc (1/2) 1) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(1-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (1:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  have hh:=analytic_first_left hv (fun k => by have hh := (Bernstein1.N1_left.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (1:ℝ) + (-1/2)*v=s := by simpa using he
  rw [he'] at hh
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,neg_one_mul,one_mul] using hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_12_N1_right {s : ℝ} (hs : s ∈ Set.Icc 12 (25/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-12)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (12:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨12,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat] using (Bernstein12.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_12_N1_left {s : ℝ} (hs : s ∈ Set.Icc (21/2) 12) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(12-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (12:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨12,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat] using (Bernstein12.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_13_N1_right {s : ℝ} (hs : s ∈ Set.Icc 13 14) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-13)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_13_N1_left {s : ℝ} (hs : s ∈ Set.Icc (25/2) 13) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(13-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (13:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨13,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein13.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_15_N1_right {s : ℝ} (hs : s ∈ Set.Icc 15 (31/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-15)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (15:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨15,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein15.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_15_N1_left {s : ℝ} (hs : s ∈ Set.Icc 14 15) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(15-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (15:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨15,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein15.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_16_N1_right {s : ℝ} (hs : s ∈ Set.Icc 16 (35/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-16)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (16:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨16,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein16.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_16_N1_left {s : ℝ} (hs : s ∈ Set.Icc (31/2) 16) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(16-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (16:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨16,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein16.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_19_N1_right {s : ℝ} (hs : s ∈ Set.Icc 19 20) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-19)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (19:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨19,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein19.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_19_N1_left {s : ℝ} (hs : s ∈ Set.Icc (35/2) 19) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(19-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (19:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨19,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein19.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_21_N1_right {s : ℝ} (hs : s ∈ Set.Icc 21 (45/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-21)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (21:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨21,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein21.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_21_N1_left {s : ℝ} (hs : s ∈ Set.Icc 20 21) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(21-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (21:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨21,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein21.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_24_N1_right {s : ℝ} (hs : s ∈ Set.Icc 24 (49/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-24)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (24:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨24,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein24.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_24_N1_left {s : ℝ} (hs : s ∈ Set.Icc (45/2) 24) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(24-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (24:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨24,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein24.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_25_N1_right {s : ℝ} (hs : s ∈ Set.Icc 25 26) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-25)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (25:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨25,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein25.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_25_N1_left {s : ℝ} (hs : s ∈ Set.Icc (49/2) 25) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(25-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (25:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨25,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein25.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_27_N1_right {s : ℝ} (hs : s ∈ Set.Icc 27 (55/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-27)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (27:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨27,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein27.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_27_N1_left {s : ℝ} (hs : s ∈ Set.Icc 26 27) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(27-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (27:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨27,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein27.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_28_N1_right {s : ℝ} (hs : s ∈ Set.Icc 28 (59/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-28)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_28_N1_left {s : ℝ} (hs : s ∈ Set.Icc (55/2) 28) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(28-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (28:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨28,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein28.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_3_N1_right {s : ℝ} (hs : s ∈ Set.Icc 3 (7/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-3)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  have hh:=analytic_3_right true hv (fun k => by have hh := (Bernstein3.N1_right.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+(1/2)*v=s := he
  rw [he'] at hh
  exact hh
lemma halfSign_3_N1_left {s : ℝ} (hs : s ∈ Set.Icc 2 3) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(3-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (3:ℝ)+-1*v=s := by dsimp [v] <;> ring
  have hh:=analytic_3_left true hv (fun k => by have hh := (Bernstein3.N1_left.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (3:ℝ)+-1*v=s := he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_31_N1_right {s : ℝ} (hs : s ∈ Set.Icc 31 32) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-31)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (31:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨31,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein31.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_31_N1_left {s : ℝ} (hs : s ∈ Set.Icc (59/2) 31) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(31-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (31:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨31,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein31.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_33_N1_right {s : ℝ} (hs : s ∈ Set.Icc 33 (69/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-33)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (33:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨33,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein33.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_33_N1_left {s : ℝ} (hs : s ∈ Set.Icc 32 33) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(33-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (33:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨33,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein33.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_36_N1_right {s : ℝ} (hs : s ∈ Set.Icc 36 (73/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-36)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (36:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨36,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein36.N1_right.bound k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_36_N1_left {s : ℝ} (hs : s ∈ Set.Icc (69/2) 36) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(36-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (36:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨36,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein36.N1_left.bound k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_37_N1_right {s : ℝ} (hs : s ∈ Set.Icc 37 38) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-37)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (37:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨37,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein37.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_37_N1_left {s : ℝ} (hs : s ∈ Set.Icc (73/2) 37) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(37-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (37:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨37,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein37.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_39_N1_right {s : ℝ} (hs : s ∈ Set.Icc 39 (79/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-39)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (39:ℝ)+(1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨39,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein39.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_39_N1_left {s : ℝ} (hs : s ∈ Set.Icc 38 39) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(39-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (39:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨39,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein39.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_4_N1_right {s : ℝ} (hs : s ∈ Set.Icc 4 (11/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-4)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (4:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  have hh:=analytic_4_right true hv (fun k => by have hh := (Bernstein4.N1_right.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (4:ℝ)+(3/2)*v=s := he
  rw [he'] at hh
  exact hh
lemma halfSign_4_N1_left {s : ℝ} (hs : s ∈ Set.Icc (7/2) 4) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(4-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (4:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  have hh:=analytic_4_left true hv (fun k => by have hh := (Bernstein4.N1_left.bound_g k).le; norm_num at hh ⊢; exact hh)
  have he' : (4:ℝ)+(-1/2)*v=s := he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_40_N1_right {s : ℝ} (hs : s ∈ Set.Icc 40 (83/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-40)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (40:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨40,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein40.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_40_N1_left {s : ℝ} (hs : s ∈ Set.Icc (79/2) 40) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(40-s)/(1/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (1/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (1/2))).mpr
      linarith [hs.1,hs.2]
  have he : (40:ℝ)+(-1/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨40,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-1/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein40.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-1/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_7_N1_right {s : ℝ} (hs : s ∈ Set.Icc 7 8) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-7)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (7:ℝ)+1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨7,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := 1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein7.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_7_N1_left {s : ℝ} (hs : s ∈ Set.Icc (11/2) 7) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(7-s)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (7:ℝ)+(-3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨7,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (-3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein7.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+(-3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfSign9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma halfSign_9_N1_right {s : ℝ} (hs : s ∈ Set.Icc 9 (21/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(s-9)/(3/2)
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ (3/2))
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < (3/2))).mpr
      linarith [hs.1,hs.2]
  have he : (9:ℝ)+(3/2)*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨9,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := (3/2)) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein9.N1_right.bound_g k).le)
  have he' : (n.val:ℝ)+(3/2)*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
lemma halfSign_9_N1_left {s : ℝ} (hs : s ∈ Set.Icc 8 9) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  let v : ℝ:=(9-s)/1
  have hv : v ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (by linarith [hs.1,hs.2]) (by norm_num : (0:ℝ) ≤ 1)
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 1)).mpr
      linarith [hs.1,hs.2]
  have he : (9:ℝ)+-1*v=s := by dsimp [v] <;> ring
  let n : Node:=⟨9,by decide +kernel⟩
  have hh:=analytic_large true n (by decide +kernel) (y := -1) (by norm_num) hv
    (fun k => by simpa only [n,Nat.cast_ofNat,div_one] using (Bernstein9.N1_left.bound_g k).le)
  have he' : (n.val:ℝ)+-1*v=s := by simpa only [n,Nat.cast_ofNat] using he
  rw [he'] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_GlobalSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma finite_sign_true {s : ℝ} (hs : s ∈ Set.Icc 0 (83/2)) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  by_cases h0 : s ≤ (1/2)
  · exact halfSign_0_N1_right_g ⟨hs.1,h0⟩
  by_cases h1 : s ≤ 1
  · exact halfSign_1_N1_left ⟨le_of_lt (lt_of_not_ge h0),h1⟩
  by_cases h2 : s ≤ 2
  · exact halfSign_1_N1_right ⟨le_of_lt (lt_of_not_ge h1),h2⟩
  by_cases h3 : s ≤ 3
  · exact halfSign_3_N1_left ⟨le_of_lt (lt_of_not_ge h2),h3⟩
  by_cases h4 : s ≤ (7/2)
  · exact halfSign_3_N1_right ⟨le_of_lt (lt_of_not_ge h3),h4⟩
  by_cases h5 : s ≤ 4
  · exact halfSign_4_N1_left ⟨le_of_lt (lt_of_not_ge h4),h5⟩
  by_cases h6 : s ≤ (11/2)
  · exact halfSign_4_N1_right ⟨le_of_lt (lt_of_not_ge h5),h6⟩
  by_cases h7 : s ≤ 7
  · exact halfSign_7_N1_left ⟨le_of_lt (lt_of_not_ge h6),h7⟩
  by_cases h8 : s ≤ 8
  · exact halfSign_7_N1_right ⟨le_of_lt (lt_of_not_ge h7),h8⟩
  by_cases h9 : s ≤ 9
  · exact halfSign_9_N1_left ⟨le_of_lt (lt_of_not_ge h8),h9⟩
  by_cases h10 : s ≤ (21/2)
  · exact halfSign_9_N1_right ⟨le_of_lt (lt_of_not_ge h9),h10⟩
  by_cases h11 : s ≤ 12
  · exact halfSign_12_N1_left ⟨le_of_lt (lt_of_not_ge h10),h11⟩
  by_cases h12 : s ≤ (25/2)
  · exact halfSign_12_N1_right ⟨le_of_lt (lt_of_not_ge h11),h12⟩
  by_cases h13 : s ≤ 13
  · exact halfSign_13_N1_left ⟨le_of_lt (lt_of_not_ge h12),h13⟩
  by_cases h14 : s ≤ 14
  · exact halfSign_13_N1_right ⟨le_of_lt (lt_of_not_ge h13),h14⟩
  by_cases h15 : s ≤ 15
  · exact halfSign_15_N1_left ⟨le_of_lt (lt_of_not_ge h14),h15⟩
  by_cases h16 : s ≤ (31/2)
  · exact halfSign_15_N1_right ⟨le_of_lt (lt_of_not_ge h15),h16⟩
  by_cases h17 : s ≤ 16
  · exact halfSign_16_N1_left ⟨le_of_lt (lt_of_not_ge h16),h17⟩
  by_cases h18 : s ≤ (35/2)
  · exact halfSign_16_N1_right ⟨le_of_lt (lt_of_not_ge h17),h18⟩
  by_cases h19 : s ≤ 19
  · exact halfSign_19_N1_left ⟨le_of_lt (lt_of_not_ge h18),h19⟩
  by_cases h20 : s ≤ 20
  · exact halfSign_19_N1_right ⟨le_of_lt (lt_of_not_ge h19),h20⟩
  by_cases h21 : s ≤ 21
  · exact halfSign_21_N1_left ⟨le_of_lt (lt_of_not_ge h20),h21⟩
  by_cases h22 : s ≤ (45/2)
  · exact halfSign_21_N1_right ⟨le_of_lt (lt_of_not_ge h21),h22⟩
  by_cases h23 : s ≤ 24
  · exact halfSign_24_N1_left ⟨le_of_lt (lt_of_not_ge h22),h23⟩
  by_cases h24 : s ≤ (49/2)
  · exact halfSign_24_N1_right ⟨le_of_lt (lt_of_not_ge h23),h24⟩
  by_cases h25 : s ≤ 25
  · exact halfSign_25_N1_left ⟨le_of_lt (lt_of_not_ge h24),h25⟩
  by_cases h26 : s ≤ 26
  · exact halfSign_25_N1_right ⟨le_of_lt (lt_of_not_ge h25),h26⟩
  by_cases h27 : s ≤ 27
  · exact halfSign_27_N1_left ⟨le_of_lt (lt_of_not_ge h26),h27⟩
  by_cases h28 : s ≤ (55/2)
  · exact halfSign_27_N1_right ⟨le_of_lt (lt_of_not_ge h27),h28⟩
  by_cases h29 : s ≤ 28
  · exact halfSign_28_N1_left ⟨le_of_lt (lt_of_not_ge h28),h29⟩
  by_cases h30 : s ≤ (59/2)
  · exact halfSign_28_N1_right ⟨le_of_lt (lt_of_not_ge h29),h30⟩
  by_cases h31 : s ≤ 31
  · exact halfSign_31_N1_left ⟨le_of_lt (lt_of_not_ge h30),h31⟩
  by_cases h32 : s ≤ 32
  · exact halfSign_31_N1_right ⟨le_of_lt (lt_of_not_ge h31),h32⟩
  by_cases h33 : s ≤ 33
  · exact halfSign_33_N1_left ⟨le_of_lt (lt_of_not_ge h32),h33⟩
  by_cases h34 : s ≤ (69/2)
  · exact halfSign_33_N1_right ⟨le_of_lt (lt_of_not_ge h33),h34⟩
  by_cases h35 : s ≤ 36
  · exact halfSign_36_N1_left ⟨le_of_lt (lt_of_not_ge h34),h35⟩
  by_cases h36 : s ≤ (73/2)
  · exact halfSign_36_N1_right ⟨le_of_lt (lt_of_not_ge h35),h36⟩
  by_cases h37 : s ≤ 37
  · exact halfSign_37_N1_left ⟨le_of_lt (lt_of_not_ge h36),h37⟩
  by_cases h38 : s ≤ 38
  · exact halfSign_37_N1_right ⟨le_of_lt (lt_of_not_ge h37),h38⟩
  by_cases h39 : s ≤ 39
  · exact halfSign_39_N1_left ⟨le_of_lt (lt_of_not_ge h38),h39⟩
  by_cases h40 : s ≤ (79/2)
  · exact halfSign_39_N1_right ⟨le_of_lt (lt_of_not_ge h39),h40⟩
  by_cases h41 : s ≤ 40
  · exact halfSign_40_N1_left ⟨le_of_lt (lt_of_not_ge h40),h41⟩
  exact halfSign_40_N1_right ⟨le_of_lt (lt_of_not_ge h41),hs.2⟩
lemma global_sign_true {s : ℝ} (hs : (0:ℝ) ≤ s) :
    0 ≤ (if true then (1:ℝ) else -1)*exactJet true 0 s := by
  by_cases hh : s ≤ 83/2
  · exact finite_sign_true ⟨hs,hh⟩
  · exact exact_sign_tail_g true (le_of_lt (lt_of_not_ge hh))
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_OriginIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality at the origin from triangular lattice contacts and Poisson summation -/

namespace SharpPlanar
lemma exactRight_apply (x : Plane) : exactRight x=Real.exp (-Real.pi*h*(b*‖x‖^2))*H₂ (b*‖x‖^2) :=
  pairRight_apply _ _ _
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_OriginPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity at the origin of the exact Fourier pair -/

namespace SharpPlanar
open IntegerIntervals CachedData
lemma exactJet_zero_H₂ (s : ℝ) : exactJet true 0 s=H₂ s := by
  simp only [exactJet,exactData,ite_true, if_true,Bool.not_true,Bool.false_eq_true,ite_false, if_false,← cardinal_eq_cardinalSeries,H₂]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma normalizedCandidate_fourier_nonneg_g_oai (ξ : Plane) : 0≤(fourier normalizedCandidate ξ).re := by
  rw [normalizedCandidate_fourier_g]
  change 0≤exactRight (scaleFactor⁻¹ • ξ)/exactLeft 0
  apply div_nonneg _ exactLeft_origin_positive_g.le
  rw [exactRight_apply]
  apply mul_nonneg (Real.exp_pos _).le
  have hh:=global_sign_true (mul_nonneg b_pos_g.le (sq_nonneg ‖scaleFactor⁻¹ • ξ‖))
  rw [exactJet_zero_H₂] at hh
  simpa only [ite_true, if_true,one_mul] using hh
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g_oai := @OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g_oai
